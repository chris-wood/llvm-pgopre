//===-- Type.cpp - Implement the Type class -------------------------------===//
// 
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
// 
//===----------------------------------------------------------------------===//
//
// This file implements the Type class for the VMCore library.
//
//===----------------------------------------------------------------------===//

#include "llvm/AbstractTypeUser.h"
#include "llvm/DerivedTypes.h"
#include "llvm/SymbolTable.h"
#include "llvm/Constants.h"
#include "Support/DepthFirstIterator.h"
#include "Support/StringExtras.h"
#include "Support/STLExtras.h"
#include <algorithm>
#include <iostream>
using namespace llvm;

// DEBUG_MERGE_TYPES - Enable this #define to see how and when derived types are
// created and later destroyed, all in an effort to make sure that there is only
// a single canonical version of a type.
//
//#define DEBUG_MERGE_TYPES 1

AbstractTypeUser::~AbstractTypeUser() {}

//===----------------------------------------------------------------------===//
//                         Type Class Implementation
//===----------------------------------------------------------------------===//

// Concrete/Abstract TypeDescriptions - We lazily calculate type descriptions
// for types as they are needed.  Because resolution of types must invalidate
// all of the abstract type descriptions, we keep them in a seperate map to make
// this easy.
static std::map<const Type*, std::string> ConcreteTypeDescriptions;
static std::map<const Type*, std::string> AbstractTypeDescriptions;

Type::Type( const std::string& name, TypeID id )
  : RefCount(0), ForwardType(0) {
  if (!name.empty())
    ConcreteTypeDescriptions[this] = name;
  ID = id;
  Abstract = false;
}

const Type *Type::getPrimitiveType(TypeID IDNumber) {
  switch (IDNumber) {
  case VoidTyID  : return VoidTy;
  case BoolTyID  : return BoolTy;
  case UByteTyID : return UByteTy;
  case SByteTyID : return SByteTy;
  case UShortTyID: return UShortTy;
  case ShortTyID : return ShortTy;
  case UIntTyID  : return UIntTy;
  case IntTyID   : return IntTy;
  case ULongTyID : return ULongTy;
  case LongTyID  : return LongTy;
  case FloatTyID : return FloatTy;
  case DoubleTyID: return DoubleTy;
  case LabelTyID : return LabelTy;
  default:
    return 0;
  }
}

// isLosslesslyConvertibleTo - Return true if this type can be converted to
// 'Ty' without any reinterpretation of bits.  For example, uint to int.
//
bool Type::isLosslesslyConvertibleTo(const Type *Ty) const {
  if (this == Ty) return true;
  if ((!isPrimitiveType()    && !isa<PointerType>(this)) ||
      (!isa<PointerType>(Ty) && !Ty->isPrimitiveType())) return false;

  if (getTypeID() == Ty->getTypeID())
    return true;  // Handles identity cast, and cast of differing pointer types

  // Now we know that they are two differing primitive or pointer types
  switch (getTypeID()) {
  case Type::UByteTyID:   return Ty == Type::SByteTy;
  case Type::SByteTyID:   return Ty == Type::UByteTy;
  case Type::UShortTyID:  return Ty == Type::ShortTy;
  case Type::ShortTyID:   return Ty == Type::UShortTy;
  case Type::UIntTyID:    return Ty == Type::IntTy;
  case Type::IntTyID:     return Ty == Type::UIntTy;
  case Type::ULongTyID:   return Ty == Type::LongTy;
  case Type::LongTyID:    return Ty == Type::ULongTy;
  case Type::PointerTyID: return isa<PointerType>(Ty);
  default:
    return false;  // Other types have no identity values
  }
}

/// getUnsignedVersion - If this is an integer type, return the unsigned
/// variant of this type.  For example int -> uint.
const Type *Type::getUnsignedVersion() const {
  switch (getTypeID()) {
  default:
    assert(isInteger()&&"Type::getUnsignedVersion is only valid for integers!");
  case Type::UByteTyID:   
  case Type::SByteTyID:   return Type::UByteTy;
  case Type::UShortTyID:  
  case Type::ShortTyID:   return Type::UShortTy;
  case Type::UIntTyID:    
  case Type::IntTyID:     return Type::UIntTy;
  case Type::ULongTyID:   
  case Type::LongTyID:    return Type::ULongTy;
  }
}

/// getSignedVersion - If this is an integer type, return the signed variant
/// of this type.  For example uint -> int.
const Type *Type::getSignedVersion() const {
  switch (getTypeID()) {
  default:
    assert(isInteger() && "Type::getSignedVersion is only valid for integers!");
  case Type::UByteTyID:   
  case Type::SByteTyID:   return Type::SByteTy;
  case Type::UShortTyID:  
  case Type::ShortTyID:   return Type::ShortTy;
  case Type::UIntTyID:    
  case Type::IntTyID:     return Type::IntTy;
  case Type::ULongTyID:   
  case Type::LongTyID:    return Type::LongTy;
  }
}


// getPrimitiveSize - Return the basic size of this type if it is a primitive
// type.  These are fixed by LLVM and are not target dependent.  This will
// return zero if the type does not have a size or is not a primitive type.
//
unsigned Type::getPrimitiveSize() const {
  switch (getTypeID()) {
#define HANDLE_PRIM_TYPE(TY,SIZE)  case TY##TyID: return SIZE;
#include "llvm/Type.def"
  default: return 0;
  }
}

/// isSizedDerivedType - Derived types like structures and arrays are sized
/// iff all of the members of the type are sized as well.  Since asking for
/// their size is relatively uncommon, move this operation out of line.
bool Type::isSizedDerivedType() const {
  if (const ArrayType *ATy = dyn_cast<ArrayType>(this))
    return ATy->getElementType()->isSized();

  if (!isa<StructType>(this)) return false;

  // Okay, our struct is sized if all of the elements are...
  for (subtype_iterator I = subtype_begin(), E = subtype_end(); I != E; ++I)
    if (!(*I)->isSized()) return false;

  return true;
}

/// getForwardedTypeInternal - This method is used to implement the union-find
/// algorithm for when a type is being forwarded to another type.
const Type *Type::getForwardedTypeInternal() const {
  assert(ForwardType && "This type is not being forwarded to another type!");
  
  // Check to see if the forwarded type has been forwarded on.  If so, collapse
  // the forwarding links.
  const Type *RealForwardedType = ForwardType->getForwardedType();
  if (!RealForwardedType)
    return ForwardType;  // No it's not forwarded again

  // Yes, it is forwarded again.  First thing, add the reference to the new
  // forward type.
  if (RealForwardedType->isAbstract())
    cast<DerivedType>(RealForwardedType)->addRef();

  // Now drop the old reference.  This could cause ForwardType to get deleted.
  cast<DerivedType>(ForwardType)->dropRef();
  
  // Return the updated type.
  ForwardType = RealForwardedType;
  return ForwardType;
}

// getTypeDescription - This is a recursive function that walks a type hierarchy
// calculating the description for a type.
//
static std::string getTypeDescription(const Type *Ty,
                                      std::vector<const Type *> &TypeStack) {
  if (isa<OpaqueType>(Ty)) {                     // Base case for the recursion
    std::map<const Type*, std::string>::iterator I =
      AbstractTypeDescriptions.lower_bound(Ty);
    if (I != AbstractTypeDescriptions.end() && I->first == Ty)
      return I->second;
    std::string Desc = "opaque";
    AbstractTypeDescriptions.insert(std::make_pair(Ty, Desc));
    return Desc;
  }
  
  if (!Ty->isAbstract()) {                       // Base case for the recursion
    std::map<const Type*, std::string>::iterator I =
      ConcreteTypeDescriptions.find(Ty);
    if (I != ConcreteTypeDescriptions.end()) return I->second;
  }
      
  // Check to see if the Type is already on the stack...
  unsigned Slot = 0, CurSize = TypeStack.size();
  while (Slot < CurSize && TypeStack[Slot] != Ty) ++Slot; // Scan for type
  
  // This is another base case for the recursion.  In this case, we know 
  // that we have looped back to a type that we have previously visited.
  // Generate the appropriate upreference to handle this.
  // 
  if (Slot < CurSize)
    return "\\" + utostr(CurSize-Slot);         // Here's the upreference

  // Recursive case: derived types...
  std::string Result;
  TypeStack.push_back(Ty);    // Add us to the stack..
      
  switch (Ty->getTypeID()) {
  case Type::FunctionTyID: {
    const FunctionType *FTy = cast<FunctionType>(Ty);
    Result = getTypeDescription(FTy->getReturnType(), TypeStack) + " (";
    for (FunctionType::param_iterator I = FTy->param_begin(),
           E = FTy->param_end(); I != E; ++I) {
      if (I != FTy->param_begin())
        Result += ", ";
      Result += getTypeDescription(*I, TypeStack);
    }
    if (FTy->isVarArg()) {
      if (FTy->getNumParams()) Result += ", ";
      Result += "...";
    }
    Result += ")";
    break;
  }
  case Type::StructTyID: {
    const StructType *STy = cast<StructType>(Ty);
    Result = "{ ";
    for (StructType::element_iterator I = STy->element_begin(),
           E = STy->element_end(); I != E; ++I) {
      if (I != STy->element_begin())
        Result += ", ";
      Result += getTypeDescription(*I, TypeStack);
    }
    Result += " }";
    break;
  }
  case Type::PointerTyID: {
    const PointerType *PTy = cast<PointerType>(Ty);
    Result = getTypeDescription(PTy->getElementType(), TypeStack) + " *";
    break;
  }
  case Type::ArrayTyID: {
    const ArrayType *ATy = cast<ArrayType>(Ty);
    unsigned NumElements = ATy->getNumElements();
    Result = "[";
    Result += utostr(NumElements) + " x ";
    Result += getTypeDescription(ATy->getElementType(), TypeStack) + "]";
    break;
  }
  default:
    Result = "<error>";
    assert(0 && "Unhandled type in getTypeDescription!");
  }

  TypeStack.pop_back();       // Remove self from stack...

  return Result;
}



static const std::string &getOrCreateDesc(std::map<const Type*,std::string>&Map,
                                          const Type *Ty) {
  std::map<const Type*, std::string>::iterator I = Map.find(Ty);
  if (I != Map.end()) return I->second;
    
  std::vector<const Type *> TypeStack;
  return Map[Ty] = getTypeDescription(Ty, TypeStack);
}


const std::string &Type::getDescription() const {
  if (isAbstract())
    return getOrCreateDesc(AbstractTypeDescriptions, this);
  else
    return getOrCreateDesc(ConcreteTypeDescriptions, this);
}


bool StructType::indexValid(const Value *V) const {
  // Structure indexes require unsigned integer constants.
  if (V->getType() == Type::UIntTy)
    if (const ConstantUInt *CU = dyn_cast<ConstantUInt>(V))
      return CU->getValue() < ContainedTys.size();
  return false;
}

// getTypeAtIndex - Given an index value into the type, return the type of the
// element.  For a structure type, this must be a constant value...
//
const Type *StructType::getTypeAtIndex(const Value *V) const {
  assert(indexValid(V) && "Invalid structure index!");
  unsigned Idx = (unsigned)cast<ConstantUInt>(V)->getValue();
  return ContainedTys[Idx];
}


//===----------------------------------------------------------------------===//
//                           Static 'Type' data
//===----------------------------------------------------------------------===//

namespace {
  struct PrimType : public Type {
    PrimType(const char *S, TypeID ID) : Type(S, ID) {}
  };
}

static PrimType TheVoidTy  ("void"  , Type::VoidTyID);
static PrimType TheBoolTy  ("bool"  , Type::BoolTyID);
static PrimType TheSByteTy ("sbyte" , Type::SByteTyID);
static PrimType TheUByteTy ("ubyte" , Type::UByteTyID);
static PrimType TheShortTy ("short" , Type::ShortTyID);
static PrimType TheUShortTy("ushort", Type::UShortTyID);
static PrimType TheIntTy   ("int"   , Type::IntTyID);
static PrimType TheUIntTy  ("uint"  , Type::UIntTyID);
static PrimType TheLongTy  ("long"  , Type::LongTyID);
static PrimType TheULongTy ("ulong" , Type::ULongTyID);
static PrimType TheFloatTy ("float" , Type::FloatTyID);
static PrimType TheDoubleTy("double", Type::DoubleTyID);
static PrimType TheLabelTy ("label" , Type::LabelTyID);

Type *Type::VoidTy   = &TheVoidTy;
Type *Type::BoolTy   = &TheBoolTy;
Type *Type::SByteTy  = &TheSByteTy;
Type *Type::UByteTy  = &TheUByteTy;
Type *Type::ShortTy  = &TheShortTy;
Type *Type::UShortTy = &TheUShortTy;
Type *Type::IntTy    = &TheIntTy;
Type *Type::UIntTy   = &TheUIntTy;
Type *Type::LongTy   = &TheLongTy;
Type *Type::ULongTy  = &TheULongTy;
Type *Type::FloatTy  = &TheFloatTy;
Type *Type::DoubleTy = &TheDoubleTy;
Type *Type::LabelTy  = &TheLabelTy;


//===----------------------------------------------------------------------===//
//                          Derived Type Constructors
//===----------------------------------------------------------------------===//

FunctionType::FunctionType(const Type *Result,
                           const std::vector<const Type*> &Params, 
                           bool IsVarArgs) : DerivedType(FunctionTyID), 
                                             isVarArgs(IsVarArgs) {
  assert((Result->isFirstClassType() || Result == Type::VoidTy ||
         isa<OpaqueType>(Result)) && 
         "LLVM functions cannot return aggregates");
  bool isAbstract = Result->isAbstract();
  ContainedTys.reserve(Params.size()+1);
  ContainedTys.push_back(PATypeHandle(Result, this));

  for (unsigned i = 0; i != Params.size(); ++i) {
    assert((Params[i]->isFirstClassType() || isa<OpaqueType>(Params[i])) &&
           "Function arguments must be value types!");

    ContainedTys.push_back(PATypeHandle(Params[i], this));
    isAbstract |= Params[i]->isAbstract();
  }

  // Calculate whether or not this type is abstract
  setAbstract(isAbstract);
}

StructType::StructType(const std::vector<const Type*> &Types)
  : CompositeType(StructTyID) {
  ContainedTys.reserve(Types.size());
  bool isAbstract = false;
  for (unsigned i = 0; i < Types.size(); ++i) {
    assert(Types[i] != Type::VoidTy && "Void type for structure field!!");
    ContainedTys.push_back(PATypeHandle(Types[i], this));
    isAbstract |= Types[i]->isAbstract();
  }

  // Calculate whether or not this type is abstract
  setAbstract(isAbstract);
}

ArrayType::ArrayType(const Type *ElType, unsigned NumEl)
  : SequentialType(ArrayTyID, ElType) {
  NumElements = NumEl;

  // Calculate whether or not this type is abstract
  setAbstract(ElType->isAbstract());
}

PointerType::PointerType(const Type *E) : SequentialType(PointerTyID, E) {
  // Calculate whether or not this type is abstract
  setAbstract(E->isAbstract());
}

OpaqueType::OpaqueType() : DerivedType(OpaqueTyID) {
  setAbstract(true);
#ifdef DEBUG_MERGE_TYPES
  std::cerr << "Derived new type: " << *this << "\n";
#endif
}

// dropAllTypeUses - When this (abstract) type is resolved to be equal to
// another (more concrete) type, we must eliminate all references to other
// types, to avoid some circular reference problems.
void DerivedType::dropAllTypeUses() {
  if (!ContainedTys.empty()) {
    while (ContainedTys.size() > 1)
      ContainedTys.pop_back();
    
    // The type must stay abstract.  To do this, we insert a pointer to a type
    // that will never get resolved, thus will always be abstract.
    static Type *AlwaysOpaqueTy = OpaqueType::get();
    static PATypeHolder Holder(AlwaysOpaqueTy);
    ContainedTys[0] = AlwaysOpaqueTy;
  }
}

// isTypeAbstract - This is a recursive function that walks a type hierarchy
// calculating whether or not a type is abstract.  Worst case it will have to do
// a lot of traversing if you have some whacko opaque types, but in most cases,
// it will do some simple stuff when it hits non-abstract types that aren't
// recursive.
//
bool Type::isTypeAbstract() {
  if (!isAbstract())                           // Base case for the recursion
    return false;                              // Primitive = leaf type
  
  if (isa<OpaqueType>(this))                   // Base case for the recursion
    return true;                               // This whole type is abstract!

  // We have to guard against recursion.  To do this, we temporarily mark this
  // type as concrete, so that if we get back to here recursively we will think
  // it's not abstract, and thus not scan it again.
  setAbstract(false);

  // Scan all of the sub-types.  If any of them are abstract, than so is this
  // one!
  for (Type::subtype_iterator I = subtype_begin(), E = subtype_end(); 
       I != E; ++I)
    if (const_cast<Type*>(I->get())->isTypeAbstract()) {
      setAbstract(true);        // Restore the abstract bit.
      return true;              // This type is abstract if subtype is abstract!
    }
  
  // Restore the abstract bit.
  setAbstract(true);

  // Nothing looks abstract here...
  return false;
}


//===----------------------------------------------------------------------===//
//                      Type Structural Equality Testing
//===----------------------------------------------------------------------===//

// TypesEqual - Two types are considered structurally equal if they have the
// same "shape": Every level and element of the types have identical primitive
// ID's, and the graphs have the same edges/nodes in them.  Nodes do not have to
// be pointer equals to be equivalent though.  This uses an optimistic algorithm
// that assumes that two graphs are the same until proven otherwise.
//
static bool TypesEqual(const Type *Ty, const Type *Ty2,
                       std::map<const Type *, const Type *> &EqTypes) {
  if (Ty == Ty2) return true;
  if (Ty->getTypeID() != Ty2->getTypeID()) return false;
  if (isa<OpaqueType>(Ty))
    return false;  // Two unequal opaque types are never equal

  std::map<const Type*, const Type*>::iterator It = EqTypes.lower_bound(Ty);
  if (It != EqTypes.end() && It->first == Ty)
    return It->second == Ty2;    // Looping back on a type, check for equality

  // Otherwise, add the mapping to the table to make sure we don't get
  // recursion on the types...
  EqTypes.insert(It, std::make_pair(Ty, Ty2));

  // Two really annoying special cases that breaks an otherwise nice simple
  // algorithm is the fact that arraytypes have sizes that differentiates types,
  // and that function types can be varargs or not.  Consider this now.
  //
  if (const PointerType *PTy = dyn_cast<PointerType>(Ty)) {
    return TypesEqual(PTy->getElementType(),
                      cast<PointerType>(Ty2)->getElementType(), EqTypes);
  } else if (const StructType *STy = dyn_cast<StructType>(Ty)) {
    const StructType *STy2 = cast<StructType>(Ty2);
    if (STy->getNumElements() != STy2->getNumElements()) return false;
    for (unsigned i = 0, e = STy2->getNumElements(); i != e; ++i)
      if (!TypesEqual(STy->getElementType(i), STy2->getElementType(i), EqTypes))
        return false;
    return true;
  } else if (const ArrayType *ATy = dyn_cast<ArrayType>(Ty)) {
    const ArrayType *ATy2 = cast<ArrayType>(Ty2);
    return ATy->getNumElements() == ATy2->getNumElements() &&
           TypesEqual(ATy->getElementType(), ATy2->getElementType(), EqTypes);
  } else if (const FunctionType *FTy = dyn_cast<FunctionType>(Ty)) {
    const FunctionType *FTy2 = cast<FunctionType>(Ty2);
    if (FTy->isVarArg() != FTy2->isVarArg() ||
        FTy->getNumParams() != FTy2->getNumParams() ||
        !TypesEqual(FTy->getReturnType(), FTy2->getReturnType(), EqTypes))
      return false;
    for (unsigned i = 0, e = FTy2->getNumParams(); i != e; ++i)
      if (!TypesEqual(FTy->getParamType(i), FTy2->getParamType(i), EqTypes))
        return false;
    return true;
  } else {
    assert(0 && "Unknown derived type!");
    return false;
  }
}

static bool TypesEqual(const Type *Ty, const Type *Ty2) {
  std::map<const Type *, const Type *> EqTypes;
  return TypesEqual(Ty, Ty2, EqTypes);
}

// TypeHasCycleThrough - Return true there is a path from CurTy to TargetTy in
// the type graph.  We know that Ty is an abstract type, so if we ever reach a
// non-abstract type, we know that we don't need to search the subgraph.
static bool TypeHasCycleThrough(const Type *TargetTy, const Type *CurTy,
                                std::set<const Type*> &VisitedTypes) {
  if (TargetTy == CurTy) return true;
  if (!CurTy->isAbstract()) return false;

  std::set<const Type*>::iterator VTI = VisitedTypes.lower_bound(CurTy);
  if (VTI != VisitedTypes.end() && *VTI == CurTy)
    return false;
  VisitedTypes.insert(VTI, CurTy);

  for (Type::subtype_iterator I = CurTy->subtype_begin(), 
       E = CurTy->subtype_end(); I != E; ++I)
    if (TypeHasCycleThrough(TargetTy, *I, VisitedTypes))
      return true;
  return false;
}


/// TypeHasCycleThroughItself - Return true if the specified type has a cycle
/// back to itself.
static bool TypeHasCycleThroughItself(const Type *Ty) {
  assert(Ty->isAbstract() && "This code assumes that Ty was abstract!");
  std::set<const Type*> VisitedTypes;
  for (Type::subtype_iterator I = Ty->subtype_begin(), E = Ty->subtype_end(); 
       I != E; ++I)
    if (TypeHasCycleThrough(Ty, *I, VisitedTypes))
      return true;
  return false;
}


//===----------------------------------------------------------------------===//
//                       Derived Type Factory Functions
//===----------------------------------------------------------------------===//

// TypeMap - Make sure that only one instance of a particular type may be
// created on any given run of the compiler... note that this involves updating
// our map if an abstract type gets refined somehow.
//
namespace llvm {
template<class ValType, class TypeClass>
class TypeMap {
  std::map<ValType, PATypeHolder> Map;

  /// TypesByHash - Keep track of each type by its structure hash value.
  ///
  std::multimap<unsigned, PATypeHolder> TypesByHash;
public:
  typedef typename std::map<ValType, PATypeHolder>::iterator iterator;
  ~TypeMap() { print("ON EXIT"); }

  inline TypeClass *get(const ValType &V) {
    iterator I = Map.find(V);
    return I != Map.end() ? cast<TypeClass>((Type*)I->second.get()) : 0;
  }

  inline void add(const ValType &V, TypeClass *Ty) {
    Map.insert(std::make_pair(V, Ty));

    // If this type has a cycle, remember it.
    TypesByHash.insert(std::make_pair(ValType::hashTypeStructure(Ty), Ty));
    print("add");
  }

  void RemoveFromTypesByHash(unsigned Hash, const Type *Ty) {
    std::multimap<unsigned, PATypeHolder>::iterator I = 
      TypesByHash.lower_bound(Hash);
    while (I->second != Ty) {
      ++I;
      assert(I != TypesByHash.end() && I->first == Hash);
    }
    TypesByHash.erase(I);
  }

  /// finishRefinement - This method is called after we have updated an existing
  /// type with its new components.  We must now either merge the type away with
  /// some other type or reinstall it in the map with it's new configuration.
  /// The specified iterator tells us what the type USED to look like.
  void finishRefinement(TypeClass *Ty, const DerivedType *OldType,
                        const Type *NewType) {
    assert((Ty->isAbstract() || !OldType->isAbstract()) &&
           "Refining a non-abstract type!");
#ifdef DEBUG_MERGE_TYPES
    std::cerr << "refineAbstractTy(" << (void*)OldType << "[" << *OldType
              << "], " << (void*)NewType << " [" << *NewType << "])\n";
#endif

    // Make a temporary type holder for the type so that it doesn't disappear on
    // us when we erase the entry from the map.
    PATypeHolder TyHolder = Ty;

    // The old record is now out-of-date, because one of the children has been
    // updated.  Remove the obsolete entry from the map.
    Map.erase(ValType::get(Ty));

    // Remember the structural hash for the type before we start hacking on it,
    // in case we need it later.  Also, check to see if the type HAD a cycle
    // through it, if so, we know it will when we hack on it.
    unsigned OldTypeHash = ValType::hashTypeStructure(Ty);

    // Find the type element we are refining... and change it now!
    for (unsigned i = 0, e = Ty->ContainedTys.size(); i != e; ++i)
      if (Ty->ContainedTys[i] == OldType) {
        Ty->ContainedTys[i].removeUserFromConcrete();
        Ty->ContainedTys[i] = NewType;
      }

    unsigned TypeHash = ValType::hashTypeStructure(Ty);
    
    // If there are no cycles going through this node, we can do a simple,
    // efficient lookup in the map, instead of an inefficient nasty linear
    // lookup.
    bool TypeHasCycle = Ty->isAbstract() && TypeHasCycleThroughItself(Ty);
    if (!TypeHasCycle) {
      iterator I = Map.find(ValType::get(Ty));
      if (I != Map.end()) {
        // We already have this type in the table.  Get rid of the newly refined
        // type.
        assert(Ty->isAbstract() && "Replacing a non-abstract type?");
        TypeClass *NewTy = cast<TypeClass>((Type*)I->second.get());
        
        // Refined to a different type altogether?
        RemoveFromTypesByHash(TypeHash, Ty);
        Ty->refineAbstractTypeTo(NewTy);
        return;
      }
      
    } else {
      // Now we check to see if there is an existing entry in the table which is
      // structurally identical to the newly refined type.  If so, this type
      // gets refined to the pre-existing type.
      //
      std::multimap<unsigned, PATypeHolder>::iterator I,E, Entry;
      tie(I, E) = TypesByHash.equal_range(TypeHash);
      Entry = E;
      for (; I != E; ++I) {
        if (I->second != Ty) {
          if (TypesEqual(Ty, I->second)) {
            assert(Ty->isAbstract() && "Replacing a non-abstract type?");
            TypeClass *NewTy = cast<TypeClass>((Type*)I->second.get());
            
            if (Entry == E) {
              // Find the location of Ty in the TypesByHash structure.
              while (I->second != Ty) {
                ++I;
                assert(I != E && "Structure doesn't contain type??");
              }
              Entry = I;
            }

            TypesByHash.erase(Entry);
            Ty->refineAbstractTypeTo(NewTy);
            return;
          }
        } else {
          // Remember the position of 
          Entry = I;
        }
      }
    }

    // If we succeeded, we need to insert the type into the cycletypes table.
    // There are several cases here, depending on whether the original type
    // had the same hash code and was itself cyclic.
    if (TypeHash != OldTypeHash) {
      RemoveFromTypesByHash(OldTypeHash, Ty);
      TypesByHash.insert(std::make_pair(TypeHash, Ty));
    }

    // If there is no existing type of the same structure, we reinsert an
    // updated record into the map.
    Map.insert(std::make_pair(ValType::get(Ty), Ty));

    // If the type is currently thought to be abstract, rescan all of our
    // subtypes to see if the type has just become concrete!
    if (Ty->isAbstract()) {
      Ty->setAbstract(Ty->isTypeAbstract());

      // If the type just became concrete, notify all users!
      if (!Ty->isAbstract())
        Ty->notifyUsesThatTypeBecameConcrete();
    }
  }
  
  void print(const char *Arg) const {
#ifdef DEBUG_MERGE_TYPES
    std::cerr << "TypeMap<>::" << Arg << " table contents:\n";
    unsigned i = 0;
    for (typename std::map<ValType, PATypeHolder>::const_iterator I
           = Map.begin(), E = Map.end(); I != E; ++I)
      std::cerr << " " << (++i) << ". " << (void*)I->second.get() << " " 
                << *I->second.get() << "\n";
#endif
  }

  void dump() const { print("dump output"); }
};
}


//===----------------------------------------------------------------------===//
// Function Type Factory and Value Class...
//

// FunctionValType - Define a class to hold the key that goes into the TypeMap
//
namespace llvm {
class FunctionValType {
  const Type *RetTy;
  std::vector<const Type*> ArgTypes;
  bool isVarArg;
public:
  FunctionValType(const Type *ret, const std::vector<const Type*> &args,
                  bool IVA) : RetTy(ret), isVarArg(IVA) {
    for (unsigned i = 0; i < args.size(); ++i)
      ArgTypes.push_back(args[i]);
  }

  static FunctionValType get(const FunctionType *FT);

  static unsigned hashTypeStructure(const FunctionType *FT) {
    return FT->getNumParams()*2+FT->isVarArg();
  }

  // Subclass should override this... to update self as usual
  void doRefinement(const DerivedType *OldType, const Type *NewType) {
    if (RetTy == OldType) RetTy = NewType;
    for (unsigned i = 0, e = ArgTypes.size(); i != e; ++i)
      if (ArgTypes[i] == OldType) ArgTypes[i] = NewType;
  }

  inline bool operator<(const FunctionValType &MTV) const {
    if (RetTy < MTV.RetTy) return true;
    if (RetTy > MTV.RetTy) return false;

    if (ArgTypes < MTV.ArgTypes) return true;
    return ArgTypes == MTV.ArgTypes && isVarArg < MTV.isVarArg;
  }
};
}

// Define the actual map itself now...
static TypeMap<FunctionValType, FunctionType> FunctionTypes;

FunctionValType FunctionValType::get(const FunctionType *FT) {
  // Build up a FunctionValType
  std::vector<const Type *> ParamTypes;
  ParamTypes.reserve(FT->getNumParams());
  for (unsigned i = 0, e = FT->getNumParams(); i != e; ++i)
    ParamTypes.push_back(FT->getParamType(i));
  return FunctionValType(FT->getReturnType(), ParamTypes, FT->isVarArg());
}


// FunctionType::get - The factory function for the FunctionType class...
FunctionType *FunctionType::get(const Type *ReturnType, 
                                const std::vector<const Type*> &Params,
                                bool isVarArg) {
  FunctionValType VT(ReturnType, Params, isVarArg);
  FunctionType *MT = FunctionTypes.get(VT);
  if (MT) return MT;

  FunctionTypes.add(VT, MT = new FunctionType(ReturnType, Params, isVarArg));

#ifdef DEBUG_MERGE_TYPES
  std::cerr << "Derived new type: " << MT << "\n";
#endif
  return MT;
}

//===----------------------------------------------------------------------===//
// Array Type Factory...
//
namespace llvm {
class ArrayValType {
  const Type *ValTy;
  unsigned Size;
public:
  ArrayValType(const Type *val, int sz) : ValTy(val), Size(sz) {}

  static ArrayValType get(const ArrayType *AT) {
    return ArrayValType(AT->getElementType(), AT->getNumElements());
  }

  static unsigned hashTypeStructure(const ArrayType *AT) {
    return AT->getNumElements();
  }

  // Subclass should override this... to update self as usual
  void doRefinement(const DerivedType *OldType, const Type *NewType) {
    assert(ValTy == OldType);
    ValTy = NewType;
  }

  inline bool operator<(const ArrayValType &MTV) const {
    if (Size < MTV.Size) return true;
    return Size == MTV.Size && ValTy < MTV.ValTy;
  }
};
}
static TypeMap<ArrayValType, ArrayType> ArrayTypes;


ArrayType *ArrayType::get(const Type *ElementType, unsigned NumElements) {
  assert(ElementType && "Can't get array of null types!");

  ArrayValType AVT(ElementType, NumElements);
  ArrayType *AT = ArrayTypes.get(AVT);
  if (AT) return AT;           // Found a match, return it!

  // Value not found.  Derive a new type!
  ArrayTypes.add(AVT, AT = new ArrayType(ElementType, NumElements));

#ifdef DEBUG_MERGE_TYPES
  std::cerr << "Derived new type: " << *AT << "\n";
#endif
  return AT;
}

//===----------------------------------------------------------------------===//
// Struct Type Factory...
//

namespace llvm {
// StructValType - Define a class to hold the key that goes into the TypeMap
//
class StructValType {
  std::vector<const Type*> ElTypes;
public:
  StructValType(const std::vector<const Type*> &args) : ElTypes(args) {}

  static StructValType get(const StructType *ST) {
    std::vector<const Type *> ElTypes;
    ElTypes.reserve(ST->getNumElements());
    for (unsigned i = 0, e = ST->getNumElements(); i != e; ++i)
      ElTypes.push_back(ST->getElementType(i));
    
    return StructValType(ElTypes);
  }

  static unsigned hashTypeStructure(const StructType *ST) {
    return ST->getNumElements();
  }

  // Subclass should override this... to update self as usual
  void doRefinement(const DerivedType *OldType, const Type *NewType) {
    for (unsigned i = 0; i < ElTypes.size(); ++i)
      if (ElTypes[i] == OldType) ElTypes[i] = NewType;
  }

  inline bool operator<(const StructValType &STV) const {
    return ElTypes < STV.ElTypes;
  }
};
}

static TypeMap<StructValType, StructType> StructTypes;

StructType *StructType::get(const std::vector<const Type*> &ETypes) {
  StructValType STV(ETypes);
  StructType *ST = StructTypes.get(STV);
  if (ST) return ST;

  // Value not found.  Derive a new type!
  StructTypes.add(STV, ST = new StructType(ETypes));

#ifdef DEBUG_MERGE_TYPES
  std::cerr << "Derived new type: " << *ST << "\n";
#endif
  return ST;
}



//===----------------------------------------------------------------------===//
// Pointer Type Factory...
//

// PointerValType - Define a class to hold the key that goes into the TypeMap
//
namespace llvm {
class PointerValType {
  const Type *ValTy;
public:
  PointerValType(const Type *val) : ValTy(val) {}

  static PointerValType get(const PointerType *PT) {
    return PointerValType(PT->getElementType());
  }

  static unsigned hashTypeStructure(const PointerType *PT) {
    return 0;
  }

  // Subclass should override this... to update self as usual
  void doRefinement(const DerivedType *OldType, const Type *NewType) {
    assert(ValTy == OldType);
    ValTy = NewType;
  }

  bool operator<(const PointerValType &MTV) const {
    return ValTy < MTV.ValTy;
  }
};
}

static TypeMap<PointerValType, PointerType> PointerTypes;

PointerType *PointerType::get(const Type *ValueType) {
  assert(ValueType && "Can't get a pointer to <null> type!");
  PointerValType PVT(ValueType);

  PointerType *PT = PointerTypes.get(PVT);
  if (PT) return PT;

  // Value not found.  Derive a new type!
  PointerTypes.add(PVT, PT = new PointerType(ValueType));

#ifdef DEBUG_MERGE_TYPES
  std::cerr << "Derived new type: " << *PT << "\n";
#endif
  return PT;
}


//===----------------------------------------------------------------------===//
//                     Derived Type Refinement Functions
//===----------------------------------------------------------------------===//

// removeAbstractTypeUser - Notify an abstract type that a user of the class
// no longer has a handle to the type.  This function is called primarily by
// the PATypeHandle class.  When there are no users of the abstract type, it
// is annihilated, because there is no way to get a reference to it ever again.
//
void DerivedType::removeAbstractTypeUser(AbstractTypeUser *U) const {
  // Search from back to front because we will notify users from back to
  // front.  Also, it is likely that there will be a stack like behavior to
  // users that register and unregister users.
  //
  unsigned i;
  for (i = AbstractTypeUsers.size(); AbstractTypeUsers[i-1] != U; --i)
    assert(i != 0 && "AbstractTypeUser not in user list!");

  --i;  // Convert to be in range 0 <= i < size()
  assert(i < AbstractTypeUsers.size() && "Index out of range!");  // Wraparound?

  AbstractTypeUsers.erase(AbstractTypeUsers.begin()+i);
      
#ifdef DEBUG_MERGE_TYPES
  std::cerr << "  remAbstractTypeUser[" << (void*)this << ", "
            << *this << "][" << i << "] User = " << U << "\n";
#endif
    
  if (AbstractTypeUsers.empty() && getRefCount() == 0 && isAbstract()) {
#ifdef DEBUG_MERGE_TYPES
    std::cerr << "DELETEing unused abstract type: <" << *this
              << ">[" << (void*)this << "]" << "\n";
#endif
    delete this;                  // No users of this abstract type!
  }
}


// refineAbstractTypeTo - This function is used to when it is discovered that
// the 'this' abstract type is actually equivalent to the NewType specified.
// This causes all users of 'this' to switch to reference the more concrete type
// NewType and for 'this' to be deleted.
//
void DerivedType::refineAbstractTypeTo(const Type *NewType) {
  assert(isAbstract() && "refineAbstractTypeTo: Current type is not abstract!");
  assert(this != NewType && "Can't refine to myself!");
  assert(ForwardType == 0 && "This type has already been refined!");

  // The descriptions may be out of date.  Conservatively clear them all!
  AbstractTypeDescriptions.clear();

#ifdef DEBUG_MERGE_TYPES
  std::cerr << "REFINING abstract type [" << (void*)this << " "
            << *this << "] to [" << (void*)NewType << " "
            << *NewType << "]!\n";
#endif

  // Make sure to put the type to be refined to into a holder so that if IT gets
  // refined, that we will not continue using a dead reference...
  //
  PATypeHolder NewTy(NewType);

  // Any PATypeHolders referring to this type will now automatically forward to
  // the type we are resolved to.
  ForwardType = NewType;
  if (NewType->isAbstract())
    cast<DerivedType>(NewType)->addRef();

  // Add a self use of the current type so that we don't delete ourself until
  // after the function exits.
  //
  PATypeHolder CurrentTy(this);

  // To make the situation simpler, we ask the subclass to remove this type from
  // the type map, and to replace any type uses with uses of non-abstract types.
  // This dramatically limits the amount of recursive type trouble we can find
  // ourselves in.
  dropAllTypeUses();

  // Iterate over all of the uses of this type, invoking callback.  Each user
  // should remove itself from our use list automatically.  We have to check to
  // make sure that NewTy doesn't _become_ 'this'.  If it does, resolving types
  // will not cause users to drop off of the use list.  If we resolve to ourself
  // we succeed!
  //
  while (!AbstractTypeUsers.empty() && NewTy != this) {
    AbstractTypeUser *User = AbstractTypeUsers.back();

    unsigned OldSize = AbstractTypeUsers.size();
#ifdef DEBUG_MERGE_TYPES
    std::cerr << " REFINING user " << OldSize-1 << "[" << (void*)User
              << "] of abstract type [" << (void*)this << " "
              << *this << "] to [" << (void*)NewTy.get() << " "
              << *NewTy << "]!\n";
#endif
    User->refineAbstractType(this, NewTy);

    assert(AbstractTypeUsers.size() != OldSize &&
           "AbsTyUser did not remove self from user list!");
  }

  // If we were successful removing all users from the type, 'this' will be
  // deleted when the last PATypeHolder is destroyed or updated from this type.
  // This may occur on exit of this function, as the CurrentTy object is
  // destroyed.
}

// notifyUsesThatTypeBecameConcrete - Notify AbstractTypeUsers of this type that
// the current type has transitioned from being abstract to being concrete.
//
void DerivedType::notifyUsesThatTypeBecameConcrete() {
#ifdef DEBUG_MERGE_TYPES
  std::cerr << "typeIsREFINED type: " << (void*)this << " " << *this << "\n";
#endif

  unsigned OldSize = AbstractTypeUsers.size();
  while (!AbstractTypeUsers.empty()) {
    AbstractTypeUser *ATU = AbstractTypeUsers.back();
    ATU->typeBecameConcrete(this);

    assert(AbstractTypeUsers.size() < OldSize-- &&
           "AbstractTypeUser did not remove itself from the use list!");
  }
}
  



// refineAbstractType - Called when a contained type is found to be more
// concrete - this could potentially change us from an abstract type to a
// concrete type.
//
void FunctionType::refineAbstractType(const DerivedType *OldType,
                                      const Type *NewType) {
  FunctionTypes.finishRefinement(this, OldType, NewType);
}

void FunctionType::typeBecameConcrete(const DerivedType *AbsTy) {
  refineAbstractType(AbsTy, AbsTy);
}


// refineAbstractType - Called when a contained type is found to be more
// concrete - this could potentially change us from an abstract type to a
// concrete type.
//
void ArrayType::refineAbstractType(const DerivedType *OldType,
                                   const Type *NewType) {
  ArrayTypes.finishRefinement(this, OldType, NewType);
}

void ArrayType::typeBecameConcrete(const DerivedType *AbsTy) {
  refineAbstractType(AbsTy, AbsTy);
}


// refineAbstractType - Called when a contained type is found to be more
// concrete - this could potentially change us from an abstract type to a
// concrete type.
//
void StructType::refineAbstractType(const DerivedType *OldType,
                                    const Type *NewType) {
  StructTypes.finishRefinement(this, OldType, NewType);
}

void StructType::typeBecameConcrete(const DerivedType *AbsTy) {
  refineAbstractType(AbsTy, AbsTy);
}

// refineAbstractType - Called when a contained type is found to be more
// concrete - this could potentially change us from an abstract type to a
// concrete type.
//
void PointerType::refineAbstractType(const DerivedType *OldType,
                                     const Type *NewType) {
  PointerTypes.finishRefinement(this, OldType, NewType);
}

void PointerType::typeBecameConcrete(const DerivedType *AbsTy) {
  refineAbstractType(AbsTy, AbsTy);
}

bool SequentialType::indexValid(const Value *V) const {
  const Type *Ty = V->getType();
  switch (Ty->getTypeID()) {
  case Type::IntTyID:
  case Type::UIntTyID:
  case Type::LongTyID:
  case Type::ULongTyID:
    return true;
  default:
    return false;
  }
}

namespace llvm {
std::ostream &operator<<(std::ostream &OS, const Type *T) {
  if (T == 0)
    OS << "<null> value!\n";
  else
    T->print(OS);
  return OS;
}

std::ostream &operator<<(std::ostream &OS, const Type &T) {
  T.print(OS);
  return OS;
}
}

// vim: sw=2
