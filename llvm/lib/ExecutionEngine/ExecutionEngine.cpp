//===-- ExecutionEngine.cpp - Common Implementation shared by EEs ---------===//
// 
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
// 
//===----------------------------------------------------------------------===//
// 
// This file defines the common interface used by the various execution engine
// subclasses.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "jit"
#include "Interpreter/Interpreter.h"
#include "JIT/JIT.h"
#include "llvm/Constants.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Module.h"
#include "llvm/ModuleProvider.h"
#include "llvm/CodeGen/IntrinsicLowering.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/GenericValue.h"
#include "llvm/Target/TargetData.h"
#include "Support/Debug.h"
#include "Support/Statistic.h"
#include "Support/DynamicLinker.h"
using namespace llvm;

namespace {
  Statistic<> NumInitBytes("lli", "Number of bytes of global vars initialized");
  Statistic<> NumGlobals  ("lli", "Number of global vars initialized");
}

ExecutionEngine::ExecutionEngine(ModuleProvider *P) : 
  CurMod(*P->getModule()), MP(P) {
  assert(P && "ModuleProvider is null?");
}

ExecutionEngine::ExecutionEngine(Module *M) : CurMod(*M), MP(0) {
  assert(M && "Module is null?");
}

ExecutionEngine::~ExecutionEngine() {
  delete MP;
}

/// getGlobalValueAtAddress - Return the LLVM global value object that starts
/// at the specified address.
///
const GlobalValue *ExecutionEngine::getGlobalValueAtAddress(void *Addr) {
  // If we haven't computed the reverse mapping yet, do so first.
  if (GlobalAddressReverseMap.empty()) {
    for (std::map<const GlobalValue*, void *>::iterator I = 
           GlobalAddressMap.begin(), E = GlobalAddressMap.end(); I != E; ++I)
      GlobalAddressReverseMap.insert(std::make_pair(I->second, I->first));
  }

  std::map<void *, const GlobalValue*>::iterator I =
    GlobalAddressReverseMap.find(Addr);
  return I != GlobalAddressReverseMap.end() ? I->second : 0;
}

// CreateArgv - Turn a vector of strings into a nice argv style array of
// pointers to null terminated strings.
//
static void *CreateArgv(ExecutionEngine *EE,
                        const std::vector<std::string> &InputArgv) {
  unsigned PtrSize = EE->getTargetData().getPointerSize();
  char *Result = new char[(InputArgv.size()+1)*PtrSize];

  DEBUG(std::cerr << "ARGV = " << (void*)Result << "\n");
  const Type *SBytePtr = PointerType::get(Type::SByteTy);

  for (unsigned i = 0; i != InputArgv.size(); ++i) {
    unsigned Size = InputArgv[i].size()+1;
    char *Dest = new char[Size];
    DEBUG(std::cerr << "ARGV[" << i << "] = " << (void*)Dest << "\n");
      
    std::copy(InputArgv[i].begin(), InputArgv[i].end(), Dest);
    Dest[Size-1] = 0;
      
    // Endian safe: Result[i] = (PointerTy)Dest;
    EE->StoreValueToMemory(PTOGV(Dest), (GenericValue*)(Result+i*PtrSize),
                           SBytePtr);
  }

  // Null terminate it
  EE->StoreValueToMemory(PTOGV(0),
                         (GenericValue*)(Result+InputArgv.size()*PtrSize),
                         SBytePtr);
  return Result;
}

/// runFunctionAsMain - This is a helper function which wraps runFunction to
/// handle the common task of starting up main with the specified argc, argv,
/// and envp parameters.
int ExecutionEngine::runFunctionAsMain(Function *Fn,
                                       const std::vector<std::string> &argv,
                                       const char * const * envp) {
  std::vector<GenericValue> GVArgs;
  GenericValue GVArgc;
  GVArgc.IntVal = argv.size();
  GVArgs.push_back(GVArgc); // Arg #0 = argc.
  GVArgs.push_back(PTOGV(CreateArgv(this, argv))); // Arg #1 = argv.
  assert(((char **)GVTOP(GVArgs[1]))[0] && "argv[0] was null after CreateArgv");

  std::vector<std::string> EnvVars;
  for (unsigned i = 0; envp[i]; ++i)
    EnvVars.push_back(envp[i]);
  GVArgs.push_back(PTOGV(CreateArgv(this, EnvVars))); // Arg #2 = envp.
  return runFunction(Fn, GVArgs).IntVal;
}



/// If possible, create a JIT, unless the caller specifically requests an
/// Interpreter or there's an error. If even an Interpreter cannot be created,
/// NULL is returned. 
///
ExecutionEngine *ExecutionEngine::create(ModuleProvider *MP, 
                                         bool ForceInterpreter,
                                         IntrinsicLowering *IL) {
  ExecutionEngine *EE = 0;

  // Unless the interpreter was explicitly selected, try making a JIT.
  if (!ForceInterpreter)
    EE = JIT::create(MP, IL);

  // If we can't make a JIT, make an interpreter instead.
  if (EE == 0) {
    try {
      Module *M = MP->materializeModule();
      try {
        EE = Interpreter::create(M, IL);
      } catch (...) {
        std::cerr << "Error creating the interpreter!\n";
      }
    } catch (std::string& errmsg) {
      std::cerr << "Error reading the bytecode file: " << errmsg << "\n";
    } catch (...) {
      std::cerr << "Error reading the bytecode file!\n";
    }
  }

  if (EE == 0) delete IL;
  return EE;
}

/// getPointerToGlobal - This returns the address of the specified global
/// value.  This may involve code generation if it's a function.
///
void *ExecutionEngine::getPointerToGlobal(const GlobalValue *GV) {
  if (Function *F = const_cast<Function*>(dyn_cast<Function>(GV)))
    return getPointerToFunction(F);

  assert(GlobalAddressMap[GV] && "Global hasn't had an address allocated yet?");
  return GlobalAddressMap[GV];
}

/// FIXME: document
/// 
GenericValue ExecutionEngine::getConstantValue(const Constant *C) {
  GenericValue Result;

  if (ConstantExpr *CE = const_cast<ConstantExpr*>(dyn_cast<ConstantExpr>(C))) {
    switch (CE->getOpcode()) {
    case Instruction::GetElementPtr: {
      Result = getConstantValue(CE->getOperand(0));
      std::vector<Value*> Indexes(CE->op_begin()+1, CE->op_end());
      uint64_t Offset =
        TD->getIndexedOffset(CE->getOperand(0)->getType(), Indexes);
                             
      Result.LongVal += Offset;
      return Result;
    }
    case Instruction::Cast: {
      // We only need to handle a few cases here.  Almost all casts will
      // automatically fold, just the ones involving pointers won't.
      //
      Constant *Op = CE->getOperand(0);
      GenericValue GV = getConstantValue(Op);

      // Handle cast of pointer to pointer...
      if (Op->getType()->getTypeID() == C->getType()->getTypeID())
        return GV;

      // Handle a cast of pointer to any integral type...
      if (isa<PointerType>(Op->getType()) && C->getType()->isIntegral())
        return GV;
        
      // Handle cast of integer to a pointer...
      if (isa<PointerType>(C->getType()) && Op->getType()->isIntegral())
        switch (Op->getType()->getTypeID()) {
        case Type::BoolTyID:    return PTOGV((void*)(uintptr_t)GV.BoolVal);
        case Type::SByteTyID:   return PTOGV((void*)( intptr_t)GV.SByteVal);
        case Type::UByteTyID:   return PTOGV((void*)(uintptr_t)GV.UByteVal);
        case Type::ShortTyID:   return PTOGV((void*)( intptr_t)GV.ShortVal);
        case Type::UShortTyID:  return PTOGV((void*)(uintptr_t)GV.UShortVal);
        case Type::IntTyID:     return PTOGV((void*)( intptr_t)GV.IntVal);
        case Type::UIntTyID:    return PTOGV((void*)(uintptr_t)GV.UIntVal);
        case Type::LongTyID:    return PTOGV((void*)( intptr_t)GV.LongVal);
        case Type::ULongTyID:   return PTOGV((void*)(uintptr_t)GV.ULongVal);
        default: assert(0 && "Unknown integral type!");
        }
      break;
    }

    case Instruction::Add:
      switch (CE->getOperand(0)->getType()->getTypeID()) {
      default: assert(0 && "Bad add type!"); abort();
      case Type::LongTyID:
      case Type::ULongTyID:
        Result.LongVal = getConstantValue(CE->getOperand(0)).LongVal +
                         getConstantValue(CE->getOperand(1)).LongVal;
        break;
      case Type::IntTyID:
      case Type::UIntTyID:
        Result.IntVal = getConstantValue(CE->getOperand(0)).IntVal +
                        getConstantValue(CE->getOperand(1)).IntVal;
        break;
      case Type::ShortTyID:
      case Type::UShortTyID:
        Result.ShortVal = getConstantValue(CE->getOperand(0)).ShortVal +
                          getConstantValue(CE->getOperand(1)).ShortVal;
        break;
      case Type::SByteTyID:
      case Type::UByteTyID:
        Result.SByteVal = getConstantValue(CE->getOperand(0)).SByteVal +
                          getConstantValue(CE->getOperand(1)).SByteVal;
        break;
      case Type::FloatTyID:
        Result.FloatVal = getConstantValue(CE->getOperand(0)).FloatVal +
                          getConstantValue(CE->getOperand(1)).FloatVal;
        break;
      case Type::DoubleTyID:
        Result.DoubleVal = getConstantValue(CE->getOperand(0)).DoubleVal +
                           getConstantValue(CE->getOperand(1)).DoubleVal;
        break;
      }
      return Result;
    default:
      break;
    }
    std::cerr << "ConstantExpr not handled as global var init: " << *CE << "\n";
    abort();
  }
  
  switch (C->getType()->getTypeID()) {
#define GET_CONST_VAL(TY, CLASS) \
  case Type::TY##TyID: Result.TY##Val = cast<CLASS>(C)->getValue(); break
    GET_CONST_VAL(Bool   , ConstantBool);
    GET_CONST_VAL(UByte  , ConstantUInt);
    GET_CONST_VAL(SByte  , ConstantSInt);
    GET_CONST_VAL(UShort , ConstantUInt);
    GET_CONST_VAL(Short  , ConstantSInt);
    GET_CONST_VAL(UInt   , ConstantUInt);
    GET_CONST_VAL(Int    , ConstantSInt);
    GET_CONST_VAL(ULong  , ConstantUInt);
    GET_CONST_VAL(Long   , ConstantSInt);
    GET_CONST_VAL(Float  , ConstantFP);
    GET_CONST_VAL(Double , ConstantFP);
#undef GET_CONST_VAL
  case Type::PointerTyID:
    if (isa<ConstantPointerNull>(C))
      Result.PointerVal = 0;
    else if (const Function *F = dyn_cast<Function>(C))
      Result = PTOGV(getPointerToFunctionOrStub(const_cast<Function*>(F)));
    else if (const GlobalVariable* GV = dyn_cast<GlobalVariable>(C))
      Result = PTOGV(getOrEmitGlobalVariable(const_cast<GlobalVariable*>(GV)));
    else
      assert(0 && "Unknown constant pointer type!");
    break;
  default:
    std::cout << "ERROR: Constant unimp for type: " << *C->getType() << "\n";
    abort();
  }
  return Result;
}

/// FIXME: document
///
void ExecutionEngine::StoreValueToMemory(GenericValue Val, GenericValue *Ptr,
                                         const Type *Ty) {
  if (getTargetData().isLittleEndian()) {
    switch (Ty->getTypeID()) {
    case Type::BoolTyID:
    case Type::UByteTyID:
    case Type::SByteTyID:   Ptr->Untyped[0] = Val.UByteVal; break;
    case Type::UShortTyID:
    case Type::ShortTyID:   Ptr->Untyped[0] = Val.UShortVal & 255;
                            Ptr->Untyped[1] = (Val.UShortVal >> 8) & 255;
                            break;
    Store4BytesLittleEndian:
    case Type::FloatTyID:
    case Type::UIntTyID:
    case Type::IntTyID:     Ptr->Untyped[0] =  Val.UIntVal        & 255;
                            Ptr->Untyped[1] = (Val.UIntVal >>  8) & 255;
                            Ptr->Untyped[2] = (Val.UIntVal >> 16) & 255;
                            Ptr->Untyped[3] = (Val.UIntVal >> 24) & 255;
                            break;
    case Type::PointerTyID: if (getTargetData().getPointerSize() == 4)
                              goto Store4BytesLittleEndian;
    case Type::DoubleTyID:
    case Type::ULongTyID:
    case Type::LongTyID:    Ptr->Untyped[0] =  Val.ULongVal        & 255;
                            Ptr->Untyped[1] = (Val.ULongVal >>  8) & 255;
                            Ptr->Untyped[2] = (Val.ULongVal >> 16) & 255;
                            Ptr->Untyped[3] = (Val.ULongVal >> 24) & 255;
                            Ptr->Untyped[4] = (Val.ULongVal >> 32) & 255;
                            Ptr->Untyped[5] = (Val.ULongVal >> 40) & 255;
                            Ptr->Untyped[6] = (Val.ULongVal >> 48) & 255;
                            Ptr->Untyped[7] = (Val.ULongVal >> 56) & 255;
                            break;
    default:
      std::cout << "Cannot store value of type " << *Ty << "!\n";
    }
  } else {
    switch (Ty->getTypeID()) {
    case Type::BoolTyID:
    case Type::UByteTyID:
    case Type::SByteTyID:   Ptr->Untyped[0] = Val.UByteVal; break;
    case Type::UShortTyID:
    case Type::ShortTyID:   Ptr->Untyped[1] = Val.UShortVal & 255;
                            Ptr->Untyped[0] = (Val.UShortVal >> 8) & 255;
                            break;
    Store4BytesBigEndian:
    case Type::FloatTyID:
    case Type::UIntTyID:
    case Type::IntTyID:     Ptr->Untyped[3] =  Val.UIntVal        & 255;
                            Ptr->Untyped[2] = (Val.UIntVal >>  8) & 255;
                            Ptr->Untyped[1] = (Val.UIntVal >> 16) & 255;
                            Ptr->Untyped[0] = (Val.UIntVal >> 24) & 255;
                            break;
    case Type::PointerTyID: if (getTargetData().getPointerSize() == 4)
                              goto Store4BytesBigEndian;
    case Type::DoubleTyID:
    case Type::ULongTyID:
    case Type::LongTyID:    Ptr->Untyped[7] =  Val.ULongVal        & 255;
                            Ptr->Untyped[6] = (Val.ULongVal >>  8) & 255;
                            Ptr->Untyped[5] = (Val.ULongVal >> 16) & 255;
                            Ptr->Untyped[4] = (Val.ULongVal >> 24) & 255;
                            Ptr->Untyped[3] = (Val.ULongVal >> 32) & 255;
                            Ptr->Untyped[2] = (Val.ULongVal >> 40) & 255;
                            Ptr->Untyped[1] = (Val.ULongVal >> 48) & 255;
                            Ptr->Untyped[0] = (Val.ULongVal >> 56) & 255;
                            break;
    default:
      std::cout << "Cannot store value of type " << *Ty << "!\n";
    }
  }
}

/// FIXME: document
///
GenericValue ExecutionEngine::LoadValueFromMemory(GenericValue *Ptr,
                                                  const Type *Ty) {
  GenericValue Result;
  if (getTargetData().isLittleEndian()) {
    switch (Ty->getTypeID()) {
    case Type::BoolTyID:
    case Type::UByteTyID:
    case Type::SByteTyID:   Result.UByteVal = Ptr->Untyped[0]; break;
    case Type::UShortTyID:
    case Type::ShortTyID:   Result.UShortVal = (unsigned)Ptr->Untyped[0] |
                                              ((unsigned)Ptr->Untyped[1] << 8);
                            break;
    Load4BytesLittleEndian:                            
    case Type::FloatTyID:
    case Type::UIntTyID:
    case Type::IntTyID:     Result.UIntVal = (unsigned)Ptr->Untyped[0] |
                                            ((unsigned)Ptr->Untyped[1] <<  8) |
                                            ((unsigned)Ptr->Untyped[2] << 16) |
                                            ((unsigned)Ptr->Untyped[3] << 24);
                            break;
    case Type::PointerTyID: if (getTargetData().getPointerSize() == 4)
                              goto Load4BytesLittleEndian;
    case Type::DoubleTyID:
    case Type::ULongTyID:
    case Type::LongTyID:    Result.ULongVal = (uint64_t)Ptr->Untyped[0] |
                                             ((uint64_t)Ptr->Untyped[1] <<  8) |
                                             ((uint64_t)Ptr->Untyped[2] << 16) |
                                             ((uint64_t)Ptr->Untyped[3] << 24) |
                                             ((uint64_t)Ptr->Untyped[4] << 32) |
                                             ((uint64_t)Ptr->Untyped[5] << 40) |
                                             ((uint64_t)Ptr->Untyped[6] << 48) |
                                             ((uint64_t)Ptr->Untyped[7] << 56);
                            break;
    default:
      std::cout << "Cannot load value of type " << *Ty << "!\n";
      abort();
    }
  } else {
    switch (Ty->getTypeID()) {
    case Type::BoolTyID:
    case Type::UByteTyID:
    case Type::SByteTyID:   Result.UByteVal = Ptr->Untyped[0]; break;
    case Type::UShortTyID:
    case Type::ShortTyID:   Result.UShortVal = (unsigned)Ptr->Untyped[1] |
                                              ((unsigned)Ptr->Untyped[0] << 8);
                            break;
    Load4BytesBigEndian:
    case Type::FloatTyID:
    case Type::UIntTyID:
    case Type::IntTyID:     Result.UIntVal = (unsigned)Ptr->Untyped[3] |
                                            ((unsigned)Ptr->Untyped[2] <<  8) |
                                            ((unsigned)Ptr->Untyped[1] << 16) |
                                            ((unsigned)Ptr->Untyped[0] << 24);
                            break;
    case Type::PointerTyID: if (getTargetData().getPointerSize() == 4)
                              goto Load4BytesBigEndian;
    case Type::DoubleTyID:
    case Type::ULongTyID:
    case Type::LongTyID:    Result.ULongVal = (uint64_t)Ptr->Untyped[7] |
                                             ((uint64_t)Ptr->Untyped[6] <<  8) |
                                             ((uint64_t)Ptr->Untyped[5] << 16) |
                                             ((uint64_t)Ptr->Untyped[4] << 24) |
                                             ((uint64_t)Ptr->Untyped[3] << 32) |
                                             ((uint64_t)Ptr->Untyped[2] << 40) |
                                             ((uint64_t)Ptr->Untyped[1] << 48) |
                                             ((uint64_t)Ptr->Untyped[0] << 56);
                            break;
    default:
      std::cout << "Cannot load value of type " << *Ty << "!\n";
      abort();
    }
  }
  return Result;
}

// InitializeMemory - Recursive function to apply a Constant value into the
// specified memory location...
//
void ExecutionEngine::InitializeMemory(const Constant *Init, void *Addr) {
  if (Init->getType()->isFirstClassType()) {
    GenericValue Val = getConstantValue(Init);
    StoreValueToMemory(Val, (GenericValue*)Addr, Init->getType());
    return;
  } else if (isa<ConstantAggregateZero>(Init)) {
    unsigned Size = getTargetData().getTypeSize(Init->getType());
    memset(Addr, 0, Size);
    return;
  }

  switch (Init->getType()->getTypeID()) {
  case Type::ArrayTyID: {
    const ConstantArray *CPA = cast<ConstantArray>(Init);
    unsigned ElementSize = 
      getTargetData().getTypeSize(cast<ArrayType>(CPA->getType())->getElementType());
    for (unsigned i = 0, e = CPA->getNumOperands(); i != e; ++i)
      InitializeMemory(CPA->getOperand(i), (char*)Addr+i*ElementSize);
    return;
  }

  case Type::StructTyID: {
    const ConstantStruct *CPS = cast<ConstantStruct>(Init);
    const StructLayout *SL =
      getTargetData().getStructLayout(cast<StructType>(CPS->getType()));
    for (unsigned i = 0, e = CPS->getNumOperands(); i != e; ++i)
      InitializeMemory(CPS->getOperand(i), (char*)Addr+SL->MemberOffsets[i]);
    return;
  }

  default:
    std::cerr << "Bad Type: " << *Init->getType() << "\n";
    assert(0 && "Unknown constant type to initialize memory with!");
  }
}

/// EmitGlobals - Emit all of the global variables to memory, storing their
/// addresses into GlobalAddress.  This must make sure to copy the contents of
/// their initializers into the memory.
///
void ExecutionEngine::emitGlobals() {
  const TargetData &TD = getTargetData();
  
  // Loop over all of the global variables in the program, allocating the memory
  // to hold them.
  for (Module::giterator I = getModule().gbegin(), E = getModule().gend();
       I != E; ++I)
    if (!I->isExternal()) {
      // Get the type of the global...
      const Type *Ty = I->getType()->getElementType();
      
      // Allocate some memory for it!
      unsigned Size = TD.getTypeSize(Ty);
      addGlobalMapping(I, new char[Size]);
    } else {
      // External variable reference. Try to use the dynamic loader to
      // get a pointer to it.
      if (void *SymAddr = GetAddressOfSymbol(I->getName().c_str()))
        addGlobalMapping(I, SymAddr);
      else {
        std::cerr << "Could not resolve external global address: "
                  << I->getName() << "\n";
        abort();
      }
    }
  
  // Now that all of the globals are set up in memory, loop through them all and
  // initialize their contents.
  for (Module::giterator I = getModule().gbegin(), E = getModule().gend();
       I != E; ++I)
    if (!I->isExternal())
      EmitGlobalVariable(I);
}

// EmitGlobalVariable - This method emits the specified global variable to the
// address specified in GlobalAddresses, or allocates new memory if it's not
// already in the map.
void ExecutionEngine::EmitGlobalVariable(const GlobalVariable *GV) {
  void *GA = getPointerToGlobalIfAvailable(GV);
  DEBUG(std::cerr << "Global '" << GV->getName() << "' -> " << GA << "\n");

  const Type *ElTy = GV->getType()->getElementType();
  if (GA == 0) {
    // If it's not already specified, allocate memory for the global.
    GA = new char[getTargetData().getTypeSize(ElTy)];
    addGlobalMapping(GV, GA);
  }

  InitializeMemory(GV->getInitializer(), GA);
  NumInitBytes += getTargetData().getTypeSize(ElTy);
  ++NumGlobals;
}
