//===- ArchiveReader.cpp - Code to read LLVM bytecode from .a files -------===//
// 
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
// 
//===----------------------------------------------------------------------===//
//
// This file implements the ReadArchiveFile interface, which allows a linker to
// read all of the LLVM bytecode files contained in a .a file.  This file
// understands the standard system .a file format.  This can only handle the .a
// variant prevalent on Linux systems so far, but may be extended.  See
// information in this source file for more information:
//   http://sources.redhat.com/cgi-bin/cvsweb.cgi/src/bfd/archive.c?cvsroot=src
//
//===----------------------------------------------------------------------===//

#include "llvm/Bytecode/Reader.h"
#include "llvm/Module.h"
#include "Support/FileUtilities.h"
#include <cstdlib>
#include <iostream>
using namespace llvm;

namespace {
  struct ar_hdr {
    char name[16];
    char date[12];
    char uid[6];
    char gid[6];
    char mode[8];
    char size[10];
    char fmag[2];          // Always equal to '`\n'
  };

  enum ObjectType {
    UserObject,            // A user .o/.bc file
    Unknown,               // Unknown file, just ignore it
    SVR4LongFilename,      // a "//" section used for long file names
    ArchiveSymbolTable,    // Symbol table produced by ranlib.
  };
}

/// getObjectType - Determine the type of object that this header represents.
/// This is capable of parsing the variety of special sections used for various
/// purposes.
///
static enum ObjectType getObjectType(ar_hdr *H, std::string MemberName,
                                     unsigned char *MemberData, unsigned Size) {
  // Check for sections with special names...
  if (MemberName == "__.SYMDEF       " || MemberName == "__.SYMDEF SORTED")
    return ArchiveSymbolTable;
  else if (MemberName == "//              ")
    return SVR4LongFilename;

  // Check to see if it looks like an llvm object file...
  if (Size >= 4 && !memcmp(MemberData, "llvm", 4))
    return UserObject;

  return Unknown;
}

static inline bool Error(std::string *ErrorStr, const char *Message) {
  if (ErrorStr) *ErrorStr = Message;
  return true;
}

static bool ParseSymbolTableSection(unsigned char *Buffer, unsigned Size,
                                    std::string *S) {
  // Currently not supported (succeeds without doing anything)
  return false;
}

static bool ReadArchiveBuffer(const std::string &ArchiveName,
                              unsigned char *Buffer, unsigned Length,
                              std::vector<Module*> &Objects,
                              std::string *ErrorStr) {
  if (Length < 8 || memcmp(Buffer, "!<arch>\n", 8))
    return Error(ErrorStr, "signature incorrect for an archive file!");
  Buffer += 8;  Length -= 8; // Skip the magic string.

  std::vector<char> LongFilenames;

  while (Length >= sizeof(ar_hdr)) {
    ar_hdr *Hdr = (ar_hdr*)Buffer;
    unsigned SizeFromHeader = atoi(Hdr->size);
    if (SizeFromHeader + sizeof(ar_hdr) > Length)
      return Error(ErrorStr, "invalid record length in archive file!");

    unsigned char *MemberData = Buffer + sizeof(ar_hdr);
    unsigned MemberSize = SizeFromHeader;
    // Get name of archive member.
    char *startp = Hdr->name;
    char *endp = (char *) memchr (startp, '/', sizeof(ar_hdr));
    if (memcmp (Hdr->name, "#1/", 3) == 0) {
      // 4.4BSD/MacOSX long filenames are abbreviated as "#1/L", where L is an
      // ASCII-coded decimal number representing the length of the name buffer,
      // which is prepended to the archive member's contents.
      unsigned NameLength = atoi (&Hdr->name[3]);
      startp = (char *) MemberData;
      endp = startp + NameLength;
      MemberData += NameLength;
      MemberSize -= NameLength;
    } else if (startp == endp && isdigit (Hdr->name[1])) {
      // SVR4 long filenames are abbreviated as "/I", where I is
      // an ASCII-coded decimal index into the LongFilenames vector.
      unsigned NameIndex = atoi (&Hdr->name[1]);
      assert (LongFilenames.size () > NameIndex
              && "SVR4-style long filename for archive member not found");
      startp = &LongFilenames[NameIndex];
      endp = strchr (startp, '/');
    } else if (startp == endp && Hdr->name[1] == '/') {
      // This is for the SVR4 long filename table (there might be other
      // names starting with // but I don't know about them). Make sure that
      // getObjectType sees it.
      endp = &Hdr->name[sizeof (Hdr->name)];
    }
    if (!endp) {
      // 4.4BSD/MacOSX *short* filenames are not guaranteed to have a
      // terminator. Start at the end of the field and backtrack over spaces.
      endp = startp + sizeof(Hdr->name);
      while (endp[-1] == ' ')
        --endp;
    }
    std::string MemberName (startp, endp);
    std::string FullMemberName = ArchiveName + "(" + MemberName + ")";

    switch (getObjectType(Hdr, MemberName, MemberData, MemberSize)) {
    case SVR4LongFilename:
      // If this is a long filename section, read all of the file names into the
      // LongFilenames vector.
      LongFilenames.assign (MemberData, MemberData + MemberSize);
      break;
    case UserObject: {
      Module *M = ParseBytecodeBuffer(MemberData, MemberSize,
                                      FullMemberName, ErrorStr);
      if (!M) return true;
      Objects.push_back(M);
      break;
    }
    case ArchiveSymbolTable:
      if (ParseSymbolTableSection(MemberData, MemberSize, ErrorStr))
        return true;
      break;
    default:
      std::cerr << "ReadArchiveBuffer: WARNING: Skipping unknown file: "
                << FullMemberName << "\n";
      break;   // Just ignore unknown files.
    }

    // Round SizeFromHeader up to an even number...
    SizeFromHeader = (SizeFromHeader+1)/2*2;
    Buffer += sizeof(ar_hdr)+SizeFromHeader;   // Move to the next entry
    Length -= sizeof(ar_hdr)+SizeFromHeader;
  }

  return Length != 0;
}


// ReadArchiveFile - Read bytecode files from the specified .a file, returning
// true on error, or false on success.  This does not support reading files from
// standard input.
//
bool llvm::ReadArchiveFile(const std::string &Filename,
                           std::vector<Module*> &Objects,std::string *ErrorStr){
  unsigned Length;

    // mmap in the file all at once...
  unsigned char *Buffer = 
     (unsigned char*)ReadFileIntoAddressSpace(Filename, Length);
  if (Buffer == 0) {
    if (ErrorStr) *ErrorStr = "Error reading file '" + Filename + "'!";
    return true;
  }
  
  // Parse the archive files we mmap'ped in
  bool Result = ReadArchiveBuffer(Filename, Buffer, Length, Objects, ErrorStr);
  
  // Unmmap the archive...
  UnmapFileFromAddressSpace(Buffer, Length);

  if (Result)    // Free any loaded objects
    while (!Objects.empty()) {
      delete Objects.back();
      Objects.pop_back();
    }
  
  return Result;
}
