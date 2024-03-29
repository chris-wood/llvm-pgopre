//===-- Support/PluginLoader.h - Provide -load option to tool ---*- C++ -*-===//
// 
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
// 
//===----------------------------------------------------------------------===//
//
// A tool can #include this file to get a -load option that allows the user to
// load arbitrary shared objects into the tool's address space.  Note that this
// header can only be included by a program ONCE, so it should never to used by
// library authors.
//
//===----------------------------------------------------------------------===//

#ifndef SUPPORT_PLUGINLOADER_H
#define SUPPORT_PLUGINLOADER_H

#include "Support/CommandLine.h"

namespace llvm {
  struct PluginLoader {
    void operator=(const std::string &Filename);
  };

#ifndef DONT_GET_PLUGIN_LOADER_OPTION
  // This causes operator= above to be invoked for every -load option.
  static cl::opt<PluginLoader, false, cl::parser<std::string> >
    LoadOpt("load", cl::ZeroOrMore, cl::value_desc("pluginfilename"),
            cl::desc("Load the specified plugin"));
#endif
}

#endif
