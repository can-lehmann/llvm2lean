// Copyright 2026 Can Joshua Lehmann
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include <memory>
#include <system_error>

#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/InitLLVM.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/raw_ostream.h>

static llvm::cl::OptionCategory llvm2lean_category("llvm2lean options");

static llvm::cl::opt<std::string> input_filename(
  llvm::cl::Positional,
  llvm::cl::desc("<input .ll file>"),
  llvm::cl::Required,
  llvm::cl::cat(llvm2lean_category)
);

static llvm::cl::opt<std::string> output_filename(
  "o",
  llvm::cl::desc("Output filename"),
  llvm::cl::value_desc("filename"),
  llvm::cl::Required,
  llvm::cl::cat(llvm2lean_category)
);

int main(int argc, char** argv) {
  llvm::InitLLVM init(argc, argv);
  llvm::cl::HideUnrelatedOptions(llvm2lean_category);
  llvm::cl::ParseCommandLineOptions(argc, argv, "llvm2lean: LLVM IR to Lean 4 translator\n");

  llvm::LLVMContext context;
  llvm::SMDiagnostic diag;
  std::unique_ptr<llvm::Module> module = llvm::parseIRFile(input_filename, diag, context);
  if (!module) {
    diag.print(argv[0], llvm::errs());
    return 1;
  }

  std::error_code ec;
  llvm::raw_fd_ostream out(output_filename, ec, llvm::sys::fs::OF_Text);
  if (ec) {
    llvm::errs() << argv[0] << ": " << output_filename << ": " << ec.message() << "\n";
    return 1;
  }

  module->print(out, nullptr);
  return 0;
}
