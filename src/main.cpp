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
#include <fstream>
#include <map>
#include <set>
#include <sstream>

#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/ModuleSlotTracker.h>
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

class LeanLowering {
private:
  std::ostream& _stream;
  std::unordered_map<llvm::Value*, std::string> _names;

  void lower_type(std::ostream& stream, llvm::Type* type) {
    if (llvm::IntegerType* integer_type = llvm::dyn_cast<llvm::IntegerType>(type)) {
      stream << "(BitVec " << integer_type->getBitWidth() << ")";
    } else {
      assert(false && "Unsupported type");
    }
  }

  void lower_value(std::ostream& stream, llvm::Value* value) {
    if (_names.find(value) != _names.end()) {
      stream << _names[value];
    } else if (llvm::ConstantInt* constant_int = llvm::dyn_cast<llvm::ConstantInt>(value)) {
      stream << "(";
      llvm::SmallVector<char, 32> str;
      constant_int->getValue().toStringUnsigned(str, 10);
      stream << str.data();
      stream << " : ";
      lower_type(stream, constant_int->getType());
      stream << ")";
    } else {
      assert(false && "Unsupported value");
    }
  }

  void lower_inst(std::ostream& stream, llvm::Instruction* inst) {
    _names[inst] = "v" + std::to_string(_names.size());
    if (llvm::BinaryOperator* binop = llvm::dyn_cast<llvm::BinaryOperator>(inst)) {
      stream << "let " << _names[inst] << " := ";

      #define simple_binop(Kind, op) \
        case llvm::Instruction::Kind: \
          stream << "("; \
          lower_value(stream, binop->getOperand(0)); \
          stream << " " op " "; \
          lower_value(stream, binop->getOperand(1)); \
          stream << ")"; \
          break;
      
      switch (binop->getOpcode()) {
        simple_binop(Add, "+")
        simple_binop(Sub, "-")
        simple_binop(Mul, "*")
        default:
          assert(false && "Unsupported binary operator");
      }
      
      #undef simple_binop
    } else {
      std::ostringstream message;
      message << "Unsupported instruction: " << inst->getOpcodeName();
      throw std::runtime_error(message.str());
    }
  }

public:
  LeanLowering(std::ostream& stream, llvm::Module& module): _stream(stream) {}

  void lower(llvm::Function& function) {
    for (llvm::BasicBlock& block : function) {
      _names[&block] = "b" + std::to_string(_names.size());
    }

    _stream << "mutual\n";
    for (llvm::BasicBlock& block : function) {
      _stream << "def " << _names[&block] << " :=\n";
      for (llvm::Instruction& inst : block) {
        lower_inst(_stream, &inst);
      }
    }
    _stream << "end\n";
  }
};

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

  std::ofstream out(output_filename);
  if (!out) {
    llvm::errs() << argv[0] << ": " << output_filename << ": " << "Failed to open file for writing\n";
    return 1;
  }

  LeanLowering lowering(out, *module);
  for (llvm::Function& function : *module) {
    if (!function.isDeclaration()) {
      lowering.lower(function);
    }
  }

  return 0;
}
