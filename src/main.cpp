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

#include <algorithm>
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
#include <llvm/IR/InstIterator.h>
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
  std::unordered_map<llvm::BasicBlock*, std::vector<llvm::Instruction*>> _live_in;

  void compute_live_in(llvm::Function& function) {
    std::unordered_map<llvm::Instruction*, size_t> order;
    std::unordered_map<llvm::BasicBlock*, std::set<llvm::Instruction*>> live_in;
    for (llvm::BasicBlock& block : function) {
      for (llvm::Instruction& inst : block) {
        order[&inst] = order.size();
      }
    }

    bool changed = true;
    while (changed) {
      changed = false;
      for (llvm::BasicBlock& block : llvm::reverse(function)) {
        std::set<llvm::Instruction*> live;
        for (llvm::BasicBlock* succ : llvm::successors(&block)) {
          for (llvm::Instruction* inst : live_in[succ]) {
            live.insert(inst);
          }
          for (llvm::PHINode& phi : succ->phis()) {
            if (llvm::Instruction* incoming = llvm::dyn_cast<llvm::Instruction>(phi.getIncomingValueForBlock(&block))) {
              live.insert(incoming);
            }
          }
        }

        for (llvm::Instruction& inst : llvm::reverse(block)) {
          live.erase(&inst);
          if (llvm::isa<llvm::PHINode>(inst)) {
            continue;
          }
          for (llvm::Value* operand : inst.operands()) {
            if (llvm::Instruction* operand_inst = llvm::dyn_cast<llvm::Instruction>(operand)) {
              live.insert(operand_inst);
            }
          }
        }

        if (live != live_in[&block]) {
          live_in[&block] = live;
          changed = true;
        }
      }
    }

    for (llvm::BasicBlock& block : function) {
      std::vector<llvm::Instruction*>& sorted = _live_in[&block];
      sorted.assign(live_in[&block].begin(), live_in[&block].end());
      std::sort(sorted.begin(), sorted.end(), [&](llvm::Instruction* a, llvm::Instruction* b) {
        return order[a] < order[b];
      });
    }
  }

  void lower_type(std::ostream& stream, llvm::Type* type) {
    if (type->isIntegerTy(1)) {
      stream << "Bool";
    } else if (llvm::IntegerType* integer_type = llvm::dyn_cast<llvm::IntegerType>(type)) {
      stream << "(BitVec " << integer_type->getBitWidth() << ")";
    } else if (type->isVoidTy()) {
      stream << "Unit";
    } else {
      assert(false && "Unsupported type");
    }
  }

  void lower_value(std::ostream& stream, llvm::Value* value) {
    if (_names.find(value) != _names.end()) {
      stream << _names[value];
    } else if (value->getType()->isIntegerTy(1) && llvm::isa<llvm::ConstantInt>(value)) {
      stream << (llvm::cast<llvm::ConstantInt>(value)->isOne() ? "true" : "false");
    } else if (llvm::ConstantInt* constant_int = llvm::dyn_cast<llvm::ConstantInt>(value)) {
      stream << "(";
      llvm::SmallVector<char, 32> str;
      constant_int->getValue().toStringUnsigned(str, 10);
      stream << std::string(str.data(), str.size());
      stream << " : ";
      lower_type(stream, constant_int->getType());
      stream << ")";
    } else {
      assert(false && "Unsupported value");
    }
  }

  void lower_block_call(std::ostream& stream, llvm::BasicBlock* from, llvm::BasicBlock* to) {
    stream << "(" << _names[to];
    for (llvm::PHINode& phi : to->phis()) {
      stream << " ";
      lower_value(stream, phi.getIncomingValueForBlock(from));
    }
    for (llvm::Instruction* inst : _live_in[to]) {
      stream << " " << _names[inst];
    }
    stream << ")";
  }

  void lower_inst(std::ostream& stream, llvm::Instruction* inst) {
    if (llvm::isa<llvm::PHINode>(inst)) {
      return;
    }

    stream << "    ";
    if (llvm::BinaryOperator* binop = llvm::dyn_cast<llvm::BinaryOperator>(inst)) {
      stream << "let " << _names[inst] << " := ";

      bool is_bool = binop->getType()->isIntegerTy(1);

      #define simple_binop(Kind, op, bool_op) \
        case llvm::Instruction::Kind: \
          stream << "("; \
          lower_value(stream, binop->getOperand(0)); \
          stream << " " << (is_bool ? bool_op : op) << " "; \
          lower_value(stream, binop->getOperand(1)); \
          stream << ")"; \
          break;
      
      switch (binop->getOpcode()) {
        simple_binop(Add, "+", "^^")
        simple_binop(Sub, "-", "^^")
        simple_binop(Mul, "*", "&&")
        default:
          assert(false && "Unsupported binary operator");
      }
      
      #undef simple_binop
    } else if (llvm::ICmpInst* icmp = llvm::dyn_cast<llvm::ICmpInst>(inst)) {
      stream << "let " << _names[inst] << " := ";

      #define simple_icmp(Pred, op, swap) \
        case llvm::CmpInst::Pred: \
          stream << "(" op " "; \
          lower_value(stream, icmp->getOperand(swap ? 1 : 0)); \
          stream << " "; \
          lower_value(stream, icmp->getOperand(swap ? 0 : 1)); \
          stream << ")"; \
          break;

      switch (icmp->getPredicate()) {
        simple_icmp(ICMP_EQ, "BEq.beq", false)
        simple_icmp(ICMP_NE, "bne", false)
        simple_icmp(ICMP_ULT, "BitVec.ult", false)
        simple_icmp(ICMP_ULE, "BitVec.ule", false)
        simple_icmp(ICMP_UGT, "BitVec.ult", true)
        simple_icmp(ICMP_UGE, "BitVec.ule", true)
        simple_icmp(ICMP_SLT, "BitVec.slt", false)
        simple_icmp(ICMP_SLE, "BitVec.sle", false)
        simple_icmp(ICMP_SGT, "BitVec.slt", true)
        simple_icmp(ICMP_SGE, "BitVec.sle", true)
        default:
          assert(false && "Unsupported icmp predicate");
      }

      #undef simple_icmp
    } else if (llvm::BranchInst* br = llvm::dyn_cast<llvm::BranchInst>(inst)) {
      if (br->isConditional()) {
        stream << "if ";
        lower_value(stream, br->getCondition());
        stream << " then ";
        lower_block_call(stream, br->getParent(), br->getSuccessor(0));
        stream << " else ";
        lower_block_call(stream, br->getParent(), br->getSuccessor(1));
      } else {
        lower_block_call(stream, br->getParent(), br->getSuccessor(0));
      }
    } else if (llvm::ReturnInst* ret = llvm::dyn_cast<llvm::ReturnInst>(inst)) {
      if (llvm::Value* value = ret->getReturnValue()) {
        lower_value(stream, value);
      } else {
        stream << "()";
      }
    } else {
      std::ostringstream message;
      message << "Unsupported instruction: " << inst->getOpcodeName();
      throw std::runtime_error(message.str());
    }
    stream << "\n";
  }

public:
  LeanLowering(std::ostream& stream, llvm::Module& module): _stream(stream) {}

  void lower(llvm::Function& function) {
    for (llvm::BasicBlock& block : function) {
      _names[&block] = "b" + std::to_string(_names.size());
    }

    for (llvm::Argument& arg : function.args()) {
      _names[&arg] = "a" + std::to_string(_names.size());
    }

    for (llvm::Instruction& inst : llvm::instructions(function)) {
      if (!inst.getType()->isVoidTy()) {
        _names[&inst] = "v" + std::to_string(_names.size());
      }
    }

    compute_live_in(function);

    _stream << "partial def " << function.getName().str();
    for (llvm::Argument& arg : function.args()) {
      _stream << " (" << _names[&arg] << " : ";
      lower_type(_stream, arg.getType());
      _stream << ")";
    }
    _stream << " : ";
    lower_type(_stream, function.getReturnType());
    _stream << " :=\n";
    _stream << "  " << _names[&function.getEntryBlock()] << "\n";
    _stream << "where\n";
    for (llvm::BasicBlock& block : function) {
      _stream << "  " << _names[&block];
      for (llvm::PHINode& phi : block.phis()) {
        _stream << " (" << _names[&phi] << " : ";
        lower_type(_stream, phi.getType());
        _stream << ")";
      }
      for (llvm::Instruction* inst : _live_in[&block]) {
        _stream << " (" << _names[inst] << " : ";
        lower_type(_stream, inst->getType());
        _stream << ")";
      }
      _stream << " : ";
      lower_type(_stream, function.getReturnType());
      _stream << " :=\n";
      for (llvm::Instruction& inst : block) {
        lower_inst(_stream, &inst);
      }
    }
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
