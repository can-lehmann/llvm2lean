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
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/GetElementPtrTypeIterator.h>
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

static const char* lean_prelude = R"(abbrev Ptr := Nat × BitVec 64

def Ptr.null : Ptr := (0, 0)

structure Mem where
  regions : Nat → Unit ⊕ (BitVec 64 → BitVec 8 ⊕ Ptr)
  next : Nat

instance : Inhabited Mem := ⟨⟨fun _ => Sum.inl (), 1⟩⟩

def Mem.cell (mem : Mem) (ptr : Ptr) : BitVec 8 ⊕ Ptr :=
  (mem.regions ptr.1).elim (fun _ => Sum.inl 0) (fun region => region ptr.2)

def Mem.write (mem : Mem) (ptr : Ptr) (size : Nat) (cell : Nat → BitVec 8 ⊕ Ptr) : Mem :=
  { mem with regions := fun id =>
    if id = ptr.1 then
      (mem.regions id).map (fun u => u) (fun region offset => if (offset - ptr.2).toNat < size then cell (offset - ptr.2).toNat else region offset)
    else
      mem.regions id }

def Mem.load (mem : Mem) (ptr : Ptr) (w : Nat) : BitVec w :=
  BitVec.ofNat w ((List.range ((w + 7) / 8)).foldr (fun i acc => ((mem.cell (ptr.1, ptr.2 + BitVec.ofNat 64 i)).elim id (fun _ => 0)).toNat + acc * 256) 0)

def Mem.store {w : Nat} (mem : Mem) (ptr : Ptr) (value : BitVec w) : Mem :=
  mem.write ptr ((w + 7) / 8) (fun i => Sum.inl (BitVec.setWidth 8 (value >>> (8 * i))))

def Mem.loadPtr (mem : Mem) (ptr : Ptr) : Ptr :=
  (mem.cell ptr).elim (fun _ => Ptr.null) id

def Mem.storePtr (mem : Mem) (ptr : Ptr) (value : Ptr) : Mem :=
  mem.write ptr 8 (fun _ => Sum.inr value)

def Mem.malloc (mem : Mem) (_size : BitVec 64) : Mem × Ptr :=
  ({ regions := fun id => if id = mem.next then Sum.inr (fun _ => Sum.inl 0) else mem.regions id, next := mem.next + 1 }, (mem.next, 0))

def Mem.free (mem : Mem) (ptr : Ptr) : Mem :=
  { mem with regions := fun id => if id = ptr.1 then Sum.inl () else mem.regions id }

)";

class LeanLowering {
private:
  std::ostream& _stream;
  const llvm::DataLayout& _data_layout;
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
    } else if (type->isPointerTy()) {
      stream << "Ptr";
    } else if (type->isVoidTy()) {
      stream << "Unit";
    } else {
      assert(false && "Unsupported type");
    }
  }

  void lower_return_type(std::ostream& stream, llvm::Type* type) {
    if (type->isVoidTy()) {
      stream << "Mem";
    } else {
      stream << "(Mem × ";
      lower_type(stream, type);
      stream << ")";
    }
  }

  void lower_index(std::ostream& stream, llvm::Value* index) {
    unsigned width = index->getType()->getIntegerBitWidth();
    if (width == 64) {
      lower_value(stream, index);
    } else {
      stream << "(BitVec.signExtend 64 ";
      lower_value(stream, index);
      stream << ")";
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
    } else if (llvm::isa<llvm::ConstantPointerNull>(value)) {
      stream << "Ptr.null";
    } else {
      assert(false && "Unsupported value");
    }
  }

  void lower_block_call(std::ostream& stream, llvm::BasicBlock* from, llvm::BasicBlock* to) {
    stream << "(" << _names[to] << " mem";
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
      
      #define function_binop(Kind, function) \
        case llvm::Instruction::Kind: \
          if (is_bool) { \
            throw std::runtime_error("Unsupported boolean binary operator"); \
          } \
          stream << "(" function " "; \
          lower_value(stream, binop->getOperand(0)); \
          stream << " "; \
          lower_value(stream, binop->getOperand(1)); \
          stream << ")"; \
          break;

      switch (binop->getOpcode()) {
        simple_binop(Add, "+", "^^")
        simple_binop(Sub, "-", "^^")
        simple_binop(Mul, "*", "&&")
        function_binop(UDiv, "BitVec.udiv")
        function_binop(SDiv, "BitVec.sdiv")
        function_binop(URem, "BitVec.umod")
        function_binop(SRem, "BitVec.srem")
        default:
          assert(false && "Unsupported binary operator");
      }

      #undef simple_binop
      #undef function_binop
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
    } else if (llvm::LoadInst* load = llvm::dyn_cast<llvm::LoadInst>(inst)) {
      llvm::Type* type = load->getType();
      if (type->isPointerTy()) {
        stream << "let " << _names[inst] << " := (Mem.loadPtr mem ";
        lower_value(stream, load->getPointerOperand());
        stream << ")\n";
        return;
      }
      if (!type->isIntegerTy()) {
        throw std::runtime_error("Unsupported load type");
      }
      stream << "let " << _names[inst] << " := (Mem.load mem ";
      lower_value(stream, load->getPointerOperand());
      stream << " " << type->getIntegerBitWidth() << ")";
      if (type->isIntegerTy(1)) {
        stream << " == 1#1";
      }
    } else if (llvm::StoreInst* store = llvm::dyn_cast<llvm::StoreInst>(inst)) {
      llvm::Value* value = store->getValueOperand();
      if (value->getType()->isPointerTy()) {
        stream << "let mem := (Mem.storePtr mem ";
        lower_value(stream, store->getPointerOperand());
        stream << " ";
        lower_value(stream, value);
        stream << ")\n";
        return;
      }
      if (!value->getType()->isIntegerTy()) {
        throw std::runtime_error("Unsupported store type");
      }
      stream << "let mem := (Mem.store mem ";
      lower_value(stream, store->getPointerOperand());
      stream << " ";
      if (value->getType()->isIntegerTy(1)) {
        stream << "(BitVec.ofBool ";
        lower_value(stream, value);
        stream << ")";
      } else {
        lower_value(stream, value);
      }
      stream << ")";
    } else if (llvm::GetElementPtrInst* gep = llvm::dyn_cast<llvm::GetElementPtrInst>(inst)) {
      stream << "let " << _names[inst] << " := (";
      lower_value(stream, gep->getPointerOperand());
      stream << ".1, ";
      lower_value(stream, gep->getPointerOperand());
      stream << ".2";
      for (llvm::gep_type_iterator it = llvm::gep_type_begin(gep); it != llvm::gep_type_end(gep); ++it) {
        if (llvm::StructType* struct_type = it.getStructTypeOrNull()) {
          unsigned field = llvm::cast<llvm::ConstantInt>(it.getOperand())->getZExtValue();
          stream << " + (" << _data_layout.getStructLayout(struct_type)->getElementOffset(field).getFixedValue() << " : (BitVec 64))";
        } else {
          stream << " + (" << it.getSequentialElementStride(_data_layout).getFixedValue() << " : (BitVec 64)) * ";
          lower_index(stream, it.getOperand());
        }
      }
      stream << ")";
    } else if (llvm::CallInst* call = llvm::dyn_cast<llvm::CallInst>(inst)) {
      llvm::Function* callee = call->getCalledFunction();
      if (callee && callee->isDeclaration() && callee->getName() == "malloc") {
        stream << "let (mem, " << _names[inst] << ") := (Mem.malloc mem ";
        lower_value(stream, call->getArgOperand(0));
        stream << ")\n";
        return;
      }
      if (callee && callee->isDeclaration() && callee->getName() == "free") {
        stream << "let mem := (Mem.free mem ";
        lower_value(stream, call->getArgOperand(0));
        stream << ")\n";
        return;
      }
      if (!callee || callee->isDeclaration()) {
        throw std::runtime_error("Unsupported call target");
      }
      if (call->getType()->isVoidTy()) {
        stream << "let mem := (";
      } else {
        stream << "let (mem, " << _names[inst] << ") := (";
      }
      stream << callee->getName().str() << " mem";
      for (llvm::Value* arg : call->args()) {
        stream << " ";
        lower_value(stream, arg);
      }
      stream << ")";
    } else if (llvm::ReturnInst* ret = llvm::dyn_cast<llvm::ReturnInst>(inst)) {
      if (llvm::Value* value = ret->getReturnValue()) {
        stream << "(mem, ";
        lower_value(stream, value);
        stream << ")";
      } else {
        stream << "mem";
      }
    } else {
      std::ostringstream message;
      message << "Unsupported instruction: " << inst->getOpcodeName();
      throw std::runtime_error(message.str());
    }
    stream << "\n";
  }

public:
  LeanLowering(std::ostream& stream, llvm::Module& module): _stream(stream), _data_layout(module.getDataLayout()) {
    _stream << lean_prelude;
  }

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

    _stream << "partial def " << function.getName().str() << " (mem : Mem)";
    for (llvm::Argument& arg : function.args()) {
      _stream << " (" << _names[&arg] << " : ";
      lower_type(_stream, arg.getType());
      _stream << ")";
    }
    _stream << " : ";
    lower_return_type(_stream, function.getReturnType());
    _stream << " :=\n";
    _stream << "  " << _names[&function.getEntryBlock()] << " mem\n";
    _stream << "where\n";
    for (llvm::BasicBlock& block : function) {
      _stream << "  " << _names[&block] << " (mem : Mem)";
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
      lower_return_type(_stream, function.getReturnType());
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
