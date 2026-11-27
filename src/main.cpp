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
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Operator.h>
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

def Mem.memcpy (mem : Mem) (dst src : Ptr) (size : BitVec 64) : Mem :=
  mem.write dst size.toNat (fun i => mem.cell (src.1, src.2 + BitVec.ofNat 64 i))

def Mem.memset (mem : Mem) (dst : Ptr) (value : BitVec 8) (size : BitVec 64) : Mem :=
  mem.write dst size.toNat (fun _ => Sum.inl value)

def Ptr.toInt (ptr : Ptr) : BitVec 64 :=
  BitVec.ofNat 64 (ptr.1 * 2 ^ 32) + ptr.2

def Ptr.ofInt (value : BitVec 64) : Ptr :=
  ((value >>> 32).toNat, value &&& 0xFFFFFFFF)

def LLVM.ctpop (x : BitVec w) : BitVec w :=
  BitVec.ofNat w ((List.range w).countP (fun i => x.getLsbD i))

def LLVM.cttz (x : BitVec w) : BitVec w :=
  BitVec.ofNat w (((List.range w).find? (fun i => x.getLsbD i)).getD w)

def LLVM.ctlz (x : BitVec w) : BitVec w :=
  BitVec.ofNat w (((List.range w).find? (fun i => x.getMsbD i)).getD w)

def LLVM.abs (x : BitVec w) : BitVec w :=
  if x.msb then -x else x

def LLVM.uaddWithOverflow (x y : BitVec w) : BitVec w × Bool :=
  (x + y, decide (x.toNat + y.toNat ≥ 2 ^ w))

def LLVM.umulWithOverflow (x y : BitVec w) : BitVec w × Bool :=
  (x * y, decide (x.toNat * y.toNat ≥ 2 ^ w))

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

  std::vector<llvm::BasicBlock*> successors(llvm::Function& function, llvm::BasicBlock* block) {
    std::vector<llvm::BasicBlock*> result(llvm::succ_begin(block), llvm::succ_end(block));
    for (llvm::Instruction& inst : *block) {
      if (llvm::CallBase* call = llvm::dyn_cast<llvm::CallBase>(&inst)) {
        if (call->getCalledFunction() == &function) {
          result.push_back(&function.getEntryBlock());
        }
      }
    }
    return result;
  }

  bool reaches(llvm::Function& function, llvm::BasicBlock* from, llvm::BasicBlock* to) {
    std::set<llvm::BasicBlock*> visited;
    std::vector<llvm::BasicBlock*> stack = successors(function, from);
    while (!stack.empty()) {
      llvm::BasicBlock* block = stack.back();
      stack.pop_back();
      if (block == to) {
        return true;
      }
      if (visited.insert(block).second) {
        for (llvm::BasicBlock* succ : successors(function, block)) {
          stack.push_back(succ);
        }
      }
    }
    return false;
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
    } else if (type->isFloatingPointTy()) {
      stream << "(BitVec " << type->getPrimitiveSizeInBits().getFixedValue() << ")";
    } else if (llvm::StructType* struct_type = llvm::dyn_cast<llvm::StructType>(type)) {
      if (struct_type->getNumElements() == 0) {
        stream << "Unit";
        return;
      }
      stream << "(";
      for (unsigned it = 0; it < struct_type->getNumElements(); it++) {
        if (it > 0) {
          stream << " × ";
        }
        lower_type(stream, struct_type->getElementType(it));
      }
      stream << ")";
    } else {
      std::string name;
      llvm::raw_string_ostream name_stream(name);
      type->print(name_stream);
      throw std::runtime_error("Unsupported type: " + name);
    }
  }

  static std::string lean_name(const std::string& name) {
    bool is_simple = !name.empty() && std::isalpha(name[0]) && std::all_of(name.begin(), name.end(), [](char chr) {
      return std::isalnum(chr) || chr == '_';
    });
    if (is_simple) {
      return name;
    }
    return "«" + name + "»";
  }

  static std::string global_name(llvm::GlobalValue* global) {
    return lean_name("@" + global->getName().str());
  }

  std::string value_string(llvm::Value* value) {
    std::ostringstream stream;
    lower_value(stream, value);
    return stream.str();
  }

  std::string atom_string(llvm::Value* value) {
    if (_names.find(value) != _names.end()) {
      return _names[value];
    }
    return "(" + value_string(value) + ")";
  }

  std::string extract_string(const std::string& aggregate, llvm::Type* type, unsigned index) {
    llvm::StructType* struct_type = llvm::dyn_cast<llvm::StructType>(type);
    if (!struct_type) {
      throw std::runtime_error("Unsupported aggregate type");
    }
    unsigned count = struct_type->getNumElements();
    if (count == 1) {
      return aggregate;
    }
    std::string result = aggregate;
    for (unsigned it = 0; it < index; it++) {
      result += ".2";
    }
    if (index + 1 < count) {
      result += ".1";
    }
    return result;
  }

  std::string insert_string(const std::string& aggregate, llvm::Type* type, llvm::ArrayRef<unsigned> indices, const std::string& value) {
    if (indices.empty()) {
      return value;
    }
    llvm::StructType* struct_type = llvm::dyn_cast<llvm::StructType>(type);
    if (!struct_type) {
      throw std::runtime_error("Unsupported aggregate type");
    }
    if (struct_type->getNumElements() == 1) {
      return insert_string(aggregate, struct_type->getElementType(0), indices.drop_front(), value);
    }
    std::string result = "(";
    for (unsigned it = 0; it < struct_type->getNumElements(); it++) {
      if (it > 0) {
        result += ", ";
      }
      std::string field = extract_string(aggregate, type, it);
      if (it == indices[0]) {
        result += insert_string("(" + field + ")", struct_type->getElementType(it), indices.drop_front(), value);
      } else {
        result += field;
      }
    }
    return result + ")";
  }

  void lower_bool_as_bitvec(std::ostream& stream, llvm::Value* value) {
    if (value->getType()->isIntegerTy(1)) {
      stream << "(BitVec.ofBool ";
      lower_value(stream, value);
      stream << ")";
    } else {
      lower_value(stream, value);
    }
  }

  void lower_cast(std::ostream& stream, unsigned opcode, llvm::Value* operand, llvm::Type* type) {
    switch (opcode) {
      case llvm::Instruction::Trunc:
        if (type->isIntegerTy(1)) {
          stream << "(BitVec.getLsbD ";
          lower_value(stream, operand);
          stream << " 0)";
        } else {
          stream << "(BitVec.setWidth " << type->getIntegerBitWidth() << " ";
          lower_value(stream, operand);
          stream << ")";
        }
        break;
      case llvm::Instruction::ZExt:
        stream << "(BitVec.setWidth " << type->getIntegerBitWidth() << " ";
        lower_bool_as_bitvec(stream, operand);
        stream << ")";
        break;
      case llvm::Instruction::SExt:
        stream << "(BitVec.signExtend " << type->getIntegerBitWidth() << " ";
        lower_bool_as_bitvec(stream, operand);
        stream << ")";
        break;
      case llvm::Instruction::PtrToInt:
        stream << "(BitVec.setWidth " << type->getIntegerBitWidth() << " (Ptr.toInt ";
        lower_value(stream, operand);
        stream << "))";
        break;
      case llvm::Instruction::IntToPtr:
        stream << "(Ptr.ofInt (BitVec.setWidth 64 ";
        lower_value(stream, operand);
        stream << "))";
        break;
      case llvm::Instruction::BitCast:
        if (operand->getType() != type) {
          throw std::runtime_error("Unsupported bitcast");
        }
        lower_value(stream, operand);
        break;
      default:
        throw std::runtime_error(std::string("Unsupported cast: ") + llvm::Instruction::getOpcodeName(opcode));
    }
  }

  void lower_gep(std::ostream& stream, llvm::GEPOperator* gep) {
    std::string base = atom_string(gep->getPointerOperand());
    stream << "(" << base << ".1, " << base << ".2";
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
  }

  void lower_return_type(std::ostream& stream, llvm::Type* type) {
    if (type->isVoidTy()) {
      stream << "(Option Mem)";
    } else {
      stream << "(Option (Mem × ";
      lower_type(stream, type);
      stream << "))";
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
    } else if (llvm::isa<llvm::UndefValue>(value) || llvm::isa<llvm::ConstantAggregateZero>(value)) {
      stream << "(default : ";
      lower_type(stream, value->getType());
      stream << ")";
    } else if (llvm::ConstantFP* constant_fp = llvm::dyn_cast<llvm::ConstantFP>(value)) {
      llvm::SmallVector<char, 32> str;
      constant_fp->getValueAPF().bitcastToAPInt().toStringUnsigned(str, 10);
      stream << "(" << std::string(str.data(), str.size()) << " : ";
      lower_type(stream, constant_fp->getType());
      stream << ")";
    } else if (llvm::GlobalValue* global = llvm::dyn_cast<llvm::GlobalValue>(value)) {
      stream << global_name(global);
    } else if (llvm::ConstantStruct* constant_struct = llvm::dyn_cast<llvm::ConstantStruct>(value)) {
      stream << "(";
      for (unsigned it = 0; it < constant_struct->getNumOperands(); it++) {
        if (it > 0) {
          stream << ", ";
        }
        lower_value(stream, constant_struct->getOperand(it));
      }
      stream << ")";
    } else if (llvm::GEPOperator* gep = llvm::dyn_cast<llvm::GEPOperator>(value)) {
      lower_gep(stream, gep);
    } else if (llvm::ConstantExpr* expr = llvm::dyn_cast<llvm::ConstantExpr>(value); expr && expr->isCast()) {
      lower_cast(stream, expr->getOpcode(), expr->getOperand(0), expr->getType());
    } else {
      std::string name;
      llvm::raw_string_ostream name_stream(name);
      value->print(name_stream);
      throw std::runtime_error("Unsupported value: " + name);
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

  static bool is_noop(llvm::Instruction* inst) {
    if (llvm::isa<llvm::PHINode>(inst)) {
      return true;
    }
    if (llvm::IntrinsicInst* intrinsic = llvm::dyn_cast<llvm::IntrinsicInst>(inst)) {
      switch (intrinsic->getIntrinsicID()) {
        case llvm::Intrinsic::lifetime_start:
        case llvm::Intrinsic::lifetime_end:
        case llvm::Intrinsic::assume:
        case llvm::Intrinsic::experimental_noalias_scope_decl:
          return true;
        default:
          return false;
      }
    }
    return false;
  }

  void lower_intrinsic(std::ostream& stream, llvm::IntrinsicInst* call) {
    std::string name = _names.count(call) ? _names[call] : "";
    switch (call->getIntrinsicID()) {
      case llvm::Intrinsic::memcpy:
      case llvm::Intrinsic::memmove:
        stream << "let mem := (Mem.memcpy mem ";
        lower_value(stream, call->getArgOperand(0));
        stream << " ";
        lower_value(stream, call->getArgOperand(1));
        stream << " ";
        lower_value(stream, call->getArgOperand(2));
        stream << ")";
        break;
      case llvm::Intrinsic::memset:
        stream << "let mem := (Mem.memset mem ";
        lower_value(stream, call->getArgOperand(0));
        stream << " ";
        lower_value(stream, call->getArgOperand(1));
        stream << " ";
        lower_value(stream, call->getArgOperand(2));
        stream << ")";
        break;
      case llvm::Intrinsic::invariant_start:
        stream << "let " << name << " := Ptr.null";
        break;
      case llvm::Intrinsic::trap:
        stream << "let _ ← (none : Option Unit)";
        break;
      case llvm::Intrinsic::umin:
      case llvm::Intrinsic::umax:
      case llvm::Intrinsic::smin:
      case llvm::Intrinsic::smax: {
        llvm::Intrinsic::ID id = call->getIntrinsicID();
        bool is_min = id == llvm::Intrinsic::umin || id == llvm::Intrinsic::smin;
        bool is_signed = id == llvm::Intrinsic::smin || id == llvm::Intrinsic::smax;
        std::string a = value_string(call->getArgOperand(0));
        std::string b = value_string(call->getArgOperand(1));
        stream << "let " << name << " := (if " << (is_signed ? "BitVec.slt " : "BitVec.ult ") << a << " " << b;
        stream << " then " << (is_min ? a : b) << " else " << (is_min ? b : a) << ")";
        break;
      }
      #define unary_intrinsic(ID, function) \
        case llvm::Intrinsic::ID: \
          stream << "let " << name << " := (" function " "; \
          lower_value(stream, call->getArgOperand(0)); \
          stream << ")"; \
          break;
      unary_intrinsic(ctpop, "LLVM.ctpop")
      unary_intrinsic(cttz, "LLVM.cttz")
      unary_intrinsic(ctlz, "LLVM.ctlz")
      unary_intrinsic(abs, "LLVM.abs")
      #undef unary_intrinsic
      #define binary_intrinsic(ID, function) \
        case llvm::Intrinsic::ID: \
          stream << "let " << name << " := (" function " "; \
          lower_value(stream, call->getArgOperand(0)); \
          stream << " "; \
          lower_value(stream, call->getArgOperand(1)); \
          stream << ")"; \
          break;
      binary_intrinsic(uadd_with_overflow, "LLVM.uaddWithOverflow")
      binary_intrinsic(umul_with_overflow, "LLVM.umulWithOverflow")
      #undef binary_intrinsic
      default:
        throw std::runtime_error("Unsupported intrinsic: " + call->getCalledFunction()->getName().str());
    }
  }

  void lower_call(std::ostream& stream, llvm::CallBase* call) {
    llvm::Function* callee = call->getCalledFunction();
    if (llvm::IntrinsicInst* intrinsic = llvm::dyn_cast<llvm::IntrinsicInst>(call)) {
      lower_intrinsic(stream, intrinsic);
      return;
    }
    if (callee && callee->isDeclaration() && callee->getName() == "malloc") {
      stream << "let (mem, " << _names[call] << ") := (Mem.malloc mem ";
      lower_value(stream, call->getArgOperand(0));
      stream << ")";
      return;
    }
    if (callee && callee->isDeclaration() && callee->getName() == "free") {
      stream << "let mem := (Mem.free mem ";
      lower_value(stream, call->getArgOperand(0));
      stream << ")";
      return;
    }
    if (call->getType()->isVoidTy()) {
      stream << "let mem ← (";
    } else {
      stream << "let (mem, " << _names[call] << ") ← (";
    }
    if (callee) {
      stream << lean_name(callee->getName().str()) << " mem";
    } else {
      stream << "callIndirect mem ";
      lower_value(stream, call->getCalledOperand());
    }
    for (llvm::Value* arg : call->args()) {
      stream << " ";
      lower_value(stream, arg);
    }
    stream << ")";
  }

  void lower_inst(std::ostream& stream, llvm::Instruction* inst) {
    if (is_noop(inst)) {
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

      #define shift_binop(Kind, function) \
        case llvm::Instruction::Kind: \
          if (is_bool) { \
            throw std::runtime_error("Unsupported boolean binary operator"); \
          } \
          stream << "(" function " "; \
          lower_value(stream, binop->getOperand(0)); \
          stream << " (BitVec.toNat "; \
          lower_value(stream, binop->getOperand(1)); \
          stream << "))"; \
          break;

      switch (binop->getOpcode()) {
        simple_binop(Add, "+", "^^")
        simple_binop(Sub, "-", "^^")
        simple_binop(Mul, "*", "&&")
        simple_binop(And, "&&&", "&&")
        simple_binop(Or, "|||", "||")
        simple_binop(Xor, "^^^", "^^")
        function_binop(UDiv, "BitVec.udiv")
        function_binop(SDiv, "BitVec.sdiv")
        function_binop(URem, "BitVec.umod")
        function_binop(SRem, "BitVec.srem")
        shift_binop(Shl, "BitVec.shiftLeft")
        shift_binop(LShr, "BitVec.ushiftRight")
        shift_binop(AShr, "BitVec.sshiftRight")
        default:
          throw std::runtime_error(std::string("Unsupported binary operator: ") + binop->getOpcodeName());
      }

      #undef simple_binop
      #undef function_binop
      #undef shift_binop
    } else if (llvm::ICmpInst* icmp = llvm::dyn_cast<llvm::ICmpInst>(inst)) {
      stream << "let " << _names[inst] << " := ";

      std::string lhs = value_string(icmp->getOperand(0));
      std::string rhs = value_string(icmp->getOperand(1));
      if (icmp->isRelational()) {
        if (icmp->getOperand(0)->getType()->isPointerTy()) {
          lhs = "(Ptr.toInt " + lhs + ")";
          rhs = "(Ptr.toInt " + rhs + ")";
        } else if (icmp->getOperand(0)->getType()->isIntegerTy(1)) {
          lhs = "(BitVec.ofBool " + lhs + ")";
          rhs = "(BitVec.ofBool " + rhs + ")";
        }
      }

      #define simple_icmp(Pred, op, swap) \
        case llvm::CmpInst::Pred: \
          stream << "(" op " " << (swap ? rhs : lhs) << " " << (swap ? lhs : rhs) << ")"; \
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
          throw std::runtime_error("Unsupported icmp predicate");
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
    } else if (llvm::SwitchInst* sw = llvm::dyn_cast<llvm::SwitchInst>(inst)) {
      for (llvm::SwitchInst::CaseHandle handle : sw->cases()) {
        stream << "if (BEq.beq ";
        lower_value(stream, sw->getCondition());
        stream << " ";
        lower_value(stream, handle.getCaseValue());
        stream << ") then ";
        lower_block_call(stream, sw->getParent(), handle.getCaseSuccessor());
        stream << " else ";
      }
      lower_block_call(stream, sw->getParent(), sw->getDefaultDest());
    } else if (llvm::isa<llvm::UnreachableInst>(inst) || llvm::isa<llvm::ResumeInst>(inst)) {
      stream << "none";
    } else if (llvm::isa<llvm::LandingPadInst>(inst)) {
      stream << "let " << _names[inst] << " := (default : ";
      lower_type(stream, inst->getType());
      stream << ")";
    } else if (llvm::SelectInst* select = llvm::dyn_cast<llvm::SelectInst>(inst)) {
      stream << "let " << _names[inst] << " := (if ";
      lower_value(stream, select->getCondition());
      stream << " then ";
      lower_value(stream, select->getTrueValue());
      stream << " else ";
      lower_value(stream, select->getFalseValue());
      stream << ")";
    } else if (llvm::CastInst* cast = llvm::dyn_cast<llvm::CastInst>(inst)) {
      stream << "let " << _names[inst] << " := ";
      lower_cast(stream, cast->getOpcode(), cast->getOperand(0), cast->getType());
    } else if (llvm::ExtractValueInst* extract = llvm::dyn_cast<llvm::ExtractValueInst>(inst)) {
      std::string result = atom_string(extract->getAggregateOperand());
      llvm::Type* type = extract->getAggregateOperand()->getType();
      for (unsigned index : extract->indices()) {
        result = "(" + extract_string(result, type, index) + ")";
        type = llvm::cast<llvm::StructType>(type)->getElementType(index);
      }
      stream << "let " << _names[inst] << " := " << result;
    } else if (llvm::InsertValueInst* insert = llvm::dyn_cast<llvm::InsertValueInst>(inst)) {
      stream << "let " << _names[inst] << " := ";
      stream << insert_string(atom_string(insert->getAggregateOperand()), insert->getType(), insert->getIndices(), value_string(insert->getInsertedValueOperand()));
    } else if (llvm::AllocaInst* alloca = llvm::dyn_cast<llvm::AllocaInst>(inst)) {
      stream << "let (mem, " << _names[inst] << ") := (Mem.malloc mem ((" << _data_layout.getTypeAllocSize(alloca->getAllocatedType()).getFixedValue() << " : (BitVec 64))";
      if (alloca->isArrayAllocation()) {
        stream << " * (BitVec.setWidth 64 ";
        lower_value(stream, alloca->getArraySize());
        stream << ")";
      }
      stream << "))";
    } else if (llvm::LoadInst* load = llvm::dyn_cast<llvm::LoadInst>(inst)) {
      llvm::Type* type = load->getType();
      if (type->isPointerTy()) {
        stream << "let " << _names[inst] << " := (Mem.loadPtr mem ";
        lower_value(stream, load->getPointerOperand());
        stream << ")\n";
        return;
      }
      if (!type->isIntegerTy() && !type->isFloatingPointTy()) {
        throw std::runtime_error("Unsupported load type");
      }
      stream << "let " << _names[inst] << " := (Mem.load mem ";
      lower_value(stream, load->getPointerOperand());
      stream << " " << type->getPrimitiveSizeInBits().getFixedValue() << ")";
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
      if (!value->getType()->isIntegerTy() && !value->getType()->isFloatingPointTy()) {
        throw std::runtime_error("Unsupported store type");
      }
      stream << "let mem := (Mem.store mem ";
      lower_value(stream, store->getPointerOperand());
      stream << " ";
      lower_bool_as_bitvec(stream, value);
      stream << ")";
    } else if (llvm::GetElementPtrInst* gep = llvm::dyn_cast<llvm::GetElementPtrInst>(inst)) {
      stream << "let " << _names[inst] << " := ";
      lower_gep(stream, llvm::cast<llvm::GEPOperator>(gep));
    } else if (llvm::CallBase* call = llvm::dyn_cast<llvm::CallBase>(inst)) {
      lower_call(stream, call);
      if (llvm::InvokeInst* invoke = llvm::dyn_cast<llvm::InvokeInst>(call)) {
        stream << "\n    ";
        lower_block_call(stream, invoke->getParent(), invoke->getNormalDest());
      }
    } else if (llvm::ReturnInst* ret = llvm::dyn_cast<llvm::ReturnInst>(inst)) {
      if (llvm::Value* value = ret->getReturnValue()) {
        stream << "pure (mem, ";
        lower_value(stream, value);
        stream << ")";
      } else {
        stream << "pure mem";
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
    for (llvm::GlobalVariable& global : module.globals()) {
      _stream << "opaque " << global_name(&global) << " : Ptr\n";
    }
    for (llvm::Function& function : module) {
      if (!function.isIntrinsic() && function.hasAddressTaken()) {
        _stream << "opaque " << global_name(&function) << " : Ptr\n";
      }
    }
    _stream << "\n";
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

    bool is_recursive = false;
    for (llvm::Instruction& inst : llvm::instructions(function)) {
      if (llvm::CallBase* call = llvm::dyn_cast<llvm::CallBase>(&inst)) {
        is_recursive = is_recursive || call->getCalledFunction() == &function;
      }
    }

    _stream << "def " << lean_name(function.getName().str()) << " (mem : Mem)";
    for (llvm::Argument& arg : function.args()) {
      _stream << " (" << _names[&arg] << " : ";
      lower_type(_stream, arg.getType());
      _stream << ")";
    }
    _stream << " : ";
    lower_return_type(_stream, function.getReturnType());
    _stream << " :=\n";
    _stream << "  " << _names[&function.getEntryBlock()] << " mem\n";
    if (is_recursive) {
      _stream << "partial_fixpoint\n";
    }
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
      _stream << " := do\n";
      for (llvm::Instruction& inst : block) {
        lower_inst(_stream, &inst);
      }
      if (reaches(function, &block, &block)) {
        _stream << "  partial_fixpoint\n";
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
