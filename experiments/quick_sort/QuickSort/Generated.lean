abbrev Ptr := Nat × BitVec 64

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

def quick_sort (mem : Mem) (a11 : Ptr) (a12 : (BitVec 64)) (a13 : (BitVec 64)) : (Option Mem) :=
  b0 mem
partial_fixpoint
where
  b0 (mem : Mem) : (Option Mem) := do
    let v14 := (BitVec.sle a13 a12)
    if v14 then (b1 mem) else (b2 mem)
  partial_fixpoint
  b1 (mem : Mem) : (Option Mem) := do
    (b10 mem)
  b2 (mem : Mem) : (Option Mem) := do
    let v15 := (a11.1, a11.2 + (4 : (BitVec 64)) * a13)
    let v16 := (Mem.load mem v15 32)
    (b3 mem a12 a12 v16)
  partial_fixpoint
  b3 (mem : Mem) (v17 : (BitVec 64)) (v18 : (BitVec 64)) (v16 : (BitVec 32)) : (Option Mem) := do
    let v19 := (BitVec.slt v18 a13)
    if v19 then (b5 mem v16 v17 v18) else (b4 mem v17)
  partial_fixpoint
  b4 (mem : Mem) (v17 : (BitVec 64)) : (Option Mem) := do
    (b9 mem v17)
  partial_fixpoint
  b5 (mem : Mem) (v16 : (BitVec 32)) (v17 : (BitVec 64)) (v18 : (BitVec 64)) : (Option Mem) := do
    let v20 := (a11.1, a11.2 + (4 : (BitVec 64)) * v18)
    let v21 := (Mem.load mem v20 32)
    let v22 := (BitVec.slt v21 v16)
    if v22 then (b6 mem v16 v17 v18) else (b7 mem v17 v16 v18)
  partial_fixpoint
  b6 (mem : Mem) (v16 : (BitVec 32)) (v17 : (BitVec 64)) (v18 : (BitVec 64)) : (Option Mem) := do
    let v23 := (a11.1, a11.2 + (4 : (BitVec 64)) * v17)
    let v24 := (Mem.load mem v23 32)
    let v25 := (a11.1, a11.2 + (4 : (BitVec 64)) * v18)
    let v26 := (Mem.load mem v25 32)
    let v27 := (a11.1, a11.2 + (4 : (BitVec 64)) * v17)
    let mem := (Mem.store mem v27 v26)
    let v28 := (a11.1, a11.2 + (4 : (BitVec 64)) * v18)
    let mem := (Mem.store mem v28 v24)
    let v29 := (v17 + (1 : (BitVec 64)))
    (b7 mem v29 v16 v18)
  partial_fixpoint
  b7 (mem : Mem) (v30 : (BitVec 64)) (v16 : (BitVec 32)) (v18 : (BitVec 64)) : (Option Mem) := do
    (b8 mem v16 v18 v30)
  partial_fixpoint
  b8 (mem : Mem) (v16 : (BitVec 32)) (v18 : (BitVec 64)) (v30 : (BitVec 64)) : (Option Mem) := do
    let v31 := (v18 + (1 : (BitVec 64)))
    (b3 mem v30 v31 v16)
  partial_fixpoint
  b9 (mem : Mem) (v17 : (BitVec 64)) : (Option Mem) := do
    let v32 := (a11.1, a11.2 + (4 : (BitVec 64)) * v17)
    let v33 := (Mem.load mem v32 32)
    let v34 := (a11.1, a11.2 + (4 : (BitVec 64)) * a13)
    let v35 := (Mem.load mem v34 32)
    let v36 := (a11.1, a11.2 + (4 : (BitVec 64)) * v17)
    let mem := (Mem.store mem v36 v35)
    let v37 := (a11.1, a11.2 + (4 : (BitVec 64)) * a13)
    let mem := (Mem.store mem v37 v33)
    let v38 := (v17 - (1 : (BitVec 64)))
    let mem ← (quick_sort mem a11 a12 v38)
    let v39 := (v17 + (1 : (BitVec 64)))
    let mem ← (quick_sort mem a11 v39 a13)
    (b10 mem)
  partial_fixpoint
  b10 (mem : Mem) : (Option Mem) := do
    pure mem
