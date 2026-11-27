import QuickSort.Generated

theorem Mem.cell_store (mem : Mem) (p q : Ptr) (v : BitVec 32) (r : BitVec 64 → BitVec 8 ⊕ Ptr)
    (h : mem.regions q.1 = .inr r) :
    (mem.store q v).cell p =
      if p.1 = q.1 ∧ (p.2 - q.2).toNat < 4 then .inl (BitVec.setWidth 8 (v >>> (8 * (p.2 - q.2).toNat)))
      else mem.cell p := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  simp only at h ⊢
  by_cases e : p1 = q1
  · subst e
    simp [Mem.cell, Mem.store, Mem.write, h]
  · simp [Mem.cell, Mem.store, Mem.write, e]

theorem Mem.load_congr (mem mem' : Mem) (p : Ptr)
    (h : ∀ i < 4, mem.cell (p.1, p.2 + BitVec.ofNat 64 i) = mem'.cell (p.1, p.2 + BitVec.ofNat 64 i)) :
    mem.load p 32 = mem'.load p 32 := by
  simp only [Mem.load, show List.range ((32 + 7) / 8) = [0, 1, 2, 3] from rfl, List.foldr]
  rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]

theorem Mem.load_store_same (mem : Mem) (p : Ptr) (v : BitVec 32) (r : BitVec 64 → BitVec 8 ⊕ Ptr)
    (h : mem.regions p.1 = .inr r) : (mem.store p v).load p 32 = v := by
  simp only [Mem.load, show List.range ((32 + 7) / 8) = [0, 1, 2, 3] from rfl, List.foldr]
  have hs : ∀ y : BitVec 64, p.2 + y - p.2 = y := fun y => by bv_omega
  simp only [Mem.cell_store mem _ p v r h, hs]
  simp
  apply BitVec.eq_of_toNat_eq
  simp
  omega

theorem Mem.load_store_ne (mem : Mem) (p q : Ptr) (v : BitVec 32) (r : BitVec 64 → BitVec 8 ⊕ Ptr)
    (h : mem.regions q.1 = .inr r)
    (hne : ∀ i < 4, ¬ (p.1 = q.1 ∧ (p.2 + BitVec.ofNat 64 i - q.2).toNat < 4)) :
    (mem.store q v).load p 32 = mem.load p 32 := by
  apply Mem.load_congr
  intro i hi
  rw [Mem.cell_store mem _ q v r h, ite_eq_right_of_eq_false _ _ (eq_false (hne i hi))]

theorem Mem.regions_store_ne (mem : Mem) (q : Ptr) (v : BitVec 32) (id : Nat) (h : id ≠ q.1) :
    (mem.store q v).regions id = mem.regions id := by
  simp [Mem.store, Mem.write, h]

theorem Mem.regions_store_alloc (mem : Mem) (q : Ptr) (v : BitVec 32) (r : BitVec 64 → BitVec 8 ⊕ Ptr)
    (h : mem.regions q.1 = .inr r) : ∃ r', (mem.store q v).regions q.1 = .inr r' := by
  simp [Mem.store, Mem.write, h]

theorem Mem.next_store (mem : Mem) (q : Ptr) (v : BitVec 32) : (mem.store q v).next = mem.next := rfl

def Mem.view (mem : Mem) (a : Ptr) : Int → Int :=
  fun k => if 0 ≤ k ∧ k < 2 ^ 62 then (mem.load (a.1, a.2 + 4 * BitVec.ofInt 64 k) 32).toInt else 0

def Small (x : BitVec 64) : Prop := 0 ≤ x.toInt ∧ x.toInt < 2 ^ 62

theorem Small.toNat {x : BitVec 64} (h : Small x) : x.toNat < 2 ^ 62 ∧ x.toInt = x.toNat := by
  simp only [Small, BitVec.toInt_eq_toNat_cond] at *
  split at * <;> omega

theorem Mem.load_view (mem : Mem) (a : Ptr) (x : BitVec 64) (hx : Small x) :
    (mem.load (a.1, a.2 + 4 * x) 32).toInt = mem.view a x.toInt := by
  simp only [Mem.view, ite_eq_left (And.intro hx.1 hx.2), BitVec.ofInt_toInt]

theorem Mem.view_store (mem : Mem) (a : Ptr) (x : BitVec 64) (v : BitVec 32)
    (r : BitVec 64 → BitVec 8 ⊕ Ptr) (h : mem.regions a.1 = .inr r) (hx : Small x) :
    (mem.store (a.1, a.2 + 4 * x) v).view a = fun k => if k = x.toInt then v.toInt else mem.view a k := by
  funext k
  obtain ⟨hx₁, hx₂⟩ := hx.toNat
  by_cases hk : k = x.toInt
  · subst hk
    simp only [Mem.view, ite_eq_left (And.intro hx.1 hx.2), BitVec.ofInt_toInt, Mem.load_store_same mem (a.1, a.2 + 4 * x) v r h]
    simp
  · simp only [Mem.view, hk, ite_false]
    split
    · rw [Mem.load_store_ne mem _ (a.1, a.2 + 4 * x) v r h]
      intro i hi ⟨_, hlt⟩
      have hk' : (BitVec.ofInt 64 k).toNat = k.toNat := by
        simp [BitVec.toNat_ofInt]; omega
      have hne : (BitVec.ofInt 64 k) ≠ x := by
        intro e; apply hk; have := congrArg BitVec.toNat e; omega
      have hi' : (BitVec.ofNat 64 i).toNat = i := by simp; omega
      simp only at hlt
      bv_omega
    · rfl

def Frame (a : Ptr) (mem mem' : Mem) : Prop :=
  (∀ id, id ≠ a.1 → mem'.regions id = mem.regions id) ∧ mem'.next = mem.next ∧
    ∃ r, mem'.regions a.1 = .inr r

theorem Frame.refl {a : Ptr} {mem : Mem} (r : BitVec 64 → BitVec 8 ⊕ Ptr) (h : mem.regions a.1 = .inr r) :
    Frame a mem mem :=
  ⟨fun _ _ => rfl, rfl, r, h⟩

theorem Frame.trans {a : Ptr} {m₁ m₂ m₃ : Mem} (h₁ : Frame a m₁ m₂) (h₂ : Frame a m₂ m₃) : Frame a m₁ m₃ :=
  ⟨fun id h => (h₂.1 id h).trans (h₁.1 id h), h₂.2.1.trans h₁.2.1, h₂.2.2⟩

theorem Frame.store {a : Ptr} {mem : Mem} (x : BitVec 64) (v : BitVec 32)
    (r : BitVec 64 → BitVec 8 ⊕ Ptr) (h : mem.regions a.1 = .inr r) :
    Frame a mem (mem.store (a.1, a.2 + 4 * x) v) :=
  ⟨fun id hid => Mem.regions_store_ne mem (a.1, a.2 + 4 * x) v id hid, rfl,
    Mem.regions_store_alloc mem (a.1, a.2 + 4 * x) v r h⟩
