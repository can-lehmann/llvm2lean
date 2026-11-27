import QuickSort.Generated
import QuickSort.Spec
import QuickSort.Memory

theorem Small.of_bounds {x : BitVec 64} (lo hi : BitVec 64) (hlo : Small lo) (hhi : Small hi)
    (h₁ : lo.toInt ≤ x.toInt) (h₂ : x.toInt ≤ hi.toInt) : Small x :=
  ⟨by have := hlo.1; omega, by have := hhi.2; omega⟩

theorem toInt_add_one (x : BitVec 64) (hx : Small x) : (x + 1).toInt = x.toInt + 1 := by
  obtain ⟨h₁, h₂⟩ := hx.toNat
  rw [h₂, BitVec.toInt_eq_toNat_cond]
  split <;> bv_omega

theorem toInt_sub_one (x : BitVec 64) (hx : Small x) : (x - 1).toInt = x.toInt - 1 := by
  obtain ⟨h₁, h₂⟩ := hx.toNat
  rw [h₂, BitVec.toInt_eq_toNat_cond]
  split <;> bv_omega

theorem view_swap (mem : Mem) (a : Ptr) (i j : BitVec 64) (r : BitVec 64 → BitVec 8 ⊕ Ptr)
    (h : mem.regions a.1 = .inr r) (hi : Small i) (hj : Small j) :
    let mem' := (mem.store (a.1, a.2 + 4 * i) (mem.load (a.1, a.2 + 4 * j) 32)).store
      (a.1, a.2 + 4 * j) (mem.load (a.1, a.2 + 4 * i) 32)
    mem'.view a = Spec.swap (mem.view a) i.toInt j.toInt ∧ Frame a mem mem' := by
  intro mem'
  have f₁ := Frame.store (a := a) i (mem.load (a.1, a.2 + 4 * j) 32) r h
  obtain ⟨r', h'⟩ := f₁.2.2
  have f₂ := Frame.store (a := a) j (mem.load (a.1, a.2 + 4 * i) 32) r' h'
  refine ⟨?_, f₁.trans f₂⟩
  simp only [mem', Mem.view_store _ a j _ r' h' hj, Mem.view_store _ a i _ r h hi, Mem.load_view _ a _ hi,
    Mem.load_view _ a _ hj]
  funext k
  simp only [Spec.swap]
  by_cases e₁ : k = j.toInt <;> by_cases e₂ : k = i.toInt <;> simp_all

theorem loop_correct (a : Ptr) (lo hi : BitVec 64) (hlo : Small lo) (hhi : Small hi) (n : Nat) :
    ∀ (mem : Mem) (i j : BitVec 64) (p : BitVec 32), (hi.toInt - j.toInt).toNat = n →
      lo.toInt ≤ i.toInt → i.toInt ≤ j.toInt → j.toInt ≤ hi.toInt → (∃ r, mem.regions a.1 = .inr r) →
      ∃ mem' i', quick_sort.b3 a lo hi mem i j p = quick_sort.b9 a lo hi mem' i' ∧ Frame a mem mem' ∧
        mem'.view a = (Spec.partition (mem.view a) p.toInt hi.toInt i.toInt j.toInt).1 ∧
        i'.toInt = (Spec.partition (mem.view a) p.toInt hi.toInt i.toInt j.toInt).2 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro mem i j p hn h₁ h₂ h₃ ⟨r, hr⟩
  have si : Small i := Small.of_bounds lo hi hlo hhi h₁ (by omega)
  have sj : Small j := Small.of_bounds lo hi hlo hhi (by omega) h₃
  rw [quick_sort.b3.eq_1, Spec.partition]
  by_cases hj : j.toInt < hi.toInt
  · simp only [BitVec.slt_iff_toInt_lt.mpr hj, ite_true, hj, quick_sort.b5.eq_1]
    by_cases hc : mem.view a j.toInt < p.toInt
    · have hc' : (mem.load (a.1, a.2 + 4 * j) 32).slt p = true := by
        rw [BitVec.slt_iff_toInt_lt, Mem.load_view _ a _ sj]; exact hc
      simp only [hc', ite_true, hc,
        quick_sort.b6.eq_1, quick_sort.b7.eq_1, quick_sort.b8.eq_1]
      obtain ⟨hv, hf⟩ := view_swap mem a i j r hr si sj
      obtain ⟨mem', i', e, f, v, w⟩ := ih (hi.toInt - (j + 1).toInt).toNat
        (by rw [toInt_add_one j sj]; omega) _ (i + 1) (j + 1) p rfl
        (by rw [toInt_add_one i si]; omega) (by rw [toInt_add_one i si, toInt_add_one j sj]; omega)
        (by rw [toInt_add_one j sj]; omega) hf.2.2
      refine ⟨mem', i', e, hf.trans f, ?_, ?_⟩
      · rw [v, hv, toInt_add_one i si, toInt_add_one j sj]
      · rw [w, hv, toInt_add_one i si, toInt_add_one j sj]
    · have hc' : ¬ (mem.load (a.1, a.2 + 4 * j) 32).slt p = true := by
        rw [BitVec.slt_iff_toInt_lt, Mem.load_view _ a _ sj]; exact hc
      simp only [hc', hc, ite_false, quick_sort.b7.eq_1, quick_sort.b8.eq_1]
      obtain ⟨mem', i', e, f, v, w⟩ := ih (hi.toInt - (j + 1).toInt).toNat
        (by rw [toInt_add_one j sj]; omega) mem i (j + 1) p rfl h₁ (by rw [toInt_add_one j sj]; omega)
        (by rw [toInt_add_one j sj]; omega) ⟨r, hr⟩
      refine ⟨mem', i', e, f, ?_, ?_⟩
      · rw [v, toInt_add_one j sj]
      · rw [w, toInt_add_one j sj]
  · have hj' : ¬ j.slt hi = true := by rw [BitVec.slt_iff_toInt_lt]; exact hj
    simp only [hj', hj, ite_false, quick_sort.b4.eq_1]
    exact ⟨mem, i, rfl, Frame.refl r hr, rfl, rfl⟩

theorem quick_sort_equiv_aux (a : Ptr) (n : Nat) :
    ∀ (mem : Mem) (lo hi : BitVec 64), (hi.toInt - lo.toInt).toNat = n → 0 ≤ lo.toInt →
      hi.toInt < 2 ^ 62 → (∃ r, mem.regions a.1 = .inr r) →
      ∃ mem', quick_sort mem a lo hi = some mem' ∧ Frame a mem mem' ∧
        mem'.view a = Spec.quickSort (mem.view a) lo.toInt hi.toInt := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro mem lo hi hn hlo hhi ⟨r, hr⟩
  rw [quick_sort.eq_1, quick_sort.b0.eq_1]
  by_cases hle : hi.toInt ≤ lo.toInt
  · simp only [BitVec.sle_iff_toInt_le.mpr hle, ite_true, quick_sort.b1.eq_1, quick_sort.b10.eq_1]
    exact ⟨mem, rfl, Frame.refl r hr, (Spec.quickSort_base _ _ _ hle).symm⟩
  have hlt : lo.toInt < hi.toInt := by omega
  have slo : Small lo := ⟨hlo, by omega⟩
  have shi : Small hi := ⟨by omega, hhi⟩
  have hle' : ¬ hi.sle lo = true := by rw [BitVec.sle_iff_toInt_le]; exact hle
  simp only [hle', quick_sort.b2.eq_1]
  obtain ⟨mem₁, i, e₁, f₁, v₁, w₁⟩ := loop_correct a lo hi slo shi _ mem lo lo
    (mem.load (a.1, a.2 + 4 * hi) 32) rfl (Int.le_refl _) (Int.le_refl _) (by omega) ⟨r, hr⟩
  rw [Mem.load_view _ a _ shi] at v₁ w₁
  have hb := Spec.partition_bounds (mem.view a) (mem.view a hi.toInt) hi.toInt lo.toInt lo.toInt
    (Int.le_refl _) (by omega)
  rw [← w₁] at hb
  have si : Small i := Small.of_bounds lo hi slo shi hb.1 hb.2
  obtain ⟨r₁, hr₁⟩ := f₁.2.2
  obtain ⟨hv₂, f₂⟩ := view_swap mem₁ a i hi r₁ hr₁ si shi
  obtain ⟨mem₃, e₃, f₃, v₃⟩ := ih _ (by rw [toInt_sub_one i si]; omega) _ lo (i - 1) rfl hlo
    (by rw [toInt_sub_one i si]; omega) f₂.2.2
  obtain ⟨mem₄, e₄, f₄, v₄⟩ := ih _ (by rw [toInt_add_one i si]; omega) mem₃ (i + 1) hi rfl
    (by rw [toInt_add_one i si]; omega) hhi f₃.2.2
  rw [e₁, quick_sort.b9.eq_1]
  simp only [e₃, e₄, quick_sort.b10.eq_1, Option.bind_eq_bind, Option.bind_some]
  refine ⟨mem₄, rfl, f₁.trans (f₂.trans (f₃.trans f₄)), ?_⟩
  rw [v₄, v₃, hv₂, v₁, toInt_add_one i si, toInt_sub_one i si, w₁, Spec.quickSort_eq _ _ _ hlt]
