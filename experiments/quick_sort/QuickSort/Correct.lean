import QuickSort.Equiv

theorem quick_sort_equiv (mem : Mem) (a : Ptr) (lo hi : BitVec 64) (hlo : 0 ≤ lo.toInt)
    (hhi : hi.toInt < 2 ^ 62) (halloc : ∃ r, mem.regions a.1 = .inr r) :
    ∃ mem', quick_sort mem a lo hi = some mem' ∧ Frame a mem mem' ∧
      mem'.view a = Spec.quickSort (mem.view a) lo.toInt hi.toInt :=
  quick_sort_equiv_aux a _ mem lo hi rfl hlo hhi halloc

theorem quick_sort_correct (mem : Mem) (a : Ptr) (lo hi : BitVec 64) (hlo : 0 ≤ lo.toInt)
    (hhi : hi.toInt < 2 ^ 62) (halloc : ∃ r, mem.regions a.1 = .inr r) :
    ∃ mem', quick_sort mem a lo hi = some mem' ∧ Frame a mem mem' ∧
      Spec.Sorted (mem'.view a) lo.toInt hi.toInt ∧ Spec.Perm lo.toInt hi.toInt (mem.view a) (mem'.view a) := by
  obtain ⟨mem', e, f, v⟩ := quick_sort_equiv mem a lo hi hlo hhi halloc
  refine ⟨mem', e, f, ?_⟩
  rw [v]
  exact Spec.quickSort_spec _ _ _
