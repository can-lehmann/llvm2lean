namespace Spec

def swap (f : Int → Int) (i j : Int) : Int → Int :=
  fun k => if k = i then f j else if k = j then f i else f k

def partition (f : Int → Int) (pivot hi i j : Int) : (Int → Int) × Int :=
  if j < hi then
    if f j < pivot then partition (swap f i j) pivot hi (i + 1) (j + 1)
    else partition f pivot hi i (j + 1)
  else (f, i)
termination_by (hi - j).toNat

theorem partition_bounds (f : Int → Int) (pivot hi i j : Int) (hij : i ≤ j) (hj : j ≤ hi) :
    i ≤ (partition f pivot hi i j).2 ∧ (partition f pivot hi i j).2 ≤ hi := by
  fun_induction partition f pivot hi i j with
  | case1 f i j h1 h2 ih => have := ih (by omega) (by omega); omega
  | case2 f i j h1 h2 ih => have := ih (by omega) (by omega); omega
  | case3 f i j h1 => simp; omega

def quickSort (f : Int → Int) (lo hi : Int) : Int → Int :=
  if h : lo < hi then
    let r := partition f (f hi) hi lo lo
    have hb := partition_bounds f (f hi) hi lo lo (Int.le_refl _) (Int.le_of_lt h)
    let g := quickSort (swap r.1 r.2 hi) lo (r.2 - 1)
    quickSort g (r.2 + 1) hi
  else f
termination_by (hi - lo).toNat
decreasing_by all_goals omega

def Sorted (f : Int → Int) (lo hi : Int) : Prop :=
  ∀ x y, lo ≤ x → x ≤ y → y ≤ hi → f x ≤ f y

def Perm (lo hi : Int) (f g : Int → Int) : Prop :=
  ∃ σ τ : Int → Int, (∀ k, σ (τ k) = k) ∧ (∀ k, τ (σ k) = k) ∧
    (∀ k, (k < lo ∨ hi < k) → σ k = k) ∧ ∀ k, g k = f (σ k)

theorem Perm.refl (lo hi : Int) (f : Int → Int) : Perm lo hi f f :=
  ⟨id, id, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem Perm.trans {lo hi : Int} {f g h : Int → Int} (h₁ : Perm lo hi f g) (h₂ : Perm lo hi g h) :
    Perm lo hi f h := by
  obtain ⟨σ₁, τ₁, a₁, b₁, c₁, d₁⟩ := h₁
  obtain ⟨σ₂, τ₂, a₂, b₂, c₂, d₂⟩ := h₂
  refine ⟨σ₁ ∘ σ₂, τ₂ ∘ τ₁, ?_, ?_, ?_, ?_⟩ <;> intro k <;> simp_all

theorem Perm.mono {lo hi lo' hi' : Int} {f g : Int → Int} (h : Perm lo hi f g) (hlo : lo' ≤ lo)
    (hhi : hi ≤ hi') : Perm lo' hi' f g := by
  obtain ⟨σ, τ, a, b, c, d⟩ := h
  exact ⟨σ, τ, a, b, fun k hk => c k (by omega), d⟩

theorem Perm.swap {lo hi i j : Int} (f : Int → Int) (hi₁ : lo ≤ i) (hi₂ : i ≤ hi) (hj₁ : lo ≤ j)
    (hj₂ : j ≤ hi) : Perm lo hi f (Spec.swap f i j) := by
  let σ : Int → Int := fun k => if k = i then j else if k = j then i else k
  refine ⟨σ, σ, ?_, ?_, ?_, ?_⟩ <;> intro k <;> simp only [σ, Spec.swap] <;> split <;> grind

theorem Perm.outside {lo hi : Int} {f g : Int → Int} (h : Perm lo hi f g) (k : Int)
    (hk : k < lo ∨ hi < k) : g k = f k := by
  obtain ⟨σ, τ, a, b, c, d⟩ := h
  rw [d, c k hk]

theorem Perm.forall {lo hi : Int} {f g : Int → Int} {P : Int → Prop} (h : Perm lo hi f g)
    (hP : ∀ k, lo ≤ k → k ≤ hi → P (f k)) : ∀ k, lo ≤ k → k ≤ hi → P (g k) := by
  obtain ⟨σ, τ, a, b, c, d⟩ := h
  intro k h₁ h₂
  have hin : lo ≤ σ k ∧ σ k ≤ hi := by
    false_or_by_contra
    have e₁ := c (σ k) (by omega)
    have e₂ : τ (σ (σ k)) = σ k := b (σ k)
    rw [e₁, b k] at e₂
    omega
  rw [d]
  exact hP _ hin.1 hin.2

theorem partition_spec (f : Int → Int) (pivot lo hi i j : Int) (hlo : lo ≤ i) (hij : i ≤ j)
    (hj : j ≤ hi) (hlt : ∀ k, lo ≤ k → k < i → f k < pivot)
    (hge : ∀ k, i ≤ k → k < j → pivot ≤ f k) :
    Perm lo (hi - 1) f (partition f pivot hi i j).1 ∧
    (∀ k, lo ≤ k → k < (partition f pivot hi i j).2 → (partition f pivot hi i j).1 k < pivot) ∧
    (∀ k, (partition f pivot hi i j).2 ≤ k → k < hi → pivot ≤ (partition f pivot hi i j).1 k) := by
  fun_induction partition f pivot hi i j with
  | case1 f i j h1 h2 ih =>
    obtain ⟨p, q, r⟩ := ih (by omega) (by omega) (by omega)
      (by intro k _ _; simp only [Spec.swap]; split <;> (try split) <;> grind)
      (by intro k _ _; simp only [Spec.swap]; split <;> (try split) <;> grind)
    exact ⟨(Perm.swap f (by omega) (by omega) (by omega) (by omega)).trans p, q, r⟩
  | case2 f i j h1 h2 ih =>
    exact ih hlo (by omega) (by omega) hlt (by intro k _ _; by_cases k = j <;> grind)
  | case3 f i j h1 =>
    refine ⟨Perm.refl _ _ _, hlt, ?_⟩
    intro k _ _; exact hge k (by omega) (by omega)

theorem quickSort_eq (f : Int → Int) (lo hi : Int) (h : lo < hi) :
    quickSort f lo hi =
      quickSort (quickSort (swap (partition f (f hi) hi lo lo).1 (partition f (f hi) hi lo lo).2 hi)
        lo ((partition f (f hi) hi lo lo).2 - 1)) ((partition f (f hi) hi lo lo).2 + 1) hi := by
  rw [quickSort]; simp [h]

theorem quickSort_base (f : Int → Int) (lo hi : Int) (h : hi ≤ lo) : quickSort f lo hi = f := by
  rw [quickSort]; simp; omega

theorem quickSort_spec (f : Int → Int) (lo hi : Int) :
    Sorted (quickSort f lo hi) lo hi ∧ Perm lo hi f (quickSort f lo hi) := by
  induction hn : (hi - lo).toNat using Nat.strongRecOn generalizing f lo hi with
  | ind n ih =>
  by_cases h' : hi ≤ lo
  · rw [quickSort_base f lo hi (by omega)]
    refine ⟨fun x y _ _ _ => ?_, Perm.refl _ _ _⟩
    have : x = y := by omega
    subst this; exact Int.le_refl _
  have h : lo < hi := by omega
  rw [quickSort_eq f lo hi h]
  have hb := partition_bounds f (f hi) hi lo lo (Int.le_refl _) (Int.le_of_lt h)
  obtain ⟨hp, hlt, hge⟩ := partition_spec f (f hi) lo hi lo lo (Int.le_refl _) (Int.le_refl _)
    (Int.le_of_lt h) (fun _ _ _ => by omega) (fun _ _ _ => by omega)
  generalize partition f (f hi) hi lo lo = r at hb hp hlt hge
  obtain ⟨r₀, i⟩ := r
  simp only at hb hp hlt hge ⊢
  have hhi : r₀ hi = f hi := hp.outside hi (by omega)
  have p₀ : Perm lo hi f (swap r₀ i hi) :=
    (hp.mono (Int.le_refl _) (by omega)).trans (Perm.swap _ hb.1 hb.2 (Int.le_of_lt h) (Int.le_refl _))
  obtain ⟨s₁, p₁⟩ := ih _ (by omega) (swap r₀ i hi) lo (i - 1) rfl
  generalize quickSort (swap r₀ i hi) lo (i - 1) = g at s₁ p₁
  obtain ⟨s₂, p₂⟩ := ih _ (by omega) g (i + 1) hi rfl
  have g_lt : ∀ k, lo ≤ k → k ≤ i - 1 → g k < f hi :=
    p₁.forall (P := (· < f hi)) (fun k h₁ h₂ => by simp only [swap]; grind)
  have g_piv : g i = f hi := by rw [p₁.outside i (by omega)]; simp [swap]; grind
  have g_ge : ∀ k, i + 1 ≤ k → k ≤ hi → f hi ≤ g k := by
    intro k h₁ h₂
    rw [p₁.outside k (by omega)]
    simp only [swap]
    by_cases k = hi <;> grind
  have h_ge := p₂.forall (P := (f hi ≤ ·)) g_ge
  generalize quickSort g (i + 1) hi = g' at s₂ p₂ h_ge
  have h_lo : ∀ k, k ≤ i → g' k = g k := fun k hk => p₂.outside k (by omega)
  refine ⟨?_, (p₀.trans (p₁.mono (Int.le_refl _) (by omega))).trans (p₂.mono (by omega) (Int.le_refl _))⟩
  intro x y hx hxy hy
  by_cases hy' : y ≤ i - 1
  · rw [h_lo x (by omega), h_lo y (by omega)]; exact s₁ x y hx hxy hy'
  by_cases hx' : i + 1 ≤ x
  · exact s₂ x y hx' hxy hy
  by_cases hyp : y = i
  · subst hyp
    rw [h_lo x (by omega), h_lo y (by omega), g_piv]
    by_cases hxp : x = y
    · subst hxp; rw [g_piv]; exact Int.le_refl _
    · exact Int.le_of_lt (g_lt x hx (by omega))
  have := h_ge y (by omega) hy
  by_cases hxp : x = i
  · subst hxp; rw [h_lo x (by omega), g_piv]; exact this
  · rw [h_lo x (by omega)]; exact Int.le_trans (Int.le_of_lt (g_lt x hx (by omega))) this

end Spec
