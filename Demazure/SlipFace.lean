import Demazure.Valley
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.Interval

/-- Definition 3.1 -/
structure SlipFace where
  func : ℤ → ℤ → ℤ
  χ : ℤ
  a_step : ∀ a b : ℤ, func a b ≤ func (a+1) b ∧ func (a+1) b ≤ func a b + 1
  b_step : ∀ a b : ℤ, func a (b+1) ≤ func a b ∧ func a b ≤ func a (b+1) + 1
  nonneg : ∀ a b, func a b ≥ 0
  ge_diff : ∀ a b, func a b ≥ a - b + χ
  small_a : ∀ b, ∃ A, ∀ a ≤ A, func a b  = 0
  large_a : ∀ b, ∃ A, ∀ a ≥ A, func a b = a - b + χ
  small_b : ∀ a, ∃ B, ∀ b ≤ B, func a b = a - b + χ
  large_b : ∀ a, ∃ B, ∀ b ≥ B, func a b = 0

instance : CoeFun SlipFace (fun _ => ℤ → ℤ → ℤ) :=
  ⟨SlipFace.func⟩

lemma SF_ext (s t : SlipFace) : s = t ↔ ∀ a b, s a b = t a b := by
  constructor
  · rintro rfl
    simp
  · intro h
    have : s.χ = t.χ := by
      obtain ⟨As, hAs⟩ := s.large_a 0
      obtain ⟨At, hAt⟩ := t.large_a 0
      let A := max As At
      have hs : s.χ = s A 0 - A := by
        have := hAs A (le_max_left _ _)
        omega
      have ht : t.χ = t A 0 - A := by
        have := hAt A (le_max_right _ _)
        omega
      rw [hs, ht, h A 0]
    cases s
    cases t
    simp at h this ⊢
    constructor
    · funext a b
      exact h a b
    · exact this

namespace SlipFace
variable (sf : SlipFace)

/-- Definition 3.4 -/
def dual : SlipFace := {
  func := fun b a => sf a b - a + b - sf.χ
  χ := -sf.χ,
  a_step := by
    rintro b a
    have step := sf.b_step a b
    constructor <;> omega
  b_step := by
    rintro b a
    have step := sf.a_step a b
    constructor <;> omega
  nonneg := by
    rintro b a
    have h := sf.ge_diff a b
    linarith
  ge_diff := by
    rintro b a
    have h := sf.nonneg a b
    linarith
  small_a := by
    rintro b
    obtain ⟨A, hA⟩ := sf.small_b b
    use A
    rintro a ha
    rw [hA a ha]
    omega
  large_a := by
    rintro b
    obtain ⟨A, hA⟩ := sf.large_b b
    use A
    rintro a ha
    rw [hA a ha]
    omega
  small_b := by
    rintro a
    obtain ⟨B, hB⟩ := sf.small_a a
    use B
    rintro b hb
    rw [hB b hb]
    omega
  large_b := by
    rintro a
    obtain ⟨B, hB⟩ := sf.large_a a
    use B
    rintro b hb
    rw [hB b hb]
    omega
}

lemma dual_dual (s : SlipFace) : s.dual.dual = s := by
  apply (SF_ext s.dual.dual s).mpr
  intro a b
  dsimp [SlipFace.dual]
  omega

lemma duality (a b : ℤ) : sf a b - sf.dual b a = a - b + sf.χ := by
  dsimp [SlipFace.dual]
  omega

lemma s_eq (a b : ℤ) : sf a b = a - b + sf.χ + sf.dual b a := by
  linarith [sf.duality a b]

lemma s'_eq (b a : ℤ) : sf.dual b a = sf a b - a + b - sf.χ := by
  linarith [sf.duality a b]

/-- Properties D1 and D2 -/
structure D_props (f : ℤ → ℤ → ℤ) : Prop where
  a_step : ∀ a b : ℤ, f (a+1) b ≥ f a b
  b_step : ∀ a b : ℤ, f a (b+1) ≤ f a b
  large_b : ∀ a, ∃ B, ∀ b ≥ B, f a b = 0
  small_a : ∀ b, ∃ A, ∀ a ≤ A, f a b = 0

lemma mono_a_of_D_props (f : ℤ → ℤ → ℤ) (h : D_props f) : ∀ a a' b, a ≤ a' → f a' b ≥ f a b := by
  intro a a' b ha
  let n : ℕ := (a' - a).toNat
  have a'_eq : a' = a + n := by
    omega
  rw [a'_eq]
  induction n with
  | zero => simp
  | succ n ih =>
    apply le_trans ih
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc]
    exact h.a_step (a + n) b

lemma mono_b_of_D_props (f : ℤ → ℤ → ℤ) (h : D_props f) : ∀ a b b', b ≤ b' → f a b' ≤ f a b := by
  intro a b b' hb
  let n : ℕ := (b' - b).toNat
  have b'_eq : b' = b + n := by
    omega
  rw [b'_eq]
  induction n with
  | zero => simp
  | succ n ih =>
    apply le_trans _ ih
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc]
    exact h.b_step a (b + n)

/-- Lemma 3.6 -/
lemma sf_of_D_props {s t : ℤ → ℤ → ℤ} {χ : ℤ} (h : ∀ a b, s a b - t b a = a - b + χ) :
  D_props s ∧ D_props t →
  ∃ sf : SlipFace, (sf.func = s ∧ sf.χ = χ) ∧ sf.dual.func = t := by
  rintro ⟨sp, tp⟩
  let sf : SlipFace := {
    func := s,
    χ := χ,
    a_step := by
      intro a b
      have step0 := sp.a_step a b
      have step1 := tp.b_step b a
      constructor <;> linarith [h (a+1) b, h a (b+1), h a b]
    b_step := by
      intro a b
      have step0 := sp.b_step a b
      have step1 := tp.a_step b a
      constructor <;> linarith [h a (b+1), h (a+1) b, h a b]
    nonneg := by
      intro a b
      obtain ⟨A, hA⟩ := sp.small_a b
      by_cases ha : a ≤ A
      · exact le_of_eq <| (Eq.symm <| hA a ha)
      · have ha : A ≤ a := by omega
        rw [← hA A (le_refl A)]
        exact mono_a_of_D_props s sp A a b ha
    ge_diff := by
      intro a b
      rw [← h a b]
      suffices t b a ≥ 0 by omega
      obtain ⟨B, hB⟩ := tp.small_a a
      by_cases hb : b ≤ B
      · exact le_of_eq <| (Eq.symm <| hB b hb)
      · have hb : B ≤ b := by omega
        rw [← hB B (le_refl B)]
        exact mono_a_of_D_props t tp B b a hb
    small_a := by
      intro b
      obtain ⟨A, hA⟩ := sp.small_a b
      use A
    large_a := by
      intro b
      obtain ⟨A, hA⟩ := tp.large_b b
      use A
      intro a ha
      specialize hA a ha
      specialize h a b
      rwa [hA, sub_zero] at h
    small_b := by
      intro a
      obtain ⟨B, hB⟩ := tp.small_a a
      use B
      intro b hb
      specialize hB b hb
      specialize h a b
      rwa [hB, sub_zero] at h
    large_b := by
      intro a
      obtain ⟨B, hB⟩ := sp.large_b a
      use B
  }
  use sf
  constructor
  · constructor <;> rfl
  · ext a b
    dsimp [SlipFace.dual]
    have hsf_func : sf.func = s := rfl
    have hsf_χ : sf.χ = χ := rfl
    rw [hsf_func, hsf_χ]
    linarith [h b a]

lemma D_props_of_sf (sf : SlipFace) : D_props sf.func ∧ D_props sf.dual.func := by
  constructor
  · constructor
    · intro a b
      exact (sf.a_step a b).1
    · intro a b
      exact (sf.b_step a b).1
    · intro a
      exact sf.large_b a
    · intro b
      exact sf.small_a b
  · constructor
    · intro a b
      exact (sf.dual.a_step a b).1
    · intro a b
      exact (sf.dual.b_step a b).1
    · intro a
      exact sf.dual.large_b a
    · intro b
      exact sf.dual.small_a b

lemma nondec {a a' b b' : ℤ} (a_le_a' : a ≤ a') (b'_le_b : b' ≤ b) : sf a b ≤ sf a' b' := by
  have dp := D_props_of_sf sf
  have h1 : sf a b ≤ sf a' b := by
    exact mono_a_of_D_props sf.func dp.1 a a' b a_le_a'
  have h2 : sf a' b ≤ sf a' b' := by
    exact mono_b_of_D_props sf.func dp.1 a' b' b b'_le_b
  exact le_trans h1 h2

lemma zero_below {a a' b b' : ℤ} (a_le_a' : a ≤ a') (b'_le_b : b' ≤ b) :
  sf a' b' = 0 → sf a b = 0 := by
  intro eq0
  have := sf.nondec a_le_a' b'_le_b
  have le_zero : sf a b ≤ 0 := by
    rwa [eq0] at this
  have ge_zero : sf a b ≥ 0 := sf.nonneg a b
  exact le_antisymm le_zero ge_zero

noncomputable def SlipValley (s t : SlipFace) (a b : ℤ) : Valley where
  f := fun l => s a l + t l b
  rises := by
    intro m
    let L := a - m + s.χ
    let R := b + m - t.χ
    suffices {n : ℤ | s a n + t n b ≤ m} ⊆ Finset.Icc L R by
      apply Set.Finite.subset _ this
      apply Set.Finite.ofFinset (Finset.Icc L R)
      intro x; simp
    intro n hn
    simp at hn
    suffices n ≥ L ∧ n ≤ R by simpa
    constructor
    · linarith [t.nonneg n b, s.ge_diff a n]
    · linarith [s.nonneg a n, t.ge_diff n b]

noncomputable def star_func (s t : SlipFace) : ℤ → ℤ → ℤ :=
  fun a b => (SlipValley s t a b).min

lemma star_dual_ineq (s t : SlipFace) (a b : ℤ) :
  star_func t.dual s.dual b a ≤ star_func s t a b - a + b - s.χ - t.χ := by
  let v := SlipValley s t a b
  let l := v.M
  have hl : s a l + t l b = star_func s t a b := by
    exact (SlipValley s t a b).f_M
  have ineq : star_func t.dual s.dual b a ≤ t.dual b l + s.dual l a := by
    exact (SlipValley t.dual s.dual b a).min_spec l
  apply le_trans ineq
  dsimp [SlipFace.dual]
  omega

lemma star_dual_eq (s t : SlipFace) (a b : ℤ) :
  star_func s t a b - star_func t.dual s.dual b a = a - b + s.χ + t.χ := by
  suffices star_func t.dual s.dual b a = star_func s t a b - a + b - s.χ - t.χ by omega
  apply le_antisymm
  · exact star_dual_ineq s t a b
  let s' := s.dual
  let t' := t.dual
  have s'' : s = s'.dual := by rw [SlipFace.dual_dual s]
  have t'' : t = t'.dual := by rw [SlipFace.dual_dual t]
  have ineq := star_dual_ineq t' s' b a
  rw [← s'', ← t''] at ineq
  subst s' t'
  have : s.dual.χ = - s.χ := by dsimp [SlipFace.dual]
  rw [this] at ineq
  have : t.dual.χ = - t.χ := by dsimp [SlipFace.dual]
  rw [this] at ineq
  omega

lemma D_props_of_star_func (s t : SlipFace) : D_props (s.star_func t) := by
  constructor
  · intro a b
    let v := SlipValley s t (a+1) b
    let l := v.M
    have hl : s (a+1) l + t l b = s.star_func t (a+1) b := by
      exact (SlipValley s t (a+1) b).f_M
    rw [← hl]
    have hmin : s.star_func t a b ≤ s a l + t l b := by
      exact (SlipValley s t a b).min_spec l
    apply le_trans hmin
    have step : s a l ≤ s (a+1) l := (s.a_step a l).1
    omega
  · intro a b
    let v := SlipValley s t a b
    let l := v.M
    have hl : s a l + t l b = s.star_func t a b := by
      exact (SlipValley s t a b).f_M
    rw [← hl]
    have hmin : s.star_func t a (b+1) ≤ s a l + t l (b+1) := by
      exact (SlipValley s t a (b+1)).min_spec l
    apply le_trans hmin
    have step : t l (b+1) ≤ t l b := (t.b_step l b).1
    omega
  · intro a
    obtain ⟨l, hl⟩ := s.large_b a
    specialize hl l (le_refl l)
    obtain ⟨B, hB⟩ := t.large_b l
    use B
    intro b hb
    specialize hB b hb
    have : s.star_func t a b ≤ s a l + t l b := by
      exact (SlipValley s t a b).min_spec l
    have le_zero : s.star_func t a b ≤ 0 := by
      rwa [hl, hB, add_zero] at this
    have ge_zero : s.star_func t a b ≥ 0 := by
      let v := SlipValley s t a b
      let l := v.M
      have hl : s a l + t l b = s.star_func t a b := by
        exact (SlipValley s t a b).f_M
      rw [← hl]
      linarith [s.nonneg a l, t.nonneg l b]
    exact le_antisymm le_zero ge_zero
  · intro b
    obtain ⟨l, hl⟩ := t.small_a b
    specialize hl l (le_refl l)
    obtain ⟨A, hA⟩ := s.small_a l
    use A
    intro a ha
    specialize hA a ha
    have : s.star_func t a b ≤ s a l + t l b := by
      exact (SlipValley s t a b).min_spec l
    have le_zero : s.star_func t a b ≤ 0 := by
      rwa [hA, hl, zero_add] at this
    have ge_zero : s.star_func t a b ≥ 0 := by
      let v := SlipValley s t a b
      let l := v.M
      have hl : s a l + t l b = s.star_func t a b := by
        exact (SlipValley s t a b).f_M
      linarith [s.nonneg a l, t.nonneg l b]
    exact le_antisymm le_zero ge_zero

lemma star_exists (s t : SlipFace) : ∃ p : SlipFace,
  ((p.func = star_func s t ∧ p.χ = s.χ + t.χ)
  ∧ p.dual.func = star_func t.dual s.dual) := by
  let P := star_func s t
  let P' := star_func t.dual s.dual
  let χ := s.χ + t.χ
  have : ∀ a b : ℤ, P a b - P' b a = a - b + χ := by
    intro a b
    rw [star_dual_eq s t a b]
    omega
  have h := sf_of_D_props this
  suffices D_props P ∧ D_props P' by
    exact h this
  exact ⟨D_props_of_star_func s t, D_props_of_star_func t.dual s.dual⟩

noncomputable def star (s t : SlipFace) : SlipFace :=
  Classical.choose (star_exists s t)

noncomputable instance : Mul SlipFace := ⟨star⟩

infixl:70 " ⋆ " => star

lemma star_func_eq (s t : SlipFace) : (s ⋆ t).func = star_func s t := by
  have h := star_exists s t
  exact (Classical.choose_spec h).1.1

@[simp] lemma chi_star (s t : SlipFace) : (s ⋆ t).χ = s.χ + t.χ := by
  have h := star_exists s t
  exact (Classical.choose_spec h).1.2

@[simp] lemma star_dual (s t : SlipFace) : (s ⋆ t).dual = t.dual ⋆ s.dual := by
  have h := star_exists s t
  have := (Classical.choose_spec h).2
  apply (SF_ext _ _).mpr
  rw [star_func_eq]
  rw [← this]
  intro a b
  rfl

/-! ### Partial order on SlipFace, and interaction with ⋆  -/

instance : PartialOrder SlipFace where
  le (s t : SlipFace) := ∀ a b, s a b ≤ t a b
  le_refl := by
    intro s a b
    exact le_refl <| s a b
  le_trans := by
    intro s t u hst htu a b
    exact le_trans (hst a b) (htu a b)
  le_antisymm := by
    intro s t hst hts
    apply (SF_ext s t).mpr
    intro a b
    have le1 : s a b ≤ t a b := hst a b
    have le2 : t a b ≤ s a b := hts a b
    exact le_antisymm le1 le2

/-!  The following functions/lemmas form a wrapper around SlipValley
  to make it easier to work with. -/

lemma star_val_le (s t : SlipFace) (a b l : ℤ) : (s ⋆ t) a b ≤ s a l + t l b := by
  let v := SlipValley s t a b
  have hmin : (s ⋆ t) a b = v.min := by
    rw [star_func_eq]
    rfl
  have hM : v.min ≤ s a l+ t l b  := by
    exact v.min_spec l
  rwa [← hmin] at hM

noncomputable def star_wit (s t : SlipFace) (a b : ℤ) : ℤ :=
  (SlipValley s t a b).M

lemma star_wit_spec (s t : SlipFace) (a b : ℤ) :
  (s ⋆ t) a b = s a (star_wit s t a b) + t (star_wit s t a b) b := by
  let v := SlipValley s t a b
  rw [star_func_eq]
  exact Eq.symm v.f_M

lemma le_star_val_iff (r s t : SlipFace) (a b : ℤ) :
  r a b ≤ (s ⋆ t) a b ↔ ∀ l, r a b ≤ s a l + t l b
  := by
  constructor
  · intro h l
    contrapose! h
    exact lt_of_le_of_lt (star_val_le s t a b l) h
  · intro h
    let l := star_wit s t a b
    have : (s ⋆ t) a b = s a l + t l b := by
      exact star_wit_spec s t a b
    rw [this]
    exact h l

lemma ge_star_val_iff (r s t : SlipFace) (a b : ℤ) :
  r a b ≥ (s ⋆ t) a b ↔ ∃ l, r a b ≥ s a l + t l b
  := by
  constructor
  · intro h
    use star_wit s t a b
    rw [← star_wit_spec s t a b]
    exact h
  · rintro ⟨l, hl⟩
    exact le_trans (star_val_le s t a b l) hl

/-! ### Monoid structure on SlipFace -/

lemma star_assoc (r s t : SlipFace) : r ⋆ s ⋆ t = r ⋆ (s ⋆ t) := by
  apply (SF_ext _ _).mpr
  intro a b
  apply le_antisymm
  · let l := star_wit r (s ⋆ t) a b
    have : (r ⋆ (s ⋆ t)) a b = r a l + (s ⋆ t) l b := star_wit_spec r (s ⋆ t) a b
    rw [this]
    let m := star_wit s t l b
    have : (s ⋆ t) l b = s l m + t m b := star_wit_spec s t l b
    rw [this]
    have h1 : (r ⋆ s ⋆ t) a b ≤ (r ⋆ s) a m + t m b := by apply star_val_le
    have h2 : (r ⋆ s) a m ≤ r a l + s l m := by apply star_val_le

    omega
  · let l := star_wit (r ⋆ s) t a b
    have : ((r ⋆ s) ⋆ t) a b = (r ⋆ s) a l + t l b := star_wit_spec (r ⋆ s) t a b
    rw [this]
    let m := star_wit r s a l
    have : (r ⋆ s) a l = r a m + s m l := star_wit_spec r s a l
    rw [this]
    have h1 : (r ⋆ (s ⋆ t)) a b ≤ r a m + (s ⋆ t) m b := by apply star_val_le
    have h2 : (s ⋆ t) m b ≤ s m l + t l b := by apply star_val_le
    omega

def id : SlipFace := {
    func := fun a b => max (a - b) 0,
    χ := 0,
    a_step := by
      intro a b
      by_cases ha : a - b ≥ 0 <;> omega
    b_step := by
      intro a b
      by_cases hb : a - (b + 1) ≥ 0 <;> omega
    nonneg := by
      intro a b
      exact le_max_right (a - b) 0
    ge_diff := by
      intro a b
      rw [add_zero]
      exact le_max_left (a - b) 0
    small_a := by
      intro b
      use b
      omega
    large_a := by
      intro b
      use b
      omega
    small_b := by
      intro a
      use a
      omega
    large_b := by
      intro a
      use a
      omega
  }

lemma id_mul (s : SlipFace) : id ⋆ s = s := by
  apply (SF_ext _ _).mpr
  intro a b
  apply le_antisymm
  · apply (ge_star_val_iff s id s a b).mpr
    use a
    have : id a a = 0 := by
      rw [id]
      simp
    simp [this]
  · apply (le_star_val_iff s id s a b).mpr
    intro l
    by_cases hl : l ≤ a
    · have : id a l = a - l := by
        rw [id]
        simp [hl]
      rw [this]
      rw [s.s_eq a b, s.s_eq l b]
      have : s.dual b l ≥ s.dual b a := by
        apply s.dual.nondec (le_refl b) hl
      omega
    · have : id a l = 0 := by
        rw [id]; simp; omega
      rw [this, zero_add]
      apply s.nondec (by linarith) (le_refl b)

lemma mul_id (s : SlipFace) : s ⋆ id = s := by
  let t := s.dual
  have : s = t.dual := by rw [SlipFace.dual_dual s]
  rw [this]
  have : id = id.dual := by
    apply (SF_ext _ _).mpr
    intro a b
    dsimp [id, SlipFace.dual]
    omega
  suffices t.dual ⋆ id.dual = t.dual by
    convert this
  rw [← star_dual, id_mul]


noncomputable instance : Monoid SlipFace where
  mul := star
  one := id
  mul_assoc := star_assoc
  one_mul := id_mul
  mul_one := mul_id


/-! ### $\Delta$ and its properties -/

def Δ (a b : ℤ) : ℤ :=
  sf (a+1) b - sf a b - sf (a+1) (b+1) + sf a (b+1)

/-- Equation (18) -/
lemma Δ_dual (a b : ℤ) : sf.dual.Δ b a = sf.Δ a b := by
  dsimp [SlipFace.dual, Δ]
  omega

lemma Δ_values (a b : ℤ) : sf.Δ a b = 0 ∨ sf.Δ a b = 1 ∨ sf.Δ a b = -1 := by
  suffices sf.Δ a b ≥ -1 ∧ sf.Δ a b ≤ 1 by omega
  let d1 := sf (a+1) b - sf a b
  let d2 := sf (a+1) (b+1) - sf a (b+1)
  have diff : sf.Δ a b = d1 - d2 := by (dsimp [Δ]; omega)
  suffices d1 - d2 ≥ -1 ∧ d1 - d2 ≤ 1 by (rw [diff]; simpa)
  obtain ⟨h11, h12⟩ := sf.a_step a b
  obtain ⟨h21, h22⟩ := sf.a_step a (b+1)
  omega

lemma Δ_zero_of_s_zero (a b : ℤ) (h0 : sf (a + 1) b = 0) : sf.Δ a b = 0 := by
  have h1 : sf a b = 0 := by
    apply sf.zero_below (a' := a+1) (b' := b)
    repeat linarith
  have h2 : sf (a+1) (b+1) = 0 := by
    apply sf.zero_below (a' := a+1) (b' := b)
    repeat linarith
  have h3 : sf a (b+1) = 0 := by
    apply sf.zero_below (a' := a+1) (b' := b)
    repeat linarith
  dsimp [Δ]
  rw [h0, h1, h2, h3]
  norm_num

lemma sum_a {a₁ a₂ : ℤ} (ha : a₁ ≤ a₂) (b : ℤ) :
  ∑ a ∈ Finset.Ico a₁ a₂, sf.Δ a b
  = (sf a₂ b  - sf a₂ (b+1)) - (sf a₁ b - sf a₁ (b+1)) := by
  let n : ℕ := (a₂ - a₁).toNat
  have a₂_eq : a₂ = a₁ + n := by omega
  rw [a₂_eq]
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Nat.cast_add n 1, Nat.cast_one, ← add_assoc]
    have disj : Disjoint (Finset.Ico a₁ (a₁ + n)) {a₁ + n} := by simp
    have union : Finset.Ico a₁ (a₁ + n + 1) = Finset.Ico a₁ (a₁ + n) ∪ {a₁ + n} := by
      apply Finset.ext
      intro x
      repeat rw [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico]
      grind
    rw [union, Finset.sum_union disj, Finset.sum_singleton, SlipFace.Δ, ih]
    omega

lemma sum_b (a : ℤ) {b₁ b₂ : ℤ} (hb : b₁ ≤ b₂) :
  ∑ b ∈ Finset.Ico b₁ b₂, sf.Δ a b
  = (sf (a+1) b₁ - sf a b₁) - (sf (a+1) b₂ - sf a b₂) := by
  let n : ℕ := (b₂ - b₁).toNat
  have b₂_eq : b₂ = b₁ + n := by omega
  rw [b₂_eq]
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Nat.cast_add n 1, Nat.cast_one, ← add_assoc]
    have disj : Disjoint (Finset.Ico b₁ (b₁ + n)) {b₁ + n} := by simp
    have union : Finset.Ico b₁ (b₁ + n + 1) = Finset.Ico b₁ (b₁ + n) ∪ {b₁ + n} := by
      apply Finset.ext
      intro x
      repeat rw [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico]
      grind
    rw [union, Finset.sum_union disj, Finset.sum_singleton, SlipFace.Δ, ih]
    omega

/-- Modification of Equation (17) to a finite sum -/
lemma sum_ab {a₁ a₂ b₁ b₂ : ℤ} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
  ∑ b ∈ Finset.Ico b₁ b₂, ∑ a ∈ Finset.Ico a₁ a₂, sf.Δ a b
  = (sf a₂ b₁ - sf a₁ b₁) - (sf a₂ b₂ - sf a₁ b₂) := by
  let n : ℕ := (b₂ - b₁).toNat
  have b₂_eq : b₂ = b₁ + n := by omega
  rw [b₂_eq]
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Nat.cast_add n 1, Nat.cast_one, ← add_assoc]
    have disj : Disjoint (Finset.Ico b₁ (b₁ + n)) {b₁ + n} := by simp
    have union : Finset.Ico b₁ (b₁ + n + 1) = Finset.Ico b₁ (b₁ + n) ∪ {b₁ + n} := by
      apply Finset.ext
      intro x
      repeat rw [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico]
      grind
    rw [union, Finset.sum_union disj, Finset.sum_singleton, ih, sf.sum_a ha (b₁ + n)]
    omega

/-- Definition 4.2 -/
def submodular : Prop := ∀ a b : ℤ, sf.Δ a b ≥ 0

def Γ : Set (ℤ × ℤ) := {(a, b) | sf.Δ a b = 1}

lemma Γ_dual : ∀ (a b : ℤ), (a, b) ∈ sf.Γ ↔ (b, a) ∈ sf.dual.Γ := by
  intro a b
  simp [SlipFace.Γ, sf.Δ_dual]

end SlipFace
