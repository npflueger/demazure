/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
import Demazure.Valley
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.Interval

/-!
# Slip Faces

This file defines slipface functions and develops their basic properties, including the $\star$
(Demazure products) and contractions $\triangleleft$ and $\triangleright$. It corresponds roughly to
Section 3 of [An extended Demazure product](https://arxiv.org/abs/2206.14227).
-/

/-- A slipface function of shift `χ`, i.e. a function $s : \mathbb{Z}^2 \to \mathbb{N}$
satisfying conditions (S1) to (S3) from
[An extended Demazure product](https://arxiv.org/abs/2206.14227):

- first differences in the `a`- and `b`-directions are in `{0,1}`
- $s(a,b) \ge \max\{0, \chi + a - b\}$
- each row and column eventually agrees with $\max\{0, \chi + a - b\}$

Lean stores the function as `func` and the shift as `χ`; the article writes this as
$s \in \mathrm{SF}_\chi$. *Definition 3.1 (`defn:slipface`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
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
    have hχ : s.χ = t.χ := by
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
    rw [SlipFace.mk.injEq]
    constructor
    · funext a b
      exact h a b
    · exact hχ

namespace SlipFace
variable (sf : SlipFace)

/-- The dual slipface $s^\vee$, characterized by
$$
s(a,b) - s^\vee(b,a) = \chi + a - b.
$$

In Lean the dual is `sf.dual`, and its value at `(b,a)` is written
`sf.dual b a`. *Definition 3.4 (`defn:sdual`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
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

/-- The one-sided monotonicity and vanishing conditions providing a simplified
criterion for slipfaces.

These are conditions (D1) and (D2) from
[An extended Demazure product](https://arxiv.org/abs/2206.14227), extracted into a reusable Lean
structure. *Properties D1 and D2.* -/
structure D_props (f : ℤ → ℤ → ℤ) : Prop where
  a_step : ∀ a b : ℤ, f (a+1) b ≥ f a b
  b_step : ∀ a b : ℤ, f a (b+1) ≤ f a b
  large_b : ∀ a, ∃ B, ∀ b ≥ B, f a b = 0
  small_a : ∀ b, ∃ A, ∀ a ≤ A, f a b = 0

lemma mono_a_of_D_props (f : ℤ → ℤ → ℤ) (h : D_props f) :
    ∀ a a' b, a ≤ a' → f a' b ≥ f a b := by
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

lemma mono_b_of_D_props (f : ℤ → ℤ → ℤ) (h : D_props f) :
    ∀ a b b', b ≤ b' → f a b' ≤ f a b := by
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

/-- Construct a slipface from a pair of functions satisfying `D_props` and the
duality relation `s a b - t b a = a - b + χ`. *Lemma 3.6 (`lem:dualCrit`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
lemma sf_of_D_props {s t : ℤ → ℤ → ℤ} {χ : ℤ}
    (h : ∀ a b, s a b - t b a = a - b + χ) :
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

/-! ### Slip Valleys and the Product Formula

A `Valley` is an integer function rising on both sides, which therefore has a
well-defined minimum achieved at finitely many places.

This section packages the minimization problem defining slipface product into a
`Valley`, then uses it to construct the product `s ⋆ t` and prove its basic
properties. -/

/-- The valley $\ell \mapsto s(a,\ell) + t(\ell,b)$ whose minimum computes the
slipface product at `(a,b)`. -/
noncomputable def SlipValley (s t : SlipFace) (a b : ℤ) : Valley where
  f := fun l => s a l + t l b
  rises := by
    intro m
    let L := a - m + s.χ
    let R := b + m - t.χ
    suffices {n : ℤ | s a n + t n b ≤ m} ⊆ Finset.Icc L R by
      apply Set.Finite.subset _ this
      apply Set.Finite.ofFinset (Finset.Icc L R)
      intro x
      simp only [Finset.mem_Icc, Finset.coe_Icc, Set.mem_Icc]
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    suffices n ≥ L ∧ n ≤ R by simpa
    constructor
    · linarith [t.nonneg n b, s.ge_diff a n]
    · linarith [s.nonneg a n, t.ge_diff n b]

/-- The min-plus product formula
$$
(s \star t)(a,b) = \min_{\ell \in \mathbb{Z}} [s(a,\ell) + t(\ell,b)].
$$

In Lean, `star_func s t a b` is this integer value, while `s ⋆ t` is the resulting
`SlipFace`. *Definition 3.7 (`defn:sfAlgebra`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/3.* -/
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

/-- The product function `star_func s t` comes from a slipface of shift
`s.χ + t.χ`. *Proposition 3.9 (`prop:sfAlgebraDefined`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/5.* -/
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

/-- The product of two slipfaces, obtained from the minimum formula
`star_func`. -/
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

/-- Duality reverses the product `⋆`. *Proposition 3.9 (`prop:sfAlgebraDefined`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 4/5.* -/
@[simp] lemma star_dual (s t : SlipFace) : (s ⋆ t).dual = t.dual ⋆ s.dual := by
  have h := star_exists s t
  have := (Classical.choose_spec h).2
  apply (SF_ext _ _).mpr
  rw [star_func_eq]
  rw [← this]
  intro a b
  rfl

/-! ### Order Structure and Comparison with `⋆`

This section puts the pointwise order on `SlipFace` and records the basic
comparison lemmas relating that order to the product `⋆`.
The order is the Bruhat order on slipfaces from
[An extended Demazure product](https://arxiv.org/abs/2206.14227). *Definition 3.2.* -/

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

/-- A lower bound for `(s ⋆ t) a b` is equivalent to a uniform lower bound
against every witness `l`. -/
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

/-- An upper bound for `(s ⋆ t) a b` is equivalent to exhibiting a single
witness `l` that realizes it. -/
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

/-! ### Monoid Structure

The product `⋆` is associative and has the positive-part function as identity,
giving `SlipFace` a monoid structure. -/

/-- Slipface product is associative. *Lemma 3.11 (`lem:sfAlgebra`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/3.* -/
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

/-- The identity slipface, given by the positive part of `a - b`. -/
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
    simp only [this, zero_add, ge_iff_le, le_refl]
  · apply (le_star_val_iff s id s a b).mpr
    intro l
    by_cases hl : l ≤ a
    · have : id a l = a - l := by
        rw [id]
        simp only [Int.sub_nonneg, hl, sup_of_le_left]
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
  apply (SF_ext _ _).mpr
  intro a b
  apply le_antisymm
  · apply (ge_star_val_iff s s id a b).mpr
    use b
    have : id b b = 0 := by
      rw [id]
      simp
    simp only [this, add_zero, ge_iff_le, le_refl]
  · apply (le_star_val_iff s s id a b).mpr
    intro l
    by_cases hl : l ≤ b
    · have : id l b = 0 := by
        rw [id]; simp; omega
      rw [this, add_zero]
      apply s.nondec (le_refl a) hl
    · have : id l b = l - b := by
        rw [id]
        exact max_eq_left (by omega)
      rw [this]
      rw [s.s_eq a b, s.s_eq a l]
      have : s.dual l a ≥ s.dual b a := by
        apply s.dual.nondec (by omega) (le_refl a)
      omega

noncomputable instance : Monoid SlipFace where
  mul := star
  one := id
  mul_assoc := star_assoc
  one_mul := id_mul
  mul_one := mul_id

/-! ### The contraction operations `◃` and `▹`
This section develops the basic properties of the operations $s \triangleleft t$
and $s \triangleright t$ at the level of slipface functions.
-/

lemma left_contraction_exists (s t : SlipFace) (a b : ℤ) : ∃ m, ∀ l,
  s a l - t.dual b l ≤ s a m - t.dual b m := by
  -- Proof written by Sonnet 4.6.
  obtain ⟨B₁, hB₁⟩ := s.small_b a
  obtain ⟨B₂, hB₂⟩ := t.dual.small_b b
  obtain ⟨U₁, hU₁⟩ := s.large_b a
  obtain ⟨U₂, hU₂⟩ := t.dual.large_b b
  -- Ensure the interval is non-empty by taking max of upper bounds vs min of lower bounds
  let L := min B₁ B₂
  let U := max (max U₁ U₂) L
  have L_le_U : L ≤ U := le_max_right _ _
  have hne : (Finset.Icc L U).Nonempty :=
    ⟨L, Finset.mem_Icc.mpr ⟨le_refl _, L_le_U⟩⟩
  obtain ⟨m, -, hm_max⟩ := Finset.exists_max_image
    (Finset.Icc L U) (fun l => s a l - t.dual b l) hne
  use m
  intro l
  by_cases hlL : l ≤ L
  · -- l is in the left constant regime: f(l) = f(L)
    have hsl : s a l = a - l + s.χ := hB₁ l (le_trans hlL (min_le_left _ _))
    have htl : t.dual b l = b - l + t.dual.χ := hB₂ l (le_trans hlL (min_le_right _ _))
    have hsL : s a L = a - L + s.χ := hB₁ L (min_le_left _ _)
    have htL : t.dual b L = b - L + t.dual.χ := hB₂ L (min_le_right _ _)
    have hm_L := hm_max L (Finset.mem_Icc.mpr ⟨le_refl _, L_le_U⟩)
    omega
  · push Not at hlL
    by_cases hUl : l ≤ U
    · -- l is in the finite interval: directly bounded by argmax
      exact hm_max l (Finset.mem_Icc.mpr ⟨le_of_lt hlL, hUl⟩)
    · push Not at hUl
      -- l is in the right zero regime: f(l) = 0 ≤ f(U) ≤ f(m)
      have hU₁l : U₁ ≤ l :=
        le_trans (le_trans (le_max_left _ _) (le_max_left _ L)) hUl.le
      have hU₂l : U₂ ≤ l :=
        le_trans (le_trans (le_max_right _ _) (le_max_left _ L)) hUl.le
      have hU₁U : U₁ ≤ U := le_trans (le_max_left _ _) (le_max_left _ L)
      have hU₂U : U₂ ≤ U := le_trans (le_max_right _ _) (le_max_left _ L)
      have hs0 : s a l = 0 := hU₁ l hU₁l
      have ht0 : t.dual b l = 0 := hU₂ l hU₂l
      have hsU : s a U = 0 := hU₁ U hU₁U
      have htU : t.dual b U = 0 := hU₂ U hU₂U
      have hm_U := hm_max U (Finset.mem_Icc.mpr ⟨L_le_U, le_refl _⟩)
      omega



/-- The argmax witnessing the left contraction value $s \triangleleft t (a,b)$. -/
noncomputable def lc_wit (s t : SlipFace) (a b : ℤ) : ℤ :=
  Classical.choose (left_contraction_exists s t a b)

/-- The left contraction function
$$
(s \triangleleft t)(a,b) = \max_{\ell \in \mathbb{Z}} \bigl[s(a,\ell) - t^\vee(b,\ell)\bigr].
$$
*Definition 3.7 (`defn:sfAlgebra`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/3.* -/
noncomputable def lc_func (s t : SlipFace) : ℤ → ℤ → ℤ :=
  fun a b => s a (lc_wit s t a b) - t.dual b (lc_wit s t a b)

/-- Every value $s(a,\ell) - t^\vee(b,\ell)$ is at most $s \triangleleft t (a,b)$. -/
lemma lc_val_ge (s t : SlipFace) (a b l : ℤ) : s a l - t.dual b l ≤ lc_func s t a b :=
  Classical.choose_spec (left_contraction_exists s t a b) l

/-- The left contraction is nonnegative, since for `l ≫ 0` both terms in the
maximizing expression vanish. -/
lemma lc_func_nonneg (s t : SlipFace) (a b : ℤ) : 0 ≤ lc_func s t a b := by
  -- Proof written by GPT 5.5.
  obtain ⟨U₁, hU₁⟩ := s.large_b a
  obtain ⟨U₂, hU₂⟩ := t.dual.large_b b
  let l := max U₁ U₂
  have hs0 : s a l = 0 := hU₁ l (le_max_left _ _)
  have ht0 : t.dual b l = 0 := hU₂ l (le_max_right _ _)
  have hmax := lc_val_ge s t a b l
  rw [hs0, ht0] at hmax
  omega

/-- The left contraction function $s \triangleleft t$ satisfies `D_props`.
*Proposition 3.9 (`prop:sfAlgebraDefined`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), proof component for part 2/5.* -/
lemma D_props_of_lc_func (s t : SlipFace) : D_props (lc_func s t) := by
  -- Proof written by GPT 5.5.
  constructor
  · intro a b
    let l := lc_wit s t a b
    change s a l - t.dual b l ≤ lc_func s t (a+1) b
    have hmax : s (a+1) l - t.dual b l ≤ lc_func s t (a+1) b :=
      lc_val_ge s t (a+1) b l
    have hstep : s a l ≤ s (a+1) l := (s.a_step a l).1
    omega
  · intro a b
    let l := lc_wit s t a (b+1)
    change s a l - t.dual (b+1) l ≤ lc_func s t a b
    have hmax : s a l - t.dual b l ≤ lc_func s t a b :=
      lc_val_ge s t a b l
    have hstep : t.dual b l ≤ t.dual (b+1) l := (t.dual.a_step b l).1
    omega
  · intro a
    suffices hEventuallyNonpos : ∃ B, ∀ b ≥ B, ∀ l,
        s a l - t.dual b l ≤ 0 by
      obtain ⟨B, hB⟩ := hEventuallyNonpos
      use B
      intro b hb
      apply le_antisymm
      · let l := lc_wit s t a b
        change s a l - t.dual b l ≤ 0
        exact hB b hb l
      · exact lc_func_nonneg s t a b
    -- Paper proof: for fixed `a`, consider
    -- `L(a,b) = {l | s(a,l) > t.dual(b,l)}`.  The sets shrink as `b`
    -- increases, `L(a,b₀)` is finite once `s.χ + t.χ + a - b₀ ≤ 0`, and
    -- each individual `l` eventually leaves the set by the large-`a` behavior
    -- of `t.dual`.
    obtain ⟨L₀, hL₀⟩ := s.small_b a
    obtain ⟨U₀, hU₀⟩ := s.large_b a
    let L := L₀
    let U := max U₀ L
    let middle := Finset.Icc L U
    have hmiddle_nonempty : middle.Nonempty := by
      refine ⟨L, ?_⟩
      simp only [Finset.mem_Icc, le_refl, le_sup_right, and_self, middle, U]
    let middleBounds := middle.image (fun l => s a l + l + t.χ)
    have hbounds_nonempty : middleBounds.Nonempty := hmiddle_nonempty.image _
    let M := middleBounds.max' hbounds_nonempty
    use max (a + s.χ + t.χ) M
    intro b hb l
    have hb_left : a + s.χ + t.χ ≤ b := by
      exact le_trans (le_max_left _ _) hb
    have hb_middle : M ≤ b := by
      exact le_trans (le_max_right _ _) hb
    have htd_ge : t.dual b l ≥ b - l - t.χ := by
      change t.dual b l ≥ b - l + t.dual.χ
      exact t.dual.ge_diff b l
    by_cases hl_left : l ≤ L
    · have hs : s a l = a - l + s.χ := hL₀ l hl_left
      omega
    · push Not at hl_left
      by_cases hl_right : U ≤ l
      · have hU₀_le_l : U₀ ≤ l := le_trans (le_max_left U₀ L) hl_right
        have hs : s a l = 0 := hU₀ l hU₀_le_l
        have ht_nonneg : t.dual b l ≥ 0 := t.dual.nonneg b l
        omega
      · push Not at hl_right
        have hl_mem : l ∈ middle := by
          simp only [Finset.mem_Icc, middle]
          omega
        have hval_mem : s a l + l + t.χ ∈ middleBounds := by
          exact Finset.mem_image.mpr ⟨l, hl_mem, rfl⟩
        have hval_le_M : s a l + l + t.χ ≤ M := by
          exact Finset.le_max' middleBounds (s a l + l + t.χ) hval_mem
        omega
  · intro b
    suffices hEventuallyNonpos : ∃ A, ∀ a ≤ A, ∀ l,
        s a l - t.dual b l ≤ 0 by
      obtain ⟨A, hA⟩ := hEventuallyNonpos
      use A
      intro a ha
      apply le_antisymm
      · let l := lc_wit s t a b
        change s a l - t.dual b l ≤ 0
        exact hA a ha l
      · exact lc_func_nonneg s t a b
    -- Paper proof, with `a` moving left: `L(a-1,b) ⊆ L(a,b)`, the initial
    -- bad set is finite once `s.χ + t.χ + a - b ≤ 0`, and each fixed `l`
    -- eventually leaves because `s(a,l) = 0` for `a ≪ 0`.
    let A₀ := b - t.χ - s.χ
    obtain ⟨Lₛ, hLₛ⟩ := s.small_b A₀
    obtain ⟨Uₛ, hUₛ⟩ := s.large_b A₀
    obtain ⟨Lₜ, hLₜ⟩ := t.dual.small_b b
    let L := min Lₛ Lₜ
    let U := max Uₛ L
    let middle := Finset.Icc L U
    have hmiddle_nonempty : middle.Nonempty := by
      refine ⟨L, ?_⟩
      simp only [Finset.mem_Icc, le_refl, le_sup_right, and_self, middle, U]
    let cutoffs := middle.image (fun l => Classical.choose (s.small_a l))
    have hcutoffs_nonempty : cutoffs.Nonempty := hmiddle_nonempty.image _
    let A₁ := cutoffs.min' hcutoffs_nonempty
    use min A₀ A₁
    intro a ha l
    have ha_A₀ : a ≤ A₀ := le_trans ha (min_le_left _ _)
    have hs_le_A₀ : s a l ≤ s A₀ l := by
      exact s.nondec ha_A₀ (le_refl l)
    by_cases hl_left : l ≤ L
    · have hsA₀ : s A₀ l = A₀ - l + s.χ :=
        hLₛ l (le_trans hl_left (min_le_left _ _))
      have ht : t.dual b l = b - l - t.χ := by
        change t.dual b l = b - l + t.dual.χ
        exact hLₜ l (le_trans hl_left (min_le_right _ _))
      omega
    · push Not at hl_left
      by_cases hl_right : U ≤ l
      · have hUₛ_le_l : Uₛ ≤ l := le_trans (le_max_left Uₛ L) hl_right
        have hsA₀ : s A₀ l = 0 := hUₛ l hUₛ_le_l
        have ht_nonneg : t.dual b l ≥ 0 := t.dual.nonneg b l
        omega
      · push Not at hl_right
        have hl_mem : l ∈ middle := by
          simp only [Finset.mem_Icc, middle]
          omega
        let A_l := Classical.choose (s.small_a l)
        have hAl_mem : A_l ∈ cutoffs := by
          exact Finset.mem_image.mpr ⟨l, hl_mem, rfl⟩
        have hA₁_le_Al : A₁ ≤ A_l := by
          exact Finset.min'_le cutoffs A_l hAl_mem
        have ha_Al : a ≤ A_l := by
          exact le_trans ha (le_trans (min_le_right A₀ A₁) hA₁_le_Al)
        have hs0 : s a l = 0 := by
          exact Classical.choose_spec (s.small_a l) a ha_Al
        have ht_nonneg : t.dual b l ≥ 0 := t.dual.nonneg b l
        omega

lemma right_contraction_exists (s t : SlipFace) (a b : ℤ) : ∃ m, ∀ l,
    t l b - s.dual l a ≤ t m b - s.dual m a := by
  obtain ⟨A₁, hA₁⟩ := t.small_a b
  obtain ⟨A₂, hA₂⟩ := s.dual.small_a a
  obtain ⟨U₁, hU₁⟩ := t.large_a b
  obtain ⟨U₂, hU₂⟩ := s.dual.large_a a
  -- Ensure the interval is non-empty by taking max of upper bounds vs min of lower bounds
  let L := min A₁ A₂
  let U := max (max U₁ U₂) L
  have L_le_U : L ≤ U := le_max_right _ _
  have hne : (Finset.Icc L U).Nonempty :=
    ⟨L, Finset.mem_Icc.mpr ⟨le_refl _, L_le_U⟩⟩
  obtain ⟨m, -, hm_max⟩ := Finset.exists_max_image
    (Finset.Icc L U) (fun l => t l b - s.dual l a) hne
  use m
  intro l
  by_cases hlL : l ≤ L
  · -- l is in the left zero regime: g(l) = 0 = g(L) ≤ g(m)
    have htl : t l b = 0 := hA₁ l (le_trans hlL (min_le_left _ _))
    have hsl : s.dual l a = 0 := hA₂ l (le_trans hlL (min_le_right _ _))
    have htL : t L b = 0 := hA₁ L (min_le_left _ _)
    have hsL : s.dual L a = 0 := hA₂ L (min_le_right _ _)
    have hm_L := hm_max L (Finset.mem_Icc.mpr ⟨le_refl _, L_le_U⟩)
    omega
  · push Not at hlL
    by_cases hUl : l ≤ U
    · -- l is in the finite interval: directly bounded by argmax
      exact hm_max l (Finset.mem_Icc.mpr ⟨le_of_lt hlL, hUl⟩)
    · push Not at hUl
      -- l is in the right constant regime: g(l) = g(U) ≤ g(m)
      have hU₁l : U₁ ≤ l :=
        le_trans (le_trans (le_max_left _ _) (le_max_left _ L)) hUl.le
      have hU₂l : U₂ ≤ l :=
        le_trans (le_trans (le_max_right _ _) (le_max_left _ L)) hUl.le
      have hU₁U : U₁ ≤ U := le_trans (le_max_left _ _) (le_max_left _ L)
      have hU₂U : U₂ ≤ U := le_trans (le_max_right _ _) (le_max_left _ L)
      have htl : t l b = l - b + t.χ := hU₁ l hU₁l
      have hsl : s.dual l a = l - a + s.dual.χ := hU₂ l hU₂l
      have htU : t U b = U - b + t.χ := hU₁ U hU₁U
      have hsU : s.dual U a = U - a + s.dual.χ := hU₂ U hU₂U
      have hm_U := hm_max U (Finset.mem_Icc.mpr ⟨L_le_U, le_refl _⟩)
      omega

/-- The argmax witnessing the right contraction value $s \triangleright t (a,b)$. -/
noncomputable def rc_wit (s t : SlipFace) (a b : ℤ) : ℤ :=
  Classical.choose (right_contraction_exists s t a b)

/-- The right contraction function
$$
(s \triangleright t)(a,b) = \max_{\ell \in \mathbb{Z}} \bigl[t(\ell,b) - s^\vee(\ell,a)\bigr].
$$
*Definition 3.7 (`defn:sfAlgebra`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 3/3.* -/
noncomputable def rc_func (s t : SlipFace) : ℤ → ℤ → ℤ :=
  fun a b => t (rc_wit s t a b) b - s.dual (rc_wit s t a b) a

/-- Every value $t(\ell,b) - s^\vee(\ell,a)$ is at most $s \triangleright t (a,b)$. -/
lemma rc_val_ge (s t : SlipFace) (a b l : ℤ) : t l b - s.dual l a ≤ rc_func s t a b :=
  Classical.choose_spec (right_contraction_exists s t a b) l

/-- The right contraction is nonnegative, since for `l ≪ 0` both terms in the
maximizing expression vanish. -/
lemma rc_func_nonneg (s t : SlipFace) (a b : ℤ) : 0 ≤ rc_func s t a b := by
  -- Proof written by GPT 5.5.
  obtain ⟨A₁, hA₁⟩ := t.small_a b
  obtain ⟨A₂, hA₂⟩ := s.dual.small_a a
  let l := min A₁ A₂
  have ht0 : t l b = 0 := hA₁ l (min_le_left _ _)
  have hs0 : s.dual l a = 0 := hA₂ l (min_le_right _ _)
  have hmax := rc_val_ge s t a b l
  rw [ht0, hs0] at hmax
  omega

/-- The right contraction function $s \triangleright t$ satisfies `D_props`.
*Proposition 3.9 (`prop:sfAlgebraDefined`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), proof component for part 3/5.* -/
lemma D_props_of_rc_func (s t : SlipFace) : D_props (rc_func s t) := by
  -- Proof written by GPT 5.5.
  constructor
  · intro a b
    let l := rc_wit s t a b
    change t l b - s.dual l a ≤ rc_func s t (a+1) b
    have hmax : t l b - s.dual l (a+1) ≤ rc_func s t (a+1) b :=
      rc_val_ge s t (a+1) b l
    have hstep : s.dual l (a+1) ≤ s.dual l a := (s.dual.b_step l a).1
    omega
  · intro a b
    let l := rc_wit s t a (b+1)
    change t l (b+1) - s.dual l a ≤ rc_func s t a b
    have hmax : t l b - s.dual l a ≤ rc_func s t a b :=
      rc_val_ge s t a b l
    have hstep : t l (b+1) ≤ t l b := (t.b_step l b).1
    omega
  · intro a
    suffices hEventuallyNonpos : ∃ B, ∀ b ≥ B, ∀ l,
        t l b - s.dual l a ≤ 0 by
      obtain ⟨B, hB⟩ := hEventuallyNonpos
      use B
      intro b hb
      apply le_antisymm
      · let l := rc_wit s t a b
        change t l b - s.dual l a ≤ 0
        exact hB b hb l
      · exact rc_func_nonneg s t a b
    -- Paper proof, with `b` moving right: the positive set is finite after
    -- choosing an initial `b`, and each fixed middle `l` eventually leaves
    -- because `t(l,b) = 0` for `b ≫ 0`.
    let B₀ := a + s.χ + t.χ
    obtain ⟨Lₜ, hLₜ⟩ := t.small_a B₀
    obtain ⟨Uₜ, hUₜ⟩ := t.large_a B₀
    obtain ⟨Lₛ, hLₛ⟩ := s.dual.small_a a
    obtain ⟨Uₛ, hUₛ⟩ := s.dual.large_a a
    let L := min Lₜ Lₛ
    let U := max (max Uₜ Uₛ) L
    let middle := Finset.Icc L U
    have hmiddle_nonempty : middle.Nonempty := by
      refine ⟨L, ?_⟩
      simp only [Int.max_assoc, Finset.mem_Icc, le_refl, le_sup_iff, or_true, and_self, middle, U]
    let cutoffs := middle.image (fun l => Classical.choose (t.large_b l))
    have hcutoffs_nonempty : cutoffs.Nonempty := hmiddle_nonempty.image _
    let B₁ := cutoffs.max' hcutoffs_nonempty
    use max B₀ B₁
    intro b hb l
    have hb_B₀ : B₀ ≤ b := le_trans (le_max_left _ _) hb
    have hb_B₁ : B₁ ≤ b := le_trans (le_max_right _ _) hb
    have ht_le_B₀ : t l b ≤ t l B₀ := t.nondec (le_refl l) hb_B₀
    by_cases hl_left : l ≤ L
    · have htB₀ : t l B₀ = 0 := hLₜ l (le_trans hl_left (min_le_left _ _))
      have hs_nonneg : s.dual l a ≥ 0 := s.dual.nonneg l a
      omega
    · push Not at hl_left
      by_cases hl_right : U ≤ l
      · have hUₜ_le_l : Uₜ ≤ l :=
          le_trans (le_trans (le_max_left Uₜ Uₛ) (le_max_left _ L)) hl_right
        have hUₛ_le_l : Uₛ ≤ l :=
          le_trans (le_trans (le_max_right Uₜ Uₛ) (le_max_left _ L)) hl_right
        have htB₀ : t l B₀ = l - B₀ + t.χ := hUₜ l hUₜ_le_l
        have hs : s.dual l a = l - a - s.χ := by
          change s.dual l a = l - a + s.dual.χ
          exact hUₛ l hUₛ_le_l
        omega
      · push Not at hl_right
        have hl_mem : l ∈ middle := by
          simp only [Finset.mem_Icc, middle]
          omega
        let B_l := Classical.choose (t.large_b l)
        have hBl_mem : B_l ∈ cutoffs := by
          exact Finset.mem_image.mpr ⟨l, hl_mem, rfl⟩
        have hBl_le_B₁ : B_l ≤ B₁ := by
          exact Finset.le_max' cutoffs B_l hBl_mem
        have hBl_le_b : B_l ≤ b := le_trans hBl_le_B₁ hb_B₁
        have ht0 : t l b = 0 := by
          exact Classical.choose_spec (t.large_b l) b hBl_le_b
        have hs_nonneg : s.dual l a ≥ 0 := s.dual.nonneg l a
        omega
  · intro b
    suffices hEventuallyNonpos : ∃ A, ∀ a ≤ A, ∀ l,
        t l b - s.dual l a ≤ 0 by
      obtain ⟨A, hA⟩ := hEventuallyNonpos
      use A
      intro a ha
      apply le_antisymm
      · let l := rc_wit s t a b
        change t l b - s.dual l a ≤ 0
        exact hA a ha l
      · exact rc_func_nonneg s t a b
    -- Paper proof, with `a` moving left: the left tail is zero, the right
    -- tail is controlled by the line inequality, and the middle interval is
    -- finite.
    obtain ⟨L₀, hL₀⟩ := t.small_a b
    obtain ⟨U₀, hU₀⟩ := t.large_a b
    let L := L₀
    let U := max U₀ L
    let middle := Finset.Icc L U
    have hmiddle_nonempty : middle.Nonempty := by
      refine ⟨L, ?_⟩
      simp only [Finset.mem_Icc, le_refl, le_sup_right, and_self, middle, U]
    let middleBounds := middle.image (fun l => l - s.χ - t l b)
    have hbounds_nonempty : middleBounds.Nonempty := hmiddle_nonempty.image _
    let A := middleBounds.min' hbounds_nonempty
    use min (b - s.χ - t.χ) A
    intro a ha l
    have ha_right : a ≤ b - s.χ - t.χ := le_trans ha (min_le_left _ _)
    have ha_middle : a ≤ A := le_trans ha (min_le_right _ _)
    have hsd_ge : s.dual l a ≥ l - a - s.χ := by
      change s.dual l a ≥ l - a + s.dual.χ
      exact s.dual.ge_diff l a
    by_cases hl_left : l ≤ L
    · have ht : t l b = 0 := hL₀ l hl_left
      have hs_nonneg : s.dual l a ≥ 0 := s.dual.nonneg l a
      omega
    · push Not at hl_left
      by_cases hl_right : U ≤ l
      · have hU₀_le_l : U₀ ≤ l := le_trans (le_max_left U₀ L) hl_right
        have ht : t l b = l - b + t.χ := hU₀ l hU₀_le_l
        omega
      · push Not at hl_right
        have hl_mem : l ∈ middle := by
          simp only [Finset.mem_Icc, middle]
          omega
        have hval_mem : l - s.χ - t l b ∈ middleBounds := by
          exact Finset.mem_image.mpr ⟨l, hl_mem, rfl⟩
        have hA_le_val : A ≤ l - s.χ - t l b := by
          exact Finset.min'_le middleBounds (l - s.χ - t l b) hval_mem
        omega

/-- The left contraction is dual to the right contraction.
*Proposition 3.9 (`prop:sfAlgebraDefined`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), proof component for part 5/5.* -/
lemma lc_rc_dual_eq (s t : SlipFace) (a b : ℤ) :
    lc_func s t a b - rc_func t.dual s.dual b a = a - b + s.χ + t.χ := by
  -- Proof written by GPT 5.5.
  let C := a - b + s.χ + t.χ
  suffices lc_func s t a b ≤ rc_func t.dual s.dual b a + C ∧
      rc_func t.dual s.dual b a + C ≤ lc_func s t a b by
    omega
  constructor
  · let l := lc_wit s t a b
    change s a l - t.dual b l ≤ rc_func t.dual s.dual b a + C
    have hmax : s.dual l a - t l b ≤ rc_func t.dual s.dual b a := by
      have h := rc_val_ge t.dual s.dual b a l
      rwa [SlipFace.dual_dual t] at h
    linarith [s.s_eq a l, t.s'_eq b l, hmax]
  · let l := rc_wit t.dual s.dual b a
    change s.dual l a - (t.dual).dual l b + C ≤ lc_func s t a b
    have htdd : (t.dual).dual l b = t l b := by
      rw [SlipFace.dual_dual t]
    have hmax : s a l - t.dual b l ≤ lc_func s t a b :=
      lc_val_ge s t a b l
    linarith [s.s_eq a l, t.s'_eq b l, htdd, hmax]

/-- The function `lc_func s t` satisfies the slipface axioms and therefore
comes from a slipface. *Proposition 3.9 (`prop:sfAlgebraDefined`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/5.* -/
lemma lc_exists (s t : SlipFace) : ∃ p : SlipFace,
    ((p.func = lc_func s t ∧ p.χ = s.χ + t.χ)
    ∧ p.dual.func = rc_func t.dual s.dual) := by
  -- Proof written by GPT 5.5.
  let P := lc_func s t
  let P' := rc_func t.dual s.dual
  let χ := s.χ + t.χ
  have hdual : ∀ a b : ℤ, P a b - P' b a = a - b + χ := by
    intro a b
    rw [lc_rc_dual_eq s t a b]
    omega
  have h := sf_of_D_props hdual
  suffices D_props P ∧ D_props P' by
    exact h this
  exact ⟨D_props_of_lc_func s t, D_props_of_rc_func t.dual s.dual⟩

/-- The left contraction of two slipfaces, obtained from the maximum formula
`lc_func`. *Proposition 3.9 (`prop:sfAlgebraDefined`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/5.* -/
noncomputable def left_contract (s t : SlipFace) : SlipFace :=
  Classical.choose (lc_exists s t)

infixl:70 " ◃ " => left_contract

lemma lc_func_eq (s t : SlipFace) : (s ◃ t).func = lc_func s t := by
  have h := lc_exists s t
  exact (Classical.choose_spec h).1.1

lemma lc_wit_spec (s t : SlipFace) (a b : ℤ) :
    (s ◃ t) a b = s a (lc_wit s t a b) - t.dual b (lc_wit s t a b) := by
  rw [lc_func_eq]
  rfl

@[simp] lemma chi_lc (s t : SlipFace) : (s ◃ t).χ = s.χ + t.χ := by
  have h := lc_exists s t
  exact (Classical.choose_spec h).1.2

/-- The right contraction of two slipfaces, defined by duality from left
contraction. *Proposition 3.9 (`prop:sfAlgebraDefined`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 3/5.* -/
noncomputable def right_contract (s t : SlipFace) : SlipFace :=
  (t.dual ◃ s.dual).dual

infixr:70 " ▹ " => right_contract

lemma rc_func_eq (s t : SlipFace) : (s ▹ t).func = rc_func s t := by
  dsimp [right_contract]
  calc
    (t.dual ◃ s.dual).dual.func = rc_func s.dual.dual t.dual.dual :=
      (Classical.choose_spec (lc_exists t.dual s.dual)).2
    _ = rc_func s t := by rw [SlipFace.dual_dual s, SlipFace.dual_dual t]

lemma rc_wit_spec (s t : SlipFace) (a b : ℤ) :
    (s ▹ t) a b = t (rc_wit s t a b) b - s.dual (rc_wit s t a b) a := by
  rw [rc_func_eq]
  rfl

@[simp] lemma chi_rc (s t : SlipFace) : (s ▹ t).χ = s.χ + t.χ := by
  dsimp [right_contract, SlipFace.dual]
  rw [chi_lc]
  dsimp [SlipFace.dual]
  omega

/-- The stated left/right contraction duality.
*Proposition 3.9 (`prop:sfAlgebraDefined`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 5/5.* -/
@[simp] lemma left_contract_dual (s t : SlipFace) :
    (s ◃ t).dual = t.dual ▹ s.dual := by
  dsimp [right_contract]
  rw [SlipFace.dual_dual s, SlipFace.dual_dual t]

/-- The corresponding right/left contraction duality, obtained by applying the
left/right duality to dual slipfaces.
*Consequence of Proposition 3.9 (`prop:sfAlgebraDefined`) in
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 5/5.* -/
@[simp] lemma right_contract_dual (s t : SlipFace) :
    (s ▹ t).dual = t.dual ◃ s.dual := by
  dsimp [right_contract]
  rw [SlipFace.dual_dual]

/- A small set on which witnesses to the value $s \star t (a,b)$ always occur.
*Lemma 3.12 (`lem:setL`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/5.* -/
def bend_set (t : SlipFace) (b : ℤ) : Set ℤ :=
  {l : ℤ | t (l-1) b = t l b ∧ t l b ≠ t (l+1) b}

/- *Lemma 3.12 (`lem:setL`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/5.* -/
lemma bend_set_finite (t : SlipFace) (b : ℤ) : Finite (bend_set t b) := by
  obtain ⟨A1, hA1⟩ := t.large_a b
  obtain ⟨A0, hA0⟩ := t.small_a b
  have : bend_set t b ⊆ Finset.Icc A0 A1 := by
    rintro l ⟨hl_left,hl_right⟩
    rw [Finset.mem_coe, Finset.mem_Icc]
    constructor
    · contrapose! hl_right with l_lt_A0
      rw [hA0 l (by omega), hA0 (l+1) (by omega)]
    · contrapose! hl_left with A1_lt_l
      rw [hA1 (l-1) (by omega), hA1 l (by omega)]
      omega
  apply Set.Finite.subset _ this
  apply Finset.finite_toSet

lemma bend_set_witness_helper (s t : SlipFace) (a b l : ℤ) (hl : t l b ≠ t (l + 1) b) :
  ∃ m : ℤ, t (m-1) b = t m b ∧ t m b ≠ t (m+1) b ∧ s a m + t m b ≤ s a l + t l b := by
  by_cases h : t (l-1) b = t l b
  · use l
  have hl' : t (l-1) b ≠ t ((l-1)+1) b := by
    contrapose! h with hl'
    rw [hl']
    congr
    omega
  obtain ⟨m, ⟨teq, tneq, sumle⟩⟩ := bend_set_witness_helper s t a b (l-1) hl'
  use m, teq, tneq
  apply le_trans sumle
  have hs_step := s.b_step a (l-1)
  have ht_step := t.a_step (l-1) b
  have hs_le : s a (l-1) ≤ s a l + 1 := by
    apply le_of_le_of_eq hs_step.2
    congr; omega
  have ht_eq : t l b = t (l-1) b + 1 := by
    have hpred_succ : l - 1 + 1 = l := by omega
    rw [hpred_succ] at ht_step
    omega
  omega
termination_by (t l b).toNat
decreasing_by
  simp_wf
  have ht_step := t.a_step (l - 1) b
  have hpred_succ : l - 1 + 1 = l := by omega
  rw [hpred_succ] at ht_step
  have ht_nonneg : 0 ≤ t (l - 1) b := t.nonneg (l - 1) b
  omega

/- *Lemma 3.12 (`lem:setL`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 3/5.* -/
lemma bend_set_witness (s t : SlipFace) (a b : ℤ) :
  ∃ l ∈ bend_set t b, (s ⋆ t) a b = s a l + t l b := by
  -- Proof written by GPT 5.5.
  let v := SlipValley s t a b
  have hM_right : t v.M b ≠ t (v.M + 1) b := by
    intro ht_eq
    have hstrict : v.f (v.M + 1) > v.f v.M := (v.M_spec (v.M + 1)).2 (by omega)
    have hs_step : s a (v.M + 1) ≤ s a v.M := (s.b_step a v.M).1
    have hle : v.f (v.M + 1) ≤ v.f v.M := by
      change s a (v.M + 1) + t (v.M + 1) b ≤ s a v.M + t v.M b
      omega
    omega
  obtain ⟨m, ⟨hm_left, hm_right, hm_le⟩⟩ :=
    bend_set_witness_helper s t a b v.M hM_right
  use m
  constructor
  · exact ⟨hm_left, hm_right⟩
  · have hstarM : (s ⋆ t) a b = s a v.M + t v.M b := by
      rw [star_func_eq]
      exact Eq.symm v.f_M
    have hM_le_m : s a v.M + t v.M b ≤ s a m + t m b := by
      exact (v.M_spec m).1
    have hm_eq : s a m + t m b = s a v.M + t v.M b := le_antisymm hm_le hM_le_m
    rw [hstarM, hm_eq]

lemma bend_set_witness_lc_right_helper (s t : SlipFace) (a b l : ℤ)
    (hmax : ∀ n, s a n - t.dual b n ≤ s a l - t.dual b l) :
    ∃ m : ℤ, t m b ≠ t (m+1) b ∧
      s a l - t.dual b l ≤ s a m - t.dual b m := by
  -- Proof written by GPT 5.5.
  by_cases hright : t l b = t (l+1) b
  · have hdual : t.dual b (l+1) = t.dual b l - 1 := by
      rw [t.s'_eq b (l+1), t.s'_eq b l, hright]
      omega
    have hs_step := s.b_step a l
    have hle_next : s a l - t.dual b l ≤ s a (l+1) - t.dual b (l+1) := by
      omega
    have hge_next : s a (l+1) - t.dual b (l+1) ≤ s a l - t.dual b l :=
      hmax (l+1)
    have hs_drop : s a (l+1) = s a l - 1 := by
      omega
    have hmax_next :
        ∀ n, s a n - t.dual b n ≤ s a (l+1) - t.dual b (l+1) := by
      intro n
      have hn := hmax n
      omega
    obtain ⟨m, hm_right, hm_le⟩ :=
      bend_set_witness_lc_right_helper s t a b (l+1) hmax_next
    use m, hm_right
    exact le_trans hle_next hm_le
  · use l, hright
termination_by (s a l).toNat
decreasing_by
  simp_wf
  have hnonneg : 0 ≤ s a (l+1) := s.nonneg a (l+1)
  omega

lemma bend_set_witness_lc_helper (s t : SlipFace) (a b l : ℤ)
    (hl : t l b ≠ t (l + 1) b) :
    ∃ m : ℤ, t (m-1) b = t m b ∧ t m b ≠ t (m+1) b ∧
      s a l - t.dual b l ≤ s a m - t.dual b m := by
  -- Proof written by GPT 5.5.
  by_cases h : t (l-1) b = t l b
  · use l, h, hl
  have hl' : t (l-1) b ≠ t ((l-1)+1) b := by
    contrapose! h with hl'
    rw [hl']
    congr
    omega
  obtain ⟨m, hm_left, hm_right, hm_le⟩ :=
    bend_set_witness_lc_helper s t a b (l-1) hl'
  use m, hm_left, hm_right
  have hs_step := s.b_step a (l-1)
  have ht_step := t.a_step (l-1) b
  have ht_eq : t l b = t (l-1) b + 1 := by
    have hpred_succ : l - 1 + 1 = l := by omega
    rw [hpred_succ] at ht_step
    omega
  have hdual : t.dual b (l-1) = t.dual b l := by
    rw [t.s'_eq b (l-1), t.s'_eq b l, ht_eq]
    omega
  have hs_le : s a l ≤ s a (l-1) := by
    have hpred_succ : l - 1 + 1 = l := by omega
    rw [hpred_succ] at hs_step
    exact hs_step.1
  have hcurr_prev : s a l - t.dual b l ≤ s a (l-1) - t.dual b (l-1) := by
    rw [hdual]
    omega
  exact le_trans hcurr_prev hm_le
termination_by (t l b).toNat
decreasing_by
  simp_wf
  have ht_step := t.a_step (l - 1) b
  have hpred_succ : l - 1 + 1 = l := by omega
  rw [hpred_succ] at ht_step
  have ht_nonneg : 0 ≤ t (l - 1) b := t.nonneg (l - 1) b
  omega

/- *Lemma 3.12 (`lem:setL`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 4/5.* -/
lemma bend_set_witness_lc (s t : SlipFace) (a b : ℤ) :
    ∃ l ∈ bend_set t b, (s ◃ t) a b = s a l - t.dual b l := by
  -- Proof written by GPT 5.5.
  let l := lc_wit s t a b
  have hmax : ∀ n, s a n - t.dual b n ≤ s a l - t.dual b l := by
    intro n
    change s a n - t.dual b n ≤ s a (lc_wit s t a b) - t.dual b (lc_wit s t a b)
    exact lc_val_ge s t a b n
  obtain ⟨r, hr_right, hlr⟩ := bend_set_witness_lc_right_helper s t a b l hmax
  obtain ⟨m, hm_left, hm_right, hrm⟩ := bend_set_witness_lc_helper s t a b r hr_right
  use m
  constructor
  · exact ⟨hm_left, hm_right⟩
  · rw [lc_wit_spec]
    apply le_antisymm
    · exact le_trans hlr hrm
    · exact hmax m

/-- The $\star$ operation is Bruhat-increasing in both arguments.
*Lemma 3.8 (`lem:compatLeq`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/3.* -/
lemma star_mono {s₁ s₂ t₁ t₂ : SlipFace}
    (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) :
    s₁ ⋆ t₁ ≤ s₂ ⋆ t₂ := by
  -- Proof written by GPT 5.5.
  intro a b
  apply (le_star_val_iff (s₁ ⋆ t₁) s₂ t₂ a b).mpr
  intro l
  have hval : (s₁ ⋆ t₁) a b ≤ s₁ a l + t₁ l b := star_val_le s₁ t₁ a b l
  have hsval : s₁ a l ≤ s₂ a l := hs a l
  have htval : t₁ l b ≤ t₂ l b := ht l b
  omega

/-- The contraction `(s, t) ↦ s ◃ t.dual` is increasing in `s` and decreasing in
`t`.
*Lemma 3.8 (`lem:compatLeq`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/3.* -/
lemma left_contract_mono {s₁ s₂ t₁ t₂ : SlipFace}
    (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) :
    s₁ ◃ t₂.dual ≤ s₂ ◃ t₁.dual := by
  -- Proof written by GPT 5.5.
  intro a b
  let l := lc_wit s₁ t₂.dual a b
  rw [lc_wit_spec]
  change s₁ a l - (t₂.dual).dual b l ≤ (s₂ ◃ t₁.dual) a b
  have hmax : s₂ a l - t₁ b l ≤ (s₂ ◃ t₁.dual) a b := by
    rw [lc_func_eq]
    have h := lc_val_ge s₂ t₁.dual a b l
    rwa [SlipFace.dual_dual t₁] at h
  have hsval : s₁ a l ≤ s₂ a l := hs a l
  have htval : t₁ b l ≤ t₂ b l := ht b l
  have htdd : (t₂.dual).dual b l = t₂ b l := by
    rw [SlipFace.dual_dual t₂]
  omega

/-- The contraction `(s, t) ↦ t.dual ▹ s` is increasing in `s` and decreasing in
`t`.
*Lemma 3.8 (`lem:compatLeq`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 3/3.* -/
lemma right_contract_mono {s₁ s₂ t₁ t₂ : SlipFace}
    (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) :
    t₂.dual ▹ s₁ ≤ t₁.dual ▹ s₂ := by
  -- Proof written by GPT 5.5.
  intro a b
  let l := rc_wit t₂.dual s₁ a b
  rw [rc_wit_spec]
  change s₁ l b - (t₂.dual).dual l a ≤ (t₁.dual ▹ s₂) a b
  have hmax : s₂ l b - t₁ l a ≤ (t₁.dual ▹ s₂) a b := by
    rw [rc_func_eq]
    have h := rc_val_ge t₁.dual s₂ a b l
    rwa [SlipFace.dual_dual t₁] at h
  have hsval : s₁ l b ≤ s₂ l b := hs l b
  have htval : t₁ l a ≤ t₂ l a := ht l a
  have htdd : (t₂.dual).dual l a = t₂ l a := by
    rw [SlipFace.dual_dual t₂]
  omega

/-- The left contraction $u \triangleleft t^∨$ as a Bruhat minimum: the minimum
slipface such that $s \star t ≥ u$.
*Lemma 3.10 (`lem:sfOpChar`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/2.* -/
lemma ge_star_iff_ge_left_contract (s t u : SlipFace) :
    s ≥ u ◃ t.dual ↔ s ⋆ t ≥ u := by
  -- Proof written by GPT 5.5.
  constructor
  · intro h a b
    apply (le_star_val_iff u s t a b).mpr
    intro l
    have hcontract : u a b - t l b ≤ (u ◃ t.dual) a l := by
      rw [lc_func_eq]
      have hval := lc_val_ge u t.dual a l b
      rwa [SlipFace.dual_dual t] at hval
    have hs : (u ◃ t.dual) a l ≤ s a l := h a l
    omega
  · intro h a l
    let b := lc_wit u t.dual a l
    rw [lc_wit_spec]
    change u a b - (t.dual).dual l b ≤ s a l
    have hstar : u a b ≤ (s ⋆ t) a b := h a b
    have hval : (s ⋆ t) a b ≤ s a l + t l b := star_val_le s t a b l
    have hdd : (t.dual).dual l b = t l b := by
      rw [SlipFace.dual_dual t]
    omega

/-- The right contraction $s^∨ \triangleright u$ as a Bruhat minimum: the minimum
slipface such that $s \star t ≥ u$.
*Lemma 3.10 (`lem:sfOpChar`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/2.* -/
lemma ge_star_iff_ge_right_contract (s t u : SlipFace) :
    t ≥ s.dual ▹ u ↔ s ⋆ t ≥ u := by
  -- Proof written by GPT 5.5.
  constructor
  · intro h a b
    apply (le_star_val_iff u s t a b).mpr
    intro l
    have hcontract : u a b - s a l ≤ (s.dual ▹ u) l b := by
      rw [rc_func_eq]
      have hval := rc_val_ge s.dual u l b a
      rwa [SlipFace.dual_dual s] at hval
    have ht : (s.dual ▹ u) l b ≤ t l b := h l b
    omega
  · intro h l b
    let a := rc_wit s.dual u l b
    rw [rc_wit_spec]
    change u a b - (s.dual).dual a l ≤ t l b
    have hstar : u a b ≤ (s ⋆ t) a b := h a b
    have hval : (s ⋆ t) a b ≤ s a l + t l b := star_val_le s t a b l
    have hdd : (s.dual).dual a l = s a l := by
      rw [SlipFace.dual_dual s]
    omega

/-- Left contraction associates with the product on the right.
*Lemma 3.11 (`lem:sfAlgebra`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/3.* -/
lemma left_contract_assoc (s t u : SlipFace) :
    (s ◃ t) ◃ u = s ◃ (t ⋆ u) := by
  -- Proof written by GPT 5.5.
  have hmin (v : SlipFace) :
      v ≥ (s ◃ t) ◃ u ↔ v ≥ s ◃ (t ⋆ u) := by
    calc
      v ≥ (s ◃ t) ◃ u ↔ v ⋆ u.dual ≥ s ◃ t := by
        simpa only [SlipFace.dual_dual] using
          (ge_star_iff_ge_left_contract v u.dual (s ◃ t))
      _ ↔ (v ⋆ u.dual) ⋆ t.dual ≥ s := by
        simpa only [SlipFace.dual_dual] using
          (ge_star_iff_ge_left_contract (v ⋆ u.dual) t.dual s)
      _ ↔ v ⋆ (t ⋆ u).dual ≥ s := by
        rw [star_assoc, star_dual]
      _ ↔ v ≥ s ◃ (t ⋆ u) := by
        symm
        simpa only [SlipFace.dual_dual] using
          (ge_star_iff_ge_left_contract v (t ⋆ u).dual s)
  apply le_antisymm
  · exact (hmin (s ◃ (t ⋆ u))).mpr (le_refl _)
  · exact (hmin ((s ◃ t) ◃ u)).mp (le_refl _)

/-- Right contraction associates with the product on the left.
*Lemma 3.11 (`lem:sfAlgebra`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 3/3.* -/
lemma right_contract_assoc (s t u : SlipFace) :
    s ▹ (t ▹ u) = (s ⋆ t) ▹ u := by
  -- Proof written by GPT 5.5.
  have hmin (v : SlipFace) :
      v ≥ s ▹ (t ▹ u) ↔ v ≥ (s ⋆ t) ▹ u := by
    calc
      v ≥ s ▹ (t ▹ u) ↔ s.dual ⋆ v ≥ t ▹ u := by
        simpa only [SlipFace.dual_dual] using
          (ge_star_iff_ge_right_contract s.dual v (t ▹ u))
      _ ↔ t.dual ⋆ (s.dual ⋆ v) ≥ u := by
        simpa only [SlipFace.dual_dual] using
          (ge_star_iff_ge_right_contract t.dual (s.dual ⋆ v) u)
      _ ↔ (s ⋆ t).dual ⋆ v ≥ u := by
        rw [← star_assoc, star_dual]
      _ ↔ v ≥ (s ⋆ t) ▹ u := by
        symm
        simpa only [SlipFace.dual_dual] using
          (ge_star_iff_ge_right_contract (s ⋆ t).dual v u)
  apply le_antisymm
  · exact (hmin ((s ⋆ t) ▹ u)).mpr (le_refl _)
  · exact (hmin (s ▹ (t ▹ u))).mp (le_refl _)

/-! ### The Mixed Difference `Δ`

This section studies the discrete mixed difference `Δ`, its behavior under
duality, and the finite summation identities used later in submodularity
arguments. -/

/-- The mixed difference
$$
\Delta s(a,b) = s(a+1,b) - s(a,b) - s(a+1,b+1) + s(a,b+1).
$$

In Lean this is written `sf.Δ a b`. -/
def Δ (a b : ℤ) : ℤ :=
  sf (a+1) b - sf a b - sf (a+1) (b+1) + sf a (b+1)

/-- Duality preserves the mixed difference `Δ` after swapping the coordinates.
*Equation (18) of [An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
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

/-- Summing `Δ` over a rectangle recovers the corresponding boundary term in
`sf`. *Modification of Equation (17) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227) to a finite sum.* -/
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

/-- A slipface is submodular if $\Delta s(a,b) \ge 0$ for all `a, b`.
*Definition 4.2 (`defn:submodular`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
def submodular : Prop := ∀ a b : ℤ, sf.Δ a b ≥ 0

/-- The set of boxes where the mixed difference `Δ` is equal to `1`. -/
def Γ : Set (ℤ × ℤ) := {(a, b) | sf.Δ a b = 1}

lemma Γ_dual : ∀ (a b : ℤ), (a, b) ∈ sf.Γ ↔ (b, a) ∈ sf.dual.Γ := by
  intro a b
  simp only [Γ, Set.mem_setOf_eq, sf.Δ_dual]

end SlipFace
