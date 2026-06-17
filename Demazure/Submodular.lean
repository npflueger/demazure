/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
import Demazure.AspPerm
import Demazure.Valley
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Submodular slipfaces

This file establishes that a slipface comes from $\mathrm{ASP}$ if and only if it is submodular, and
uses this to define the operations $\star$, $\triangleleft$, and $\triangleright$ on $\mathrm{ASP}$.
It corresponds roughly to Section 4 of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).
-/

/-! ### Submodular slipfaces and recovery of ASP permutations

This section shows that submodular slipfaces are exactly those arising from
ASP permutations. -/

namespace Submodular

private lemma unique_a_helper {s : SlipFace} (hsub : s.submodular)
  (A A' b : ℤ) (hA : ∀ a ≤ A, s a b = 0) (hA' : ∀ a ≥ A', s.dual (b + 1) a = 0) :
  A ≤ A' ∧ ∑ a ∈ Finset.Ico A A', s.Δ a b = 1 := by
  specialize hA A (le_refl A)
  have hbA : s A (b+1) = 0 := by
    have := (s.b_step A b).1
    rw [hA] at this
    exact le_antisymm this (s.nonneg A (b+1))
  have A_le_A' : A ≤ A' := by
    by_contra! h
    have : A' ≤ A - 1 := by linarith
    specialize hA' (A-1) (by linarith)
    have hAb : s.dual b (A-1) = 0 := by
      have := (s.dual.a_step b (A-1)).1
      rw [hA'] at this
      exact le_antisymm this (s.dual.nonneg b (A-1))
    have : s.Δ (A-1) b = -1 := by
      dsimp [SlipFace.Δ]
      have : A - 1 + 1 = A := by omega
      rw [this]
      rw [s.s_eq (A-1) b, s.s_eq (A-1) (b+1)]
      rw [hA', hA, hAb, hbA]
      omega
    linarith [hsub (A-1) b]
  apply And.intro A_le_A'
  suffices s.dual b A' + s A (b+1) = 0 by
    rw [s.sum_a A_le_A', s.s_eq A' b, s.s_eq A' (b+1), hA' A' (le_refl A'), hA]
    linarith
  suffices s.dual b A' = 0 by rwa [hbA, add_zero]
  have := hA' A' (le_refl A')
  have : s.dual b A' ≤ 0 := by
    have := (s.dual.a_step b A').1
    rwa [hA' A' (le_refl A')] at this
  exact le_antisymm this (s.dual.nonneg b A')

private lemma unique_a {s : SlipFace} (hsub : s.submodular) (b : ℤ) :
  ∃! a : ℤ, ⟨a, b⟩ ∈ s.Γ := by
  rcases s.dual.large_b (b+1) with ⟨A', hA'⟩
  rcases s.small_a b with ⟨A, hA⟩
  obtain ⟨A_le_A', h_sum⟩ := unique_a_helper hsub A A' b hA hA'
  have : ∃ a ∈ Finset.Ico A A', ⟨a, b⟩ ∈ s.Γ := by
    by_contra! h
    have : ∀ a ∈ Finset.Ico A A', s.Δ a b = 0 := by
      intro a ha
      have := s.Δ_values a b
      rcases this with (h0 | (h1 | hn))
      · exact h0
      · have mem : ⟨a, b⟩ ∈ s.Γ := by
          simpa [SlipFace.Γ] using h1
        have nmem := h a ha
        contradiction
      · linarith [hsub a b]
    have : (0 : ℤ) = 1 := by rwa [Finset.sum_eq_zero this] at h_sum
    contradiction
  rcases this with ⟨a, ⟨a_Ico, hΓ⟩⟩
  obtain ⟨a_ge_A, a_lt_A'⟩ := Finset.mem_Ico.mp a_Ico
  use a
  constructor
  · simp only; exact hΓ
  intro a' ha'
  let A'new := max A' (a' + 1)
  have A_le_A'new : A' ≤ A'new := by apply Int.le_max_left
  let Anew := min A a'
  have Anew_le_A : Anew ≤ A := by apply Int.min_le_left
  have a'_Ico : a' ∈ Finset.Ico Anew A'new := by
    simp only [Finset.mem_Ico]
    constructor <;> linarith [Int.le_max_right A' (a' + 1), Int.min_le_right A a']
  have a_Ico : a ∈ Finset.Ico Anew A'new := by
    simp only [Finset.mem_Ico]
    constructor <;> linarith
  have hAnew : ∀ a ≤ Anew, s a b = 0 := by
    intro a ha
    have : a ≤ A := by linarith [Anew_le_A]
    exact hA a this
  have hA'new : ∀ a ≥ A'new, s.dual (b + 1) a = 0 := by
    intro a ha
    have : a ≥ A' := by linarith [A_le_A'new]
    exact hA' a this
  obtain ⟨A'new_le_A'new, h_sum⟩ := unique_a_helper hsub Anew A'new b hAnew hA'new
  have : (∑ x ∈ Finset.Ico Anew A'new, s.Δ x b)
    = s.Δ a b + ∑ x ∈ (Finset.Ico Anew A'new \ {a}), s.Δ x b := by
    exact Finset.sum_eq_add_sum_diff_singleton
      (s := Finset.Ico Anew A'new) a (fun x => s.Δ x b)
      (by intro ha; exact (ha a_Ico).elim)
  rw [this] at h_sum
  have sum0 : ∑ x ∈ (Finset.Ico Anew A'new \ {a}), s.Δ x b  = 0 := by
    have : s.Δ a b = 1 := by
      dsimp [SlipFace.Γ] at hΓ
      exact hΓ
    omega
  have : ∀ x ∈ (Finset.Ico Anew A'new \ {a}), s.Δ x b ≥ 0 := by
    intro x hx
    exact hsub x b
  have all0 : ∀ i ∈ Finset.Ico Anew A'new \ {a}, s.Δ i b = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg this).mp sum0
  specialize all0 a'
  by_contra! a'_ne_a
  have : a' ∈ Finset.Ico Anew A'new \ {a} := by
    simp only [Finset.mem_sdiff, Finset.mem_Ico, Finset.mem_singleton]
    constructor
    · simpa using a'_Ico
    · exact a'_ne_a
  have eq0 : s.Δ a' b = 0 := by
    exact all0 this
  have eq1 : s.Δ a' b = 1 := by
    simpa [SlipFace.Γ] using ha'
  rw [eq0] at eq1
  norm_num at eq1

private lemma submodular_dual {s : SlipFace} (hsub : s.submodular) :
    s.dual.submodular := by
  intro a b
  rw [← s.dual.Δ_dual, s.dual_dual]
  exact hsub b a

private lemma unique_b {s : SlipFace} (hsub : s.submodular) (a : ℤ) :
  ∃! b : ℤ, ⟨a, b⟩ ∈ s.Γ := by
  suffices ∃! b : ℤ, ⟨b, a⟩ ∈ s.dual.Γ by
    simpa [s.Γ_dual] using this
  exact unique_a (submodular_dual hsub) a

private noncomputable def asp_func {s : SlipFace} (hsub : s.submodular) : ℤ → ℤ :=
  fun b => (unique_a hsub b).choose

private lemma asp_func_spec {s : SlipFace} (hsub : s.submodular) (a b : ℤ) :
  asp_func hsub b = a ↔ ⟨a, b⟩ ∈ s.Γ := by
  constructor
  · intro eq
    dsimp [asp_func] at eq
    rw [← eq]
    exact (unique_a hsub b).choose_spec.1
  · intro mem
    dsimp [asp_func]
    have := (unique_a hsub b).choose_spec.2 a mem
    rw [this]

private lemma asp_bijective {s : SlipFace} (hsub : s.submodular) :
  (asp_func hsub).Bijective := by
  constructor
  · intro b1 b2 h
    let a1 := (unique_a hsub b1).choose
    let a2 := (unique_a hsub b2).choose
    have mem1 : ⟨a1, b1⟩ ∈ s.Γ := (unique_a hsub b1).choose_spec.1
    have mem2 : ⟨a2, b2⟩ ∈ s.Γ := (unique_a hsub b2).choose_spec.1
    have eq : a1 = a2 := h
    let b := (unique_b hsub a1).choose
    have eq1 : b1 = b :=
      (unique_b hsub a1).choose_spec.2 b1 mem1
    rw [← eq] at mem2
    have eq2 : b2 = b :=
      (unique_b hsub a1).choose_spec.2 b2 mem2
    rw [eq1, eq2]
  · intro a
    let b := (unique_b hsub a).choose
    use b
    have mem : ⟨a, b⟩ ∈ s.Γ := (unique_b hsub a).choose_spec.1
    let a' := (unique_a hsub b).choose
    suffices a = a' by
      dsimp [asp_func]
      rw [this]
    exact (unique_a hsub b).choose_spec.2 a mem

/-- The ASP permutation associated to a submodular slipface. It can be reconstructed from the set
$\Gamma$ in the manner described in Section 4 of [An extended Demazure product](https://arxiv.org/abs/2206.14227). -/
noncomputable def asp {s : SlipFace} (hsub : s.submodular) : AspPerm where
  func := fun b => (unique_a hsub b).choose
  bijective := asp_bijective hsub
  asp := by
    let S := {b : ℤ | b * (asp_func hsub b) < 0}
    suffices S.Finite by exact this
    obtain ⟨B, hB⟩ := s.dual.small_a 0
    obtain ⟨B', hB'⟩ := s.large_b 0
    have b_lt : ∀ b ∈ S, b < max 0 B' := by
      intro b hb
      by_cases b_neg : b < 0
      · exact lt_of_lt_of_le b_neg (le_max_left 0 B')
      have b_nonneg : b ≥ 0 := by linarith
      clear b_neg
      suffices b < B' by
        exact lt_of_lt_of_le this (le_max_right 0 B')
      let a := asp_func hsub b
      have a_neg : a < 0 := by
        by_contra! a_nonneg
        have neg : b * a < 0 := by exact hb
        have nonneg : b * a ≥ 0 := by exact mul_nonneg b_nonneg a_nonneg
        linarith
      have mem : ⟨a, b⟩ ∈ s.Γ := by
        apply (asp_func_spec hsub a b).mp
        rfl
      have h0 : s.Δ a b = 1 := by
        simpa [SlipFace.Γ] using mem
      contrapose! h0 with b_ge_B'
      have s0 : s (a+1) b = 0 := by
        have : s 0 b = 0 := hB' b b_ge_B'
        apply s.zero_below (a' := 0) (b' := b)
        repeat linarith
      have : s.Δ a b = 0 := s.Δ_zero_of_s_zero a b s0
      rw [this]
      norm_num
    have b_ge : ∀ b ∈ S, b ≥ min 0 B := by
      intro b hb
      by_cases b_nonneg : b ≥ 0
      · exact le_trans (min_le_left 0 B) b_nonneg
      have b_neg : b < 0 := by linarith
      clear b_nonneg
      suffices b ≥ B by
        exact le_trans (min_le_right 0 B) this
      let a := asp_func hsub b
      have a_pos : a > 0 := by
        by_contra! a_nonpos
        have nonneg : b * a ≥ 0 := by
          apply mul_nonneg_of_nonpos_of_nonpos (le_of_lt b_neg) a_nonpos
        have neg : b * a < 0 := by exact hb
        linarith
      have mem : ⟨a, b⟩ ∈ s.Γ := by
        apply (asp_func_spec hsub a b).mp
        rfl
      have h0 : s.Δ a b = 1 := by
        simpa [SlipFace.Γ] using mem
      contrapose! h0 with b_lt_B
      have s0 : s.dual (b+1) a = 0 := by
        have : b + 1 ≤ B := by linarith
        have : s.dual (b+1) 0 = 0 := hB (b+1) this
        apply s.dual.zero_below (a' := b+1) (b' := 0)
        repeat linarith
      have : s.Δ a b = 0 := by
        rw [← s.Δ_dual a b]
        apply s.dual.Δ_zero_of_s_zero b a s0
      rw [this]
      norm_num
    have : S ⊆ Set.Ico (min 0 B) (max 0 B') := by
      intro b hb
      have lt := b_lt b hb
      have ge := b_ge b hb
      simp only [Set.mem_Ico, ge, lt, and_self]
    apply Set.Finite.subset _ this
    apply Set.finite_Ico

private lemma asp_spec (s : SlipFace) (hsub : s.submodular) :
  (asp hsub).sf = s := by
  apply (SF_ext _ _).mpr
  intro a b
  let τ := asp hsub
  suffices τ.s = s by
    subst τ
    rw [← this]
    congr
  ext a b
  have : ∃ A ≤ a, s A b = 0 := by
    obtain ⟨A, hA⟩ := s.small_a b
    by_cases h : A ≤ a
    · use A
      exact ⟨h, hA A (le_refl A)⟩
    · use a
      have : a ≤ A := by linarith
      have := hA a this
      exact ⟨le_refl a, this⟩
  obtain ⟨A, hA⟩ := this
  have : ∃ B ≥ b, s a B = 0 := by
    obtain ⟨B, hB⟩ := s.large_b a
    by_cases h : B ≥ b
    · use B
      exact ⟨h, hB B (le_refl B)⟩
    · use b
      have : b ≥ B := by linarith
      have := hB b this
      exact ⟨le_refl b, this⟩
  obtain ⟨B, hB⟩ := this
  have hAB : s A B = 0 := by
    apply s.zero_below (a' := A) (b' := b)
    repeat linarith
  suffices τ.s a b = ∑ b ∈ Finset.Ico b B, ∑ a ∈ Finset.Ico A a, s.Δ a b by
    rw [this]
    rw [s.sum_ab hA.1 hB.1]
    omega
  classical
  have ite : ∀ a' b' : ℤ, s.Δ a' b' = if τ b' = a' then 1 else 0 := by
    intro a' b'
    have : τ b' = a' ↔ s.Δ a' b' = 1 := asp_func_spec hsub a' b'
    simp only [this]
    have := s.Δ_values a' b'
    rcases this with (h | (h | h)) <;> simp [h]
    have := hsub a' b'
    linarith
  have inner_sum : ∀ b' ∈ Finset.Ico b B,
    ∑ a' ∈ Finset.Ico A a, s.Δ a' b' = if τ b' < a ∧ τ b' ≥ A then 1 else 0 := by
    intro b' hb'
    simp only [ite, Finset.sum_ite_eq, Finset.mem_Ico, ge_iff_le]
    congr 1
    rw [And.comm]
  simp only [ite, Finset.sum_ite_eq, Finset.mem_Ico, Finset.sum_boole]
  rw [τ.s_eq_se_card]
  suffices τ.se_finset a b = {x ∈ Finset.Ico b B | A ≤ τ.func x ∧ τ.func x < a} by congr
  ext b'
  simp only [τ.mem_se, Finset.mem_filter, Finset.mem_Ico]
  by_cases h : b' < b
  · have : ¬ (b' ≥ b) := by linarith
    simp only [ge_iff_le, this, false_and]
  have b_le_b' : b ≤ b' := by linarith
  simp only [ge_iff_le, b_le_b', true_and]
  by_cases h : τ b' ≥ a
  · have : ¬ (τ b' < a) := by linarith
    simp only [this, and_false]
  have τb'_lt_a : τ b' < a := by linarith
  simp only [τb'_lt_a, and_true, true_iff]
  clear h
  -- We now have an element b' of the southeast set. It remains to show b' < B and τ b' ≥ A.
  have : s.Δ (τ b') b' = 1 := by
    simpa using ite (τ b') b'
  have : s (τ b' + 1) b' ≠ 0 := by
    contrapose! this with h_zero
    have := s.Δ_zero_of_s_zero (τ b') b' h_zero
    rw [this]; norm_num
  constructor
  · -- show b' < B
    contrapose! this with b'_ge_B
    apply s.zero_below (a' := a) (b' := B)
    · exact Int.add_one_le_iff.mpr τb'_lt_a
    · exact b'_ge_B
    · exact hB.2
  · -- show τ b' ≥ A
    contrapose! this with a'_lt_A
    apply s.zero_below (a' := A) (b' := b)
    · exact Int.add_one_le_iff.mpr a'_lt_A
    · exact b_le_b'
    · exact hA.2

/-- A slipface is submodular if and only if it is of the form $s_\alpha$ for
some ASP permutation `α`.

*Proposition 4.3 (`prop:imageASP`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).*, full statement. -/
theorem submodular_iff_asp (s : SlipFace) : s.submodular ↔ ∃ α : AspPerm, α.sf = s := by
  constructor
  · intro hsub
    use asp hsub
    exact asp_spec s hsub
  · rintro ⟨α, rfl⟩
    exact α.submodular


/-! ### Closure of submodularity under product

This section proves that the slipface product of submodular slipfaces is
submodular. -/

/-- The valley $\ell \mapsto s_\alpha(a,\ell) + s_\beta(\ell,b)$.

Its minimum is $s_{\alpha \star \beta}(a,b)$, and its rightmost minimizer is
the $M_{\alpha \star \beta}(a,b)$ of
[An extended Demazure product](https://arxiv.org/abs/2206.14227). In Lean that rightmost
minimizer is `(AspValley α β a b).M`. *Definition 4.5 of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), unlabeled in source.* -/
private noncomputable def AspValley (α β : AspPerm) (a b : ℤ) : Valley where
    f := fun l => α.s a l + β.s l b
    rises := by
      intro m
      let L := a - m + α.χ
      let R := b + m - β.χ
      suffices {n : ℤ | α.s a n + β.s n b ≤ m} ⊆ Finset.Icc L R by
        apply Set.Finite.subset _ this
        apply Set.Finite.ofFinset (Finset.Icc L R)
        intro x
        simp only [Finset.mem_Icc, Finset.coe_Icc, Set.mem_Icc]
      intro n hn
      simp only [Set.mem_setOf_eq] at hn
      suffices n ≥ L ∧ n ≤ R by simpa
      constructor
      · linarith [β.s_nonneg n b, α.s_ge a n]
      · linarith [α.s_nonneg a n, β.s_ge n b]

private lemma AspSlipValley (α β : AspPerm) (a b : ℤ) :
  (AspValley α β a b) = (SlipFace.SlipValley α.sf β.sf a b) := by
  suffices (AspValley α β a b).f = (SlipFace.SlipValley α.sf β.sf a b).f by
    rwa [Valley.mk.injEq]
  ext l
  dsimp [AspValley, SlipFace.SlipValley, AspPerm.sf]

/-- If `τ = α ⋆ β` in the Demazure sense, then the minimum of
`AspValley α β a b` is `τ.s a b`. -/
private lemma AspValley_min_eq_s {α β τ : AspPerm} (dprod : τ.eq_dprod α β) (a b : ℤ) :
  (AspValley α β a b).min = τ.s a b := by
  apply le_antisymm
  · have := dprod.2 a b
    unfold AspPerm.dprod_val_le at this
    rcases this with ⟨l, hl⟩
    refine le_trans ?_ hl
    exact (AspValley α β a b).min_spec l
  · have := dprod.1 a b
    unfold AspPerm.dprod_val_ge at this
    specialize this (AspValley α β a b).M
    refine le_trans this ?_
    rw [← (AspValley α β a b).f_M]
    unfold AspValley
    simp

/-- Compare the minima and rightmost minimizers of two valleys that differ by
`1` below a cutoff and agree above it. *Lemma 4.6 (`lem:fg`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/2.* -/
lemma sediment (v w : Valley) {A : ℤ}
  (low : ∀ l : ℤ, l ≤ A → w.f l = v.f l + 1) (high : ∀ l : ℤ, l > A → w.f l = v.f l) :
  ((v.M ≤ A → w.min = v.min + 1)
  ∧ (v.M > A → w.min = v.min))
  ∧ v.M ≤ w.M
  := by
  by_cases h : v.M ≤ A
  · suffices w.min = v.min + 1 ∧ v.M ≤ w.M by
      constructor
      · constructor
        · intro h'; exact this.1
        · intro h'; exfalso; exact lt_irrefl v.M <| lt_of_le_of_lt h h'
      exact this.2
    have Mv_le_Mw : v.M ≤ w.M := by
      by_contra! vM_lt_wM
      have := (w.M_spec v.M).2 vM_lt_wM
      rw [low v.M (by omega), low w.M (by omega)] at this
      have fMv_gt_fMw : v.f v.M > v.f w.M := by omega
      have := v.min_spec w.M
      rw [← v.f_M] at this
      omega
    suffices w.min = v.min + 1 by exact And.intro this Mv_le_Mw
    have le : w.min ≤ v.min + 1 := by
      rw [← v.f_M]
      have : w.f v.M ≥ w.min := w.min_spec v.M
      apply le_trans this
      rw [low v.M h]
    suffices w.min ≥ v.min + 1 by exact le_antisymm le this
    rw [← w.f_M]
    by_cases hM : w.M ≤ A
    · rw [low w.M hM]
      have := v.min_spec w.M
      omega
    · have : w.M > A := by omega
      rw [high w.M this]
      have mV_lt_mW : v.M < w.M := by omega
      have := (v.M_spec w.M).2 mV_lt_mW
      rw [← v.f_M]
      omega
  · suffices w.min = v.min ∧ v.M = w.M by
      constructor
      · constructor
        · intro h'; absurd h'; exact h
        · intro h'; exact this.1
      · exact le_of_eq this.2
    apply lt_of_not_ge at h
    have spec : ∀ n : ℤ, w.f n ≥ w.f v.M ∧ (n > v.M → w.f n > w.f v.M) := by
      intro n
      rw [high v.M h]
      by_cases hn : n ≤ A
      · repeat rw [low n hn]
        have vspec := v.M_spec n
        constructor
        · omega
        · intro hn'
          have := vspec.2 hn'
          omega
      · have hn := lt_of_not_ge hn
        repeat rw [high n hn]
        exact v.M_spec n
    have eq_val := le_antisymm (spec w.M).1 (w.M_spec v.M).1
    have le : w.M ≤ v.M := by
      contrapose! eq_val with vM_lt_wM
      exact ne_of_lt <| (spec w.M).2 vM_lt_wM
    have ge : w.M ≥ v.M := by
      contrapose! eq_val with wM_lt_vM
      have := ne_of_lt <| (w.M_spec v.M).2 wM_lt_vM
      contrapose! this; rw [this]
    have eq : v.M = w.M := le_antisymm ge le; clear le ge
    suffices w.min = v.min by exact And.intro this eq
    rw [← w.f_M, ← eq, high v.M h, v.f_M]

/-- Incrementing the first coordinate changes the valley minimum by `1`
exactly when the rightmost minimizer lies at or to the left of `α⁻¹ a`, and
the rightmost minimizer can only move to the right. *Lemma 4.7 (`lem:Kstara+1`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), in slightly different
phrasing.* -/
lemma AspValley_step_a (α β : AspPerm) (a b : ℤ) :
  let v := AspValley α β a b
  let w := AspValley α β (a+1) b
  w.min = v.min + (if v.M ≤ α⁻¹ a then 1 else 0) ∧ v.M ≤ w.M := by
  intro v w
  have : ∀ n : ℤ, w.f n = v.f n + (if n ≤ α⁻¹ a then 1 else 0) := by
    intro n
    subst v w; simp only [AspValley]
    rw [α.a_step a n]
    omega
  have low : (∀ n : ℤ, n ≤ α⁻¹ a → w.f n = v.f n + 1) := by
    intro n hn
    rw [this n, if_pos hn]
  have high : (∀ n : ℤ, n > α⁻¹ a → w.f n = v.f n) := by
    intro n hn
    rw [this n]
    simp only [add_eq_left, ite_eq_right_iff, one_ne_zero, imp_false, not_le, hn]
  have sed := sediment v w low high
  by_cases h : v.M ≤ α⁻¹ a
  · simp only [h, ↓reduceIte]
    exact ⟨sed.1.1 h, sed.2⟩
  · simp only [h, ↓reduceIte, add_zero]
    exact ⟨sed.1.2 (lt_of_not_ge h), sed.2⟩

/-- Incrementing the second coordinate changes the valley minimum according to
the position of the rightmost minimizer relative to `β b`, and the rightmost
minimizer can only move to the right. *Lemma 4.8 (`lem:Kstarb+1`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), in slightly different
phrasing.* -/
lemma AspValley_step_b (α β : AspPerm) (a b : ℤ) :
  let v := (AspValley α β a b)
  let w := AspValley α β a (b+1)
  w.min = v.min - 1 + (if v.M ≤ β b then 1 else 0) ∧ v.M ≤ w.M := by
  intro v₀ w
  let v := v₀.shift_down 1
  have : v₀.min = v.min + 1 := by
    subst v
    have := v₀.shift_down_min 1
    omega
  rw [this]
  have : v₀.M = v.M := by
    subst v
    have := v₀.shift_down_M 1
    omega
  suffices w.min = v.min  + (if v.M ≤ β b then 1 else 0) ∧ v.M ≤ w.M by
    omega
  subst v₀
  have : ∀ n : ℤ, w.f n = v.f n + (if n ≤ β b then 1 else 0) := by
    intro n
    subst v w; simp only [AspValley]
    rw [β.b_step n b]
    unfold Valley.shift_down
    by_cases h : n ≤ β b
    · simp only [h, ↓reduceIte, sub_add_cancel, add_right_inj, sub_eq_self,
        ite_eq_right_iff, one_ne_zero, imp_false, not_lt]
    · simp only [not_le.mp h, ↓reduceIte]
      omega
  have low : (∀ n : ℤ, n ≤ β b → w.f n = v.f n + 1) := by
    intro n hn
    rw [this n, if_pos hn]
  have high : (∀ n : ℤ, n > β b → w.f n = v.f n) := by
    intro n hn
    rw [this n, if_neg (not_le.mpr hn), add_zero]
  have sed := sediment v w low high
  by_cases h : v.M ≤ β b
  · simp only [h, ↓reduceIte]
    exact ⟨sed.1.1 h, sed.2⟩
  · simp only [h, ↓reduceIte, add_zero]
    exact ⟨sed.1.2 (lt_of_not_ge h), sed.2⟩

lemma AspValley_noninc (α β : AspPerm) (a b c : ℤ) (b_le_c : b ≤ c) :
  let v := AspValley α β a b
  let w := AspValley α β a c
  v.M ≤ w.M := by
  let n : ℕ := (c - b).toNat
  have : c = b + n := by omega
  rw [this]
  induction n with
  | zero =>
    rw [Nat.cast_zero, add_zero]
  | succ n ih =>
    intro v w
    let v' := AspValley α β a (b + n)
    obtain ih : v.M ≤ v'.M := ih
    apply le_trans ih
    subst v' w
    have := (AspValley_step_b α β a (b + n)).2
    refine le_trans this ?_
    apply le_of_eq
    congr 2
    rw [Nat.cast_add, add_assoc, Nat.cast_one]

/-- A local criterion for submodularity: if `s (a + 1) b` does not drop when
`b` increases, then `s a b` does not drop either. -/
private lemma submodular_of_basepoint_preserved (s : SlipFace) (a b : ℤ) :
  s.Δ a b ≥ 0 ↔ (s (a + 1) b = s (a + 1) (b + 1) → s a b = s a (b + 1)) := by
  let d1 := s (a + 1) b - s (a + 1) (b + 1)
  let d2 := s a b - s a (b + 1)
  suffices d1 ≥ d2 ↔ (d1 = 0 → d2 = 0) by
    subst d1 d2
    dsimp [SlipFace.Δ]
    omega
  constructor
  · intro ge zero
    have : d2 ≤ 0 := by
      rwa [zero] at ge
    apply le_antisymm this
    linarith [s.b_step a b]
  · intro h
    by_cases h1 : d1 = 0
    · rw [h1, h h1]
    · have h1 : d1 ≥ 1 := by
        have : d1 ≥ 0 := by linarith [(s.b_step (a+1) b).1]
        apply lt_of_le_of_ne this
        contrapose! h1
        rw [← h1]
      have h2 : d2 ≤ 1 := by linarith [s.b_step a b]
      exact le_trans h2 h1

/-- The product of two submodular slipfaces is submodular.
*Theorem 4.4 (`thm:starExists1`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/5.* -/
theorem submodular_of_star {s t : SlipFace} (subS : s.submodular) (subT : t.submodular) :
  (s.star t).submodular := by
  intro a b
  suffices
    (s ⋆ t) (a + 1) b = (s ⋆ t) (a + 1) (b + 1)
    → (s ⋆ t) a b = (s ⋆ t) a (b + 1) by
    exact (submodular_of_basepoint_preserved (s ⋆ t) a b).mpr this
  let α := asp subS
  have α_spec : α.sf = s := asp_spec s subS
  let β := asp subT
  have β_spec : β.sf = t := asp_spec t subT
  intro eq
  have : ∀ a b : ℤ, (s ⋆ t) a b = (AspValley α β a b).min := by
    intro a b
    have : (s ⋆ t) a b = (SlipFace.SlipValley s t a b).min := by
      rw [SlipFace.star_func_eq]
      dsimp [SlipFace.star_func, SlipFace.SlipValley]
    rw [this]
    rw [AspSlipValley, α_spec, β_spec]
  simp only [this] at eq ⊢
  have := (AspValley_step_b α β (a+1) b).1
  rw [this] at eq
  let M' := (AspValley α β (a + 1) b).M
  have M'_ge_b : M' ≤ β b := by
    have : 1 = if (AspValley α β (a + 1) b).M ≤ β.func b then 1 else 0 := by
      linarith [eq]
    simpa using this
  let M := (AspValley α β a b).M
  have M_le_M' : M ≤ M' := by
    exact (AspValley_step_a α β a b).2
  have M_le_βb : M ≤ β b := le_trans M_le_M' M'_ge_b
  rw [(AspValley_step_b α β a b).1]
  subst M
  simp only [M_le_βb, ↓reduceIte, sub_add_cancel]

/-! ### Closure of submodularity under residuals

This section proves that the slipface residual operations preserve
submodularity.

[An extended Demazure product](https://arxiv.org/abs/2206.14227) phrases the argument using the
rightmost maximizing witness $M_{\alpha \triangleleft \beta}(a,b)$. That maximum may be $\infty$
when the left residual value is zero, since the set of maximizing witnesses may be unbounded
above. Rather than extending $\mathbb{Z}$ to include $\infty$, we instead keep the whole witness
set and express cutoff conditions on $M$ by quantifying over witnesses: a bound $M \leq m$ becomes
a bound on every witness, while $M > m$ becomes the existence of a witness above $m$. -/

/-- The set of witnesses attaining the maximum in
$s_\alpha \triangleleft s_\beta(a,b)$. -/
private def lres_witness_set (α β : AspPerm) (a b : ℤ) : Set ℤ :=
  {l | (α.sf ◃ β.sf) a b = α.s a l - (β⁻¹).s b l}

private lemma lres_wit_mem_lres_witness_set (α β : AspPerm) (a b : ℤ) :
    SlipFace.lres_wit α.sf β.sf a b ∈ lres_witness_set α β a b := by
  dsimp [lres_witness_set]
  rw [SlipFace.lres_wit_spec, AspPerm.sf_dual]
  simp only [AspPerm.sf_func_eq_s]

private lemma lres_witness_set_nonempty (α β : AspPerm) (a b : ℤ) :
    (lres_witness_set α β a b).Nonempty :=
  ⟨SlipFace.lres_wit α.sf β.sf a b, lres_wit_mem_lres_witness_set α β a b⟩

/-- Every candidate value for left residual is at most its maximum. -/
lemma lres_candidate_le (α β : AspPerm) (a b l : ℤ) :
    α.s a l - (β⁻¹).s b l ≤ (α.sf ◃ β.sf) a b := by
  rw [SlipFace.lres_func_eq]
  simpa only [AspPerm.sf_dual, AspPerm.sf_func_eq_s] using SlipFace.lres_val_ge α.sf β.sf a b l

/-- Witness-set form of the left-residual step in the first coordinate:
the step is flat exactly when a witness for the new value lies to the right of
the cutoff. -/
private lemma lres_a_step_eq_iff_exists_witness (α β : AspPerm) (a b : ℤ) :
    (α.sf ◃ β.sf) (a + 1) b = (α.sf ◃ β.sf) a b ↔
      ∃ l ∈ lres_witness_set α β (a + 1) b, α⁻¹ a < l := by
  -- Proof written by Codex.
  constructor
  · intro hflat
    let l := SlipFace.lres_wit α.sf β.sf a b
    have hl : l ∈ lres_witness_set α β a b :=
      lres_wit_mem_lres_witness_set α β a b
    have hcut : α⁻¹ a < l := by
      by_contra hcut
      have hge : α⁻¹ a ≥ l := by omega
      have hstep : α.s (a + 1) l = α.s a l + 1 := by
        rw [α.a_step a l]
        simp only [if_pos hge]
      have hmax := lres_candidate_le α β (a + 1) b l
      dsimp [lres_witness_set] at hl
      omega
    refine ⟨l, ?_, hcut⟩
    have hstep : α.s (a + 1) l = α.s a l :=
      (α.a_step_eq_iff a l).mpr hcut
    dsimp [lres_witness_set] at hl ⊢
    rw [hflat, hstep]
    exact hl
  · rintro ⟨l, hl, hcut⟩
    have hstep : α.s (a + 1) l = α.s a l :=
      (α.a_step_eq_iff a l).mpr hcut
    have hmax := lres_candidate_le α β a b l
    have hmono := ((α.sf ◃ β.sf).a_step a b).1
    dsimp [lres_witness_set] at hl
    apply le_antisymm
    · rw [hl, hstep]
      exact hmax
    · exact hmono

/-- Witness-set form of the left-residual step in the first coordinate:
the step rises by one exactly when every witness for the new value is at or
left of the cutoff. -/
private lemma lres_a_step_one_iff_forall_witness (α β : AspPerm) (a b : ℤ) :
    (α.sf ◃ β.sf) (a + 1) b = (α.sf ◃ β.sf) a b + 1 ↔
      ∀ l ∈ lres_witness_set α β (a + 1) b, l ≤ α⁻¹ a := by
  -- Proof written by Codex.
  constructor
  · intro hone l hl
    by_contra hnot
    have hcut : α⁻¹ a < l := by omega
    have hflat :=
      (lres_a_step_eq_iff_exists_witness α β a b).mpr ⟨l, hl, hcut⟩
    omega
  · intro hall
    have hstep := (α.sf ◃ β.sf).a_step a b
    have hne : (α.sf ◃ β.sf) (a + 1) b ≠ (α.sf ◃ β.sf) a b := by
      intro hflat
      obtain ⟨l, hl, hcut⟩ :=
        (lres_a_step_eq_iff_exists_witness α β a b).mp hflat
      exact (not_lt_of_ge (hall l hl)) hcut
    omega

/-- Witness-set form of the left-residual step in the second coordinate:
the step is flat exactly when an old witness lies to the right of the cutoff.
Here the cutoff is `β b`, from applying the first-coordinate step formula to
the dual slipface $s_{\beta^{-1}}$. -/
private lemma lres_b_step_eq_iff_exists_witness (α β : AspPerm) (a b : ℤ) :
    (α.sf ◃ β.sf) a (b + 1) = (α.sf ◃ β.sf) a b ↔
      ∃ l ∈ lres_witness_set α β a b, β b < l := by
  -- Proof written by Codex.
  constructor
  · intro hflat
    let l := SlipFace.lres_wit α.sf β.sf a (b + 1)
    have hl : l ∈ lres_witness_set α β a (b + 1) :=
      lres_wit_mem_lres_witness_set α β a (b + 1)
    have hcut : β b < l := by
      by_contra hcut
      have hge : β b ≥ l := by omega
      have hstep : (β⁻¹).s (b + 1) l = (β⁻¹).s b l + 1 := by
        rw [(β⁻¹).a_step b l]
        simp only [inv_inv, if_pos hge]
      have hmax := lres_candidate_le α β a b l
      dsimp [lres_witness_set] at hl
      omega
    refine ⟨l, ?_, hcut⟩
    have hstep : (β⁻¹).s (b + 1) l = (β⁻¹).s b l := by
      apply ((β⁻¹).a_step_eq_iff b l).mpr
      simpa only [inv_inv] using hcut
    dsimp [lres_witness_set] at hl ⊢
    rw [← hflat, ← hstep]
    exact hl
  · rintro ⟨l, hl, hcut⟩
    have hstep : (β⁻¹).s (b + 1) l = (β⁻¹).s b l := by
      apply ((β⁻¹).a_step_eq_iff b l).mpr
      simpa only [inv_inv] using hcut
    have hmax := lres_candidate_le α β a (b + 1) l
    have hmono := ((α.sf ◃ β.sf).b_step a b).1
    dsimp [lres_witness_set] at hl
    apply le_antisymm
    · exact hmono
    · rw [hl, ← hstep]
      exact hmax

/-- Witness-set form of the left-residual step in the second coordinate:
the step drops by one exactly when every old witness is at or left of the
cutoff. -/
private lemma lres_b_step_one_iff_forall_witness (α β : AspPerm) (a b : ℤ) :
    (α.sf ◃ β.sf) a (b + 1) = (α.sf ◃ β.sf) a b - 1 ↔
      ∀ l ∈ lres_witness_set α β a b, l ≤ β b := by
  -- Proof written by Codex.
  constructor
  · intro hone l hl
    by_contra hnot
    have hcut : β b < l := by omega
    have hflat :=
      (lres_b_step_eq_iff_exists_witness α β a b).mpr ⟨l, hl, hcut⟩
    omega
  · intro hall
    have hstep := (α.sf ◃ β.sf).b_step a b
    have hne : (α.sf ◃ β.sf) a (b + 1) ≠ (α.sf ◃ β.sf) a b := by
      intro hflat
      obtain ⟨l, hl, hcut⟩ :=
        (lres_b_step_eq_iff_exists_witness α β a b).mp hflat
      exact (not_lt_of_ge (hall l hl)) hcut
    omega

/-- Moving the first coordinate down transports any witness weakly to the
right. This replaces the inequality from
[An extended Demazure product](https://arxiv.org/abs/2206.14227)
$M_{\alpha \triangleleft \beta}(a+1,b) \leq
M_{\alpha \triangleleft \beta}(a,b)$. -/
private lemma lres_witness_move_a_down (α β : AspPerm) (a b l : ℤ)
    (hl : l ∈ lres_witness_set α β (a + 1) b) :
    ∃ l' ∈ lres_witness_set α β a b, l ≤ l' := by
  -- Proof written by Codex.
  have old_of_high :
      ∀ {m}, m ∈ lres_witness_set α β (a + 1) b → α⁻¹ a < m →
        m ∈ lres_witness_set α β a b := by
    intro m hm hcut
    have hflat :=
      (lres_a_step_eq_iff_exists_witness α β a b).mpr ⟨m, hm, hcut⟩
    have hstep : α.s (a + 1) m = α.s a m :=
      (α.a_step_eq_iff a m).mpr hcut
    dsimp [lres_witness_set] at hm ⊢
    rw [← hflat, ← hstep]
    exact hm
  by_cases hcut : α⁻¹ a < l
  · exact ⟨l, old_of_high hl hcut, le_refl l⟩
  have hle : l ≤ α⁻¹ a := by omega
  by_cases hflat : (α.sf ◃ β.sf) (a + 1) b = (α.sf ◃ β.sf) a b
  · obtain ⟨l', hl', hcut'⟩ :=
      (lres_a_step_eq_iff_exists_witness α β a b).mp hflat
    exact ⟨l', old_of_high hl' hcut', by omega⟩
  · have hbounds := (α.sf ◃ β.sf).a_step a b
    have hone : (α.sf ◃ β.sf) (a + 1) b = (α.sf ◃ β.sf) a b + 1 := by
      omega
    have hstep : α.s (a + 1) l = α.s a l + 1 := by
      rw [α.a_step a l]
      simp only [if_pos hle]
    refine ⟨l, ?_, le_refl l⟩
    dsimp [lres_witness_set] at hl ⊢
    rw [hstep] at hl
    omega

/-- Moving the second coordinate up transports any witness weakly to the
right. This replaces the inequality from
[An extended Demazure product](https://arxiv.org/abs/2206.14227)
$M_{\alpha \triangleleft \beta}(a,b) \leq
M_{\alpha \triangleleft \beta}(a,b+1)$. -/
private lemma lres_witness_move_b_up (α β : AspPerm) (a b l : ℤ)
    (hl : l ∈ lres_witness_set α β a b) :
    ∃ l' ∈ lres_witness_set α β a (b + 1), l ≤ l' := by
  -- Proof written by Codex.
  have new_of_high :
      ∀ {m}, m ∈ lres_witness_set α β a b → β b < m →
        m ∈ lres_witness_set α β a (b + 1) := by
    intro m hm hcut
    have hflat :=
      (lres_b_step_eq_iff_exists_witness α β a b).mpr ⟨m, hm, hcut⟩
    have hstep : (β⁻¹).s (b + 1) m = (β⁻¹).s b m := by
      apply ((β⁻¹).a_step_eq_iff b m).mpr
      simpa only [inv_inv] using hcut
    dsimp [lres_witness_set] at hm ⊢
    rw [hflat, hstep]
    exact hm
  by_cases hcut : β b < l
  · exact ⟨l, new_of_high hl hcut, le_refl l⟩
  have hle : l ≤ β b := by omega
  by_cases hflat : (α.sf ◃ β.sf) a (b + 1) = (α.sf ◃ β.sf) a b
  · obtain ⟨l', hl', hcut'⟩ :=
      (lres_b_step_eq_iff_exists_witness α β a b).mp hflat
    exact ⟨l', new_of_high hl' hcut', by omega⟩
  · have hbounds := (α.sf ◃ β.sf).b_step a b
    have hdrop : (α.sf ◃ β.sf) a (b + 1) = (α.sf ◃ β.sf) a b - 1 := by
      omega
    have hstep : (β⁻¹).s (b + 1) l = (β⁻¹).s b l + 1 := by
      rw [(β⁻¹).a_step b l]
      simp only [inv_inv, if_pos hle]
    refine ⟨l, ?_, le_refl l⟩
    dsimp [lres_witness_set] at hl ⊢
    rw [hstep]
    omega

/-- Moving the first coordinate down through several steps transports a witness
weakly to the right. -/
private lemma lres_witness_move_a_down_of_le (α β : AspPerm) (a c b l : ℤ)
    (hac : a ≤ c) (hl : l ∈ lres_witness_set α β c b) :
    ∃ l' ∈ lres_witness_set α β a b, l ≤ l' := by
  -- Proof written by Codex.
  let n : ℕ := (c - a).toNat
  have hc : c = a + n := by omega
  rw [hc] at hl
  suffices ∀ n : ℕ, ∀ l,
      l ∈ lres_witness_set α β (a + n) b →
        ∃ l' ∈ lres_witness_set α β a b, l ≤ l' by
    exact this n l hl
  intro n
  induction n with
  | zero =>
    intro l hl
    simp only [Nat.cast_zero, add_zero] at hl
    exact ⟨l, hl, le_refl l⟩
  | succ n ih =>
    intro l hl
    have hl_step : l ∈ lres_witness_set α β ((a + n) + 1) b := by
      simpa only [Nat.cast_succ, Nat.cast_add, Nat.cast_one, add_assoc] using hl
    obtain ⟨m, hm, hlm⟩ := lres_witness_move_a_down α β (a + n) b l hl_step
    obtain ⟨l', hl', hml'⟩ := ih m hm
    exact ⟨l', hl', le_trans hlm hml'⟩

/-- Moving the second coordinate up through several steps transports a witness
weakly to the right. -/
private lemma lres_witness_move_b_up_of_le (α β : AspPerm) (a b c l : ℤ)
    (hbc : b ≤ c) (hl : l ∈ lres_witness_set α β a b) :
    ∃ l' ∈ lres_witness_set α β a c, l ≤ l' := by
  -- Proof written by Codex.
  let n : ℕ := (c - b).toNat
  have hc : c = b + n := by omega
  rw [hc]
  suffices ∀ n : ℕ, ∀ l,
      l ∈ lres_witness_set α β a b →
        ∃ l' ∈ lres_witness_set α β a (b + n), l ≤ l' by
    exact this n l hl
  intro n
  induction n with
  | zero =>
    intro l hl
    simp only [Nat.cast_zero, add_zero]
    exact ⟨l, hl, le_refl l⟩
  | succ n ih =>
    intro l hl
    obtain ⟨m, hm, hlm⟩ := ih l hl
    obtain ⟨l', hl', hml'⟩ := lres_witness_move_b_up α β a (b + n) m hm
    refine ⟨l', ?_, le_trans hlm hml'⟩
    simpa only [Nat.cast_succ, Nat.cast_add, Nat.cast_one, add_assoc] using hl'

/-- The left residual $s \triangleleft t$ of submodular slipfaces is
submodular. *Theorem 4.10 (`thm:resLExists`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/11.* -/
theorem submodular_of_lres {s t : SlipFace}
    (subS : s.submodular) (subT : t.submodular) :
    (s ◃ t).submodular := by
  -- Proof written by Codex.
  intro a b
  suffices
      (s ◃ t) (a + 1) b = (s ◃ t) (a + 1) (b + 1) →
        (s ◃ t) a b = (s ◃ t) a (b + 1) by
    exact (submodular_of_basepoint_preserved (s ◃ t) a b).mpr this
  let α := asp subS
  have α_spec : α.sf = s := asp_spec s subS
  let β := asp subT
  have β_spec : β.sf = t := asp_spec t subT
  intro hflat
  rw [← α_spec, ← β_spec] at hflat ⊢
  obtain ⟨l, hl, hcut⟩ :=
    (lres_b_step_eq_iff_exists_witness α β (a + 1) b).mp hflat.symm
  obtain ⟨l', hl', hl_le_l'⟩ := lres_witness_move_a_down α β a b l hl
  have hcut' : β b < l' := lt_of_lt_of_le hcut hl_le_l'
  exact ((lres_b_step_eq_iff_exists_witness α β a b).mpr ⟨l', hl', hcut'⟩).symm

/-- The right residual $s \triangleright t$ of submodular slipfaces is
submodular. *Theorem 4.10 (`thm:resLExists`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/11.* -/
theorem submodular_of_rres {s t : SlipFace}
    (subS : s.submodular) (subT : t.submodular) :
    (s ▹ t).submodular := by
  -- Proof written by Codex.
  have hdual : (s ▹ t).dual.submodular := by
    rw [SlipFace.rres_dual]
    exact submodular_of_lres (submodular_dual subT) (submodular_dual subS)
  intro a b
  rw [← (s ▹ t).Δ_dual]
  exact hdual b a

end Submodular

/-! ### The operations $\star,\; \triangleleft,\; \triangleright$ on `AspPerm`

Using the slipface construction above, this section defines Demazure product
and the two residual operationson ASP permutations and proves its basic
structural properties. -/

namespace AspPerm

/-- Two ASP permutations are equal if their associated slipfaces are equal. -/
lemma eq_of_sf_eq {α β : AspPerm} (eq_sf : α.sf = β.sf) : α = β := by
  suffices α.func = β.func by
    cases α; cases β
    congr
  ext n
  have : β.sf.Δ (β n) n = 1 := by
    simpa using β.Delta_eq (β n) n
  rw [← eq_sf] at this
  rw [α.Delta_eq (β n) n] at this
  contrapose! this with neq
  simp only [neq, ↓reduceIte, ne_eq, zero_ne_one, not_false_eq_true]

/-- The slipface product of two ASP permutations is represented by a unique ASP
permutation. -/
private lemma star_exists : ∀ α β : AspPerm, ∃! τ : AspPerm, τ.sf = α.sf ⋆ β.sf := by
  intro α β
  have : (α.sf ⋆ β.sf).submodular := by
    exact Submodular.submodular_of_star (α.submodular) (β.submodular)
  have ex := (Submodular.submodular_iff_asp (α.sf ⋆ β.sf)).mp this
  rcases ex with ⟨τ, hτ⟩
  use τ
  constructor
  · exact hτ
  · intro σ hσ
    rw [← hσ] at hτ
    rw [τ.eq_of_sf_eq hτ]

/-- The slipface left residual of two ASP permutations is represented by a
unique ASP permutation. -/
private lemma lres_exists : ∀ α β : AspPerm, ∃! τ : AspPerm, τ.sf = α.sf ◃ β.sf := by
  intro α β
  have : (α.sf ◃ β.sf).submodular := by
    exact Submodular.submodular_of_lres (α.submodular) (β.submodular)
  have ex := (Submodular.submodular_iff_asp (α.sf ◃ β.sf)).mp this
  rcases ex with ⟨τ, hτ⟩
  use τ
  constructor
  · exact hτ
  · intro σ hσ
    rw [← hσ] at hτ
    rw [τ.eq_of_sf_eq hτ]

/-- The slipface right residual of two ASP permutations is represented by a
unique ASP permutation. -/
private lemma rres_exists : ∀ α β : AspPerm, ∃! τ : AspPerm, τ.sf = α.sf ▹ β.sf := by
  intro α β
  have : (α.sf ▹ β.sf).submodular := by
    exact Submodular.submodular_of_rres (α.submodular) (β.submodular)
  have ex := (Submodular.submodular_iff_asp (α.sf ▹ β.sf)).mp this
  rcases ex with ⟨τ, hτ⟩
  use τ
  constructor
  · exact hτ
  · intro σ hσ
    rw [← hσ] at hτ
    rw [τ.eq_of_sf_eq hτ]

/-- The Demazure product on ASP permutations, characterized by
$$
s_{\alpha \star \beta}(a,b) = \min_{\ell \in \mathbb{Z}}
  [s_\alpha(a,\ell) + s_\beta(\ell,b)].
$$

In Lean this operation is written `α ⋆ β`. -/
noncomputable def star (α β : AspPerm) : AspPerm :=
  Classical.choose (star_exists α β)

/-- The Demazure product on ASP is characterized by the equation
$s_{\alpha \star \beta} = s_\alpha \star s_\beta$.
*Theorem 4.4 (`thm:starExists1`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/5. -/
@[simp] lemma star_spec (α β : AspPerm) : (star α β).sf = α.sf ⋆ β.sf :=
  (Classical.choose_spec (star_exists α β)).1

infixl:70 " ⋆ " => star

/-- Left residual on ASP permutations, characterized by
$s_{\alpha \triangleleft \beta} = s_\alpha \triangleleft s_\beta$.

In Lean this operation is written `α ◃ β`. -/
noncomputable def lres (α β : AspPerm) : AspPerm :=
  Classical.choose (lres_exists α β)

/-- Left residual on ASP permutations is characterized by
$s_{\alpha \triangleleft \beta} = s_\alpha \triangleleft s_\beta$.
*Theorem 4.10 (`thm:resLExists`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 3/11.* -/
@[simp] lemma lres_spec (α β : AspPerm) :
    (lres α β).sf = α.sf ◃ β.sf :=
  (Classical.choose_spec (lres_exists α β)).1

infixl:70 " ◃ " => lres

/-- Right residual on ASP permutations, characterized by
$s_{\alpha \triangleright \beta} = s_\alpha \triangleright s_\beta$.

In Lean this operation is written `α ▹ β`. -/
noncomputable def rres (α β : AspPerm) : AspPerm :=
  Classical.choose (rres_exists α β)

/-- Right residual on ASP permutations is characterized by
$s_{\alpha \triangleright \beta} = s_\alpha \triangleright s_\beta$.
*Theorem 4.10 (`thm:resLExists`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 4/11.* -/
@[simp] lemma rres_spec (α β : AspPerm) :
    (rres α β).sf = α.sf ▹ β.sf :=
  (Classical.choose_spec (rres_exists α β)).1

infixr:70 " ▹ " => rres

/-- Demazure product on ASP permutations is associative.
*Theorem 4.4 (`thm:starExists1`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 3/5.* -/
lemma star_assoc : ∀ α β γ : AspPerm, (α ⋆ β) ⋆ γ = α ⋆ (β ⋆ γ) := by
  intro α β γ
  apply AspPerm.eq_of_sf_eq
  simp only [star_spec, SlipFace.star_assoc]

/-- Left residual associates with Demazure product on ASP permutations.
*Theorem 4.10 (`thm:resLExists`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 5/11.* -/
lemma lres_assoc (α β γ : AspPerm) :
    (α ◃ β) ◃ γ = α ◃ (β ⋆ γ) := by
  -- Proof written by Codex.
  apply AspPerm.eq_of_sf_eq
  simp only [lres_spec, star_spec, SlipFace.lres_assoc]

/-- Right residual associates with Demazure product on ASP permutations.
*Theorem 4.10 (`thm:resLExists`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 6/11.* -/
lemma rres_assoc (α β γ : AspPerm) :
    α ▹ (β ▹ γ) = (α ⋆ β) ▹ γ := by
  -- Proof written by Codex.
  apply AspPerm.eq_of_sf_eq
  simp only [rres_spec, star_spec, SlipFace.rres_assoc]

/-- Inversion swaps left residual for right residual.
*Theorem 4.10 (`thm:resLExists`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 7/11.* -/
lemma inverse_lres (α β : AspPerm) :
    (α ◃ β)⁻¹ = β⁻¹ ▹ α⁻¹ := by
  -- Proof written by Codex.
  apply AspPerm.eq_of_sf_eq
  rw [← AspPerm.sf_dual]
  simp only [lres_spec, SlipFace.lres_dual, AspPerm.sf_dual,
    rres_spec]

/-- The shift of left residual is the sum of shifts.
*Theorem 4.10 (`thm:resLExists`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 8/11.* -/
lemma chi_lres (α β : AspPerm) : (α ◃ β).χ = α.χ + β.χ := by
  repeat rw [← AspPerm.sf_chi_eq]
  simp only [lres_spec, SlipFace.chi_lres]

/-- The shift of right residual is the sum of shifts.
*Theorem 4.10 (`thm:resLExists`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 9/11.* -/
lemma chi_rres (α β : AspPerm) : (α ▹ β).χ = α.χ + β.χ := by
  repeat rw [← AspPerm.sf_chi_eq]
  simp only [rres_spec, SlipFace.chi_rres]

private lemma star_valley (α β : AspPerm) (a b : ℤ) : (α ⋆ β).s a b
  = (Submodular.AspValley α β a b).min := by
  let v := (Submodular.AspValley α β a b)
  have : (α ⋆ β).s a b = (α ⋆ β).sf.func a b := by
    rw [AspPerm.sf_func_eq_s]
  rw [this]
  rw [star_spec]
  let w := SlipFace.SlipValley α.sf β.sf a b
  suffices w.min = v.min by
    rw [← this, SlipFace.star_func_eq]
    rfl
  have : w = v := by exact Submodular.AspSlipValley α β a b
  rw [this]

/-- The min-plus characterization of the Demazure product on \mathrm{ASP}.
This is part of *Theorem A* (`thm:starExists`) in [An extended Demazure product](https://arxiv.org/abs/2206.14227). -/
theorem star_sf_isleast (α β : AspPerm) (a b : ℤ) :
    IsLeast {α.s a l + β.s l b | l : ℤ} ((α ⋆ β).s a b) := by
  constructor
  · exact ⟨(Submodular.AspValley α β a b).M,
      (Submodular.AspValley α β a b).f_M.trans (star_valley α β a b).symm⟩
  · rintro y ⟨l, rfl⟩
    rw [star_valley]
    exact (Submodular.AspValley α β a b).min_spec l

/-- The max-minus characteriztion of the $\triangleleft$ operator on \mathrm{ASP}.
This is part of *Theorem 1.1* (`thm:resL`) in [An extended Demazure product](https://arxiv.org/abs/2206.14227). -/
theorem lres_sf_isgreatest (α β : AspPerm) (a b : ℤ) :
    IsGreatest {α.s a l - β⁻¹.s b l | l : ℤ} ((α ◃ β).s a b) := by
  constructor
  · use SlipFace.lres_wit α.sf β.sf a b
    convert Eq.symm <| SlipFace.lres_wit_spec α.sf β.sf a b
    · rfl
    · rw [β.sf_dual]
      rfl
    · rw [← lres_spec α β]
      rfl
  · rintro x ⟨l, rfl⟩
    convert SlipFace.lres_val_ge α.sf β.sf a b l
    · rfl
    · rw [β.sf_dual]
      rfl
    · rw [← SlipFace.lres_func_eq α.sf β.sf, ← lres_spec α β]
      rfl

/-- Inversion reverses Demazure products. *Theorem 4.4 (`thm:starExists1`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 4/5.* -/
lemma inverse_star (α β : AspPerm) : (α ⋆ β)⁻¹ = β⁻¹ ⋆ α⁻¹ := by
  have ex := star_exists (β⁻¹) (α⁻¹)
  let τ := β⁻¹ ⋆ α⁻¹
  have τ_eq : τ.sf = β⁻¹.sf ⋆ α⁻¹.sf  := (ex.choose_spec).1
  apply (ex.choose_spec).2 (α ⋆ β)⁻¹
  simp only [SF_ext]
  intro a b
  repeat rw [← AspPerm.sf_dual]
  simp

/-- The shift of a Demazure product satisfies
`(α ⋆ β).χ = α.χ + β.χ`, i.e. $\chi_{\alpha \star \beta}
= \chi_\alpha + \chi_\beta$. *Theorem 4.4 (`thm:starExists1`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 5/5.* -/
lemma chi_star (α β : AspPerm) : (α ⋆ β).χ = α.χ + β.χ := by
  have ex := star_exists α β
  let τ := α ⋆ β
  have τ_eq : τ.sf = α.sf ⋆ β.sf  := (ex.choose_spec).1
  repeat rw [← AspPerm.sf_chi_eq]
  simp only [star_spec, SlipFace.chi_star, sf_chi_eq]

/-!
  ## Products and Demazure products of lists of ASP permutations
-/

/-- Demazure product of a list of ASP permutations. -/
noncomputable abbrev DProd (L : List AspPerm) : AspPerm :=
  List.foldr AspPerm.star AspPerm.id L

/-- Ordinary product of a list of ASP permutations. -/
noncomputable abbrev OrdProd (L : List AspPerm) : AspPerm :=
  List.foldr (· * ·) AspPerm.id L

@[simp] lemma DProd_nil : DProd [] = AspPerm.id := rfl

@[simp] lemma DProd_cons (α : AspPerm) (L : List AspPerm) :
    DProd (α :: L) = α ⋆ DProd L := rfl

@[simp] lemma OrdProd_nil : OrdProd [] = AspPerm.id := rfl

@[simp] lemma OrdProd_cons (α : AspPerm) (L : List AspPerm) :
    OrdProd (α :: L) = α * OrdProd L := rfl

/-- The shift of a Demazure list product is the sum of the shifts. -/
lemma chi_DProd (L : List AspPerm) : (DProd L).χ = (L.map AspPerm.χ).sum := by
  -- Proof written by GPT 5.5.
  induction L with
  | nil => simp only [DProd_nil, List.map_nil, List.sum_nil, id_chi]
  | cons α L ih =>
      simp only [DProd_cons, List.map_cons, List.sum_cons, chi_star, ih]

/-- The shift of an ordinary list product is the sum of the shifts. -/
lemma chi_OrdProd (L : List AspPerm) : (OrdProd L).χ = (L.map AspPerm.χ).sum := by
  -- Proof written by GPT 5.5.
  induction L with
  | nil => simp only [OrdProd_nil, List.map_nil, List.sum_nil, id_chi]
  | cons α L ih =>
      simp only [OrdProd_cons, List.map_cons, List.sum_cons, chi_mul, ih]

/-!
  ## Some properties of the identity permutations
-/

lemma id_s_eq (a b : ℤ) : AspPerm.id.s a b = max (a - b) 0 := by
  rw [AspPerm.s_eq_se_card]
  have hset : AspPerm.id.se_finset a b = Finset.Ico b a := by
    ext k
    constructor
    · intro hk
      have hk' : b ≤ k ∧ AspPerm.id k < a := (AspPerm.id.mem_se a b k).1 hk
      simpa [AspPerm.id] using hk'
    · intro hk
      have hk' : b ≤ k ∧ AspPerm.id k < a := by
        simpa [AspPerm.id] using hk
      exact (AspPerm.id.mem_se a b k).2 hk'
  rw [hset]
  have hcard : (Finset.Ico b a).card = (a - b).toNat := by
    simp only [Int.card_Ico b a]
  rw [hcard]
  by_cases h : a - b ≥ 0
  · rw [max_eq_left h, Int.toNat_of_nonneg h]
  · have h' : a - b < 0 := lt_of_not_ge h
    rw [max_eq_right (le_of_lt h')]
    have : (a - b).toNat = 0 := Int.toNat_of_nonpos (le_of_lt h')
    simp only [this, Nat.cast_zero]

lemma id_sf : AspPerm.id.sf = SlipFace.id := by
  apply (SF_ext _ _).mpr
  intro a b
  change AspPerm.id.s a b = max (a - b) 0
  exact id_s_eq a b

lemma id_star (α : AspPerm) : AspPerm.id ⋆ α = α := by
  apply AspPerm.eq_of_sf_eq
  rw [AspPerm.star_spec, id_sf]
  simpa using SlipFace.id_mul α.sf

lemma star_id (α : AspPerm) : α ⋆ AspPerm.id = α := by
  apply AspPerm.eq_of_sf_eq
  rw [AspPerm.star_spec, id_sf]
  simpa using SlipFace.mul_id α.sf

/-!
  ## Partial (pre)orders on ASP permutations
-/

-- The `PartialOrder` on `AspPerm` is only now defined because we needed `eq_of_sf_eq`.
instance : PartialOrder AspPerm where
  le (σ τ : AspPerm) := ∀ a b : ℤ, σ.s a b ≤ τ.s a b
  le_refl := by
    intro σ a b
    exact Int.le_refl (σ.s a b)
  le_trans := by
    intro σ τ υ h₁ h₂ a b
    exact Int.le_trans (h₁ a b) (h₂ a b)
  le_antisymm := by
    intro σ τ h₁ h₂
    apply eq_of_sf_eq
    rw [SF_ext]
    intro a b
    exact Int.le_antisymm (h₁ a b) (h₂ a b)

/-- The relation $\alpha \leq_\chi \beta$ from
[An extended Demazure product](https://arxiv.org/abs/2206.14227): Bruhat order together with
equality of shifts. In Lean this is the infix `≤χ`. -/
def le_chi (σ τ : AspPerm) : Prop := σ ≤ τ ∧ σ.χ = τ.χ
infix:50 " ≤χ " => le_chi

/-- Bruhat order on ASP permutations agrees with pointwise order on their
slipfaces. -/
lemma sf_le_iff (α β : AspPerm) : α.sf ≤ β.sf ↔ α ≤ β := Iff.rfl

/-- Inversion preserves Bruhat comparisons between ASP permutations of the
same shift. *Lemma 2.1 (`lem:bruhatInverse`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227).* -/
theorem le_chi_inv_iff (α β : AspPerm) : α ≤χ β ↔ α⁻¹ ≤χ β⁻¹ := by
  -- Proof written by Codex.
  have inverse_of_le_chi : ∀ {σ τ : AspPerm}, σ ≤χ τ → σ⁻¹ ≤χ τ⁻¹ := by
    intro σ τ h
    constructor
    · intro a b
      rw [σ.s'_eq a b, τ.s'_eq a b, h.2]
      linarith [h.1 b a]
    · simp only [chi_dual, h.2]
  constructor
  · exact inverse_of_le_chi
  · intro h
    simpa only [inv_inv] using inverse_of_le_chi h

/-- An ASP permutation of nonnegative shift lies above the identity in Bruhat
order. This is the $\chi = 0$ case of the minimum-shift observation after Definition 2.5 in
[An extended Demazure product](https://arxiv.org/abs/2206.14227). -/
lemma id_le_of_chi_nonneg {τ : AspPerm} (hχ : 0 ≤ τ.χ) : AspPerm.id ≤ τ := by
  -- Proof written by Codex.
  intro a b
  rw [id_s_eq]
  apply max_le
  · linarith [τ.s_ge a b]
  · exact τ.s_nonneg a b

/-- Demazure product on ASP permutations is Bruhat-increasing in both
arguments. This lifts the slipface comparison of Lemma 3.8 in
[An extended Demazure product](https://arxiv.org/abs/2206.14227). -/
lemma star_mono {α₁ α₂ β₁ β₂ : AspPerm}
    (hα : α₁ ≤ α₂) (hβ : β₁ ≤ β₂) : α₁ ⋆ β₁ ≤ α₂ ⋆ β₂ := by
  -- Proof written by Codex.
  apply (sf_le_iff (α₁ ⋆ β₁) (α₂ ⋆ β₂)).mp
  simp only [star_spec]
  exact SlipFace.star_mono
    ((sf_le_iff α₁ α₂).mpr hα)
    ((sf_le_iff β₁ β₂).mpr hβ)

/-- The left residual $\tau \triangleleft \beta^{-1}$ is the Bruhat
minimum of the ASP permutations $\alpha$ such that $\alpha \star \beta \geq \tau$.
*Theorem 4.10 (`thm:resLExists`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 10/11.* -/
lemma ge_star_iff_ge_lres (α β τ : AspPerm) :
    α ≥ τ ◃ β⁻¹ ↔ α ⋆ β ≥ τ := by
  change (τ ◃ β⁻¹).sf ≤ α.sf ↔ τ.sf ≤ (α ⋆ β).sf
  simpa only [lres_spec, star_spec, sf_dual] using
    (SlipFace.ge_star_iff_ge_lres α.sf β.sf τ.sf)

/-- The right residual $\alpha^{-1} \triangleright \tau$ is the Bruhat
minimum of the ASP permutations $\beta$ such that $\alpha \star \beta \geq \tau$.
*Theorem 4.10 (`thm:resLExists`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 11/11.* -/
lemma ge_star_iff_ge_rres (α β τ : AspPerm) :
    β ≥ α⁻¹ ▹ τ ↔ α ⋆ β ≥ τ := by
  change (α⁻¹ ▹ τ).sf ≤ β.sf ↔ τ.sf ≤ (α ⋆ β).sf
  simpa only [rres_spec, star_spec, sf_dual] using
    (SlipFace.ge_star_iff_ge_rres α.sf β.sf τ.sf)

/-- The left residual $\alpha \triangleleft \beta^{-1}$ is the minimum permutation $\gamma$
  such that $\gamma \star \beta \ge \alpha$.
  This is the first sentence of *Theorem 1.1* (`thm:resL`) in [An extended Demazure product](https://arxiv.org/abs/2206.14227). -/
theorem lres_eq_min (α β : AspPerm) :
  IsLeast {γ : AspPerm | γ ⋆ β ≥ α } (α ◃ β⁻¹) := by
  constructor
  · apply (ge_star_iff_ge_lres (α ◃ β⁻¹) β α).mp (le_refl _)
  · intro γ h
    exact (ge_star_iff_ge_lres γ β α).mpr h

/-- Comparison `τ ≤ α ⋆ β` is equivalent to the lower Demazure-product
inequalities defining `τ.le_dprod α β`. -/
lemma le_star_iff (τ α β : AspPerm) : τ ≤ α ⋆ β ↔ τ.le_dprod α β := by
  constructor
  · intro le a b
    specialize le a b
    let v := (Submodular.AspValley α β a b)
    unfold AspPerm.dprod_val_ge
    intro l
    apply le_trans le
    rw [star_valley]
    exact v.min_spec l
  · intro dle a b
    let v := (Submodular.AspValley α β a b)
    specialize dle a b v.M
    apply le_trans dle
    rw [star_valley, ← v.f_M]
    exact Int.le_refl (v.f v.M)

/-- Comparison `α ⋆ β ≤ τ` is equivalent to the upper Demazure-product
inequalities defining `τ.ge_dprod α β`. -/
lemma ge_star_iff (τ α β : AspPerm) : α ⋆ β ≤ τ ↔ τ.ge_dprod α β := by
  constructor
  · intro ge a b
    specialize ge a b
    let v := (Submodular.AspValley α β a b)
    use v.M
    have : α.s a v.M + β.s v.M b = v.f v.M := by rfl
    rw [this, v.f_M]
    rwa [star_valley] at ge
  · intro dge a b
    let v := (Submodular.AspValley α β a b)
    rcases dge a b with ⟨l, hl⟩
    calc
      (α ⋆ β).s a b = v.f v.M := by rw [star_valley, v.f_M]
      _ ≤ v.f l := by
        rw [v.f_M]
        exact v.min_spec l
      _ = α.s a l + β.s l b := rfl
      _ ≤ τ.s a b := hl

/-- Equality `τ = α ⋆ β` is equivalent to satisfying both Demazure comparison
conditions. -/
lemma eq_star_iff {τ α β : AspPerm} : τ = α ⋆ β ↔ τ.eq_dprod α β := by
  constructor
  · intro eq
    have le : τ ≤ α ⋆ β := by
      rw [eq]
    have ge : α ⋆ β ≤ τ := by
      rw [eq]
    constructor
    · rwa [← le_star_iff]
    · rwa [← ge_star_iff]
  · intro eq
    have le : τ ≤ α ⋆ β := by
      rw [le_star_iff]
      exact eq.1
    have ge : α ⋆ β ≤ τ := by
      rw [ge_star_iff]
      exact eq.2
    apply le_antisymm le ge

end AspPerm

/-! ### Weak-order consequences of Demazure product

The final results in this file record the weak-order inequalities satisfied by
the factors of a Demazure product. -/

namespace Submodular

/-- In a Demazure product `α ⋆ β`, the factor `β` lies below the product in
left weak order. *Lemma 4.9 (`lem:invStar`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/2.* -/
theorem lel_of_dprod (α β : AspPerm) : β ≤L α ⋆ β := by
  let τ := α ⋆ β
  have dprod : τ.eq_dprod α β := by
    rw [← AspPerm.eq_star_iff]
  rintro ⟨u, v⟩ ⟨u_lt_v, βv_lt_βu⟩
  apply And.intro u_lt_v
  contrapose! βv_lt_βu with τu_le_τv
  have : τ u ≠ τ v := by
    intro eq
    apply τ.injective at eq
    rw [eq] at u_lt_v
    exact lt_irrefl v u_lt_v
  have τv_le_τu : τ u < τ v := lt_of_le_of_ne τu_le_τv this; clear this τu_le_τv
  let a := τ v
  let val_au := AspValley α β a u
  let val_av := AspValley α β a v
  have Mau_gt_βu : val_au.M > β u := by
    contrapose! τv_le_τu with h
    have := (AspValley_step_b α β a u).1
    subst val_au
    simp only [h, ↓reduceIte, sub_add_cancel] at this
    rw [AspValley_min_eq_s dprod a (u + 1), AspValley_min_eq_s dprod a u,
      τ.b_step_eq_iff a u] at this
    exact this
  have Mav_le_βv : val_av.M ≤ β v := by
    by_contra h
    have := (AspValley_step_b α β a v).1
    subst val_av
    simp only [h, ↓reduceIte, add_zero] at this
    rw [AspValley_min_eq_s dprod a (v+1), AspValley_min_eq_s dprod a v,
      τ.b_step_one_iff a v] at this
    exact lt_irrefl a this
  have Mau_le_Mav : val_au.M ≤ val_av.M := by
    apply AspValley_noninc α β a u v
    exact le_of_lt u_lt_v
  omega

/-- In a Demazure product `α ⋆ β`, the factor `α` lies below the product in
right weak order. *Lemma 4.9 (`lem:invStar`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/2.* -/
theorem ler_of_dprod (α β : AspPerm) : α ≤R α ⋆ β := by
  let τ := α ⋆ β
  have dprod : τ.eq_dprod α β := by
    rw [← AspPerm.eq_star_iff]
  suffices α⁻¹ ≤L τ⁻¹ by
    simpa using AspPerm.le_weak_R_of_L this
  -- apply lel_of_dprod β⁻¹ α⁻¹
  have := AspPerm.dprod_inv_eq_inv_dprod τ α β dprod
  rw [← AspPerm.eq_star_iff] at this
  rw [this]
  exact lel_of_dprod β⁻¹ α⁻¹

/-! ### Weak-order consequences of residuals -/

/-- Left residual forms a reduced product with the inverse of its right
factor. *Lemma 4.14 (`lem:invRes`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/2.* -/
theorem reducedProduct_of_lres (α β : AspPerm) :
    AspPerm.ReducedProduct (α ◃ β) β⁻¹ := by
  -- Proof written by Codex.
  unfold AspPerm.ReducedProduct
  simp only [inv_inv]
  apply Set.disjoint_left.mpr
  rintro ⟨u, v⟩ huv hβ
  let a := (α ◃ β) u
  have hdrop_s : (α ◃ β).s a (v + 1) = (α ◃ β).s a v - 1 := by
    exact ((α ◃ β).b_step_one_iff a v).mpr huv.2
  have hflat_s : (α ◃ β).s a (u + 1) = (α ◃ β).s a u := by
    exact ((α ◃ β).b_step_eq_iff a u).mpr (by rfl)
  have hdrop : (α.sf ◃ β.sf) a (v + 1) = (α.sf ◃ β.sf) a v - 1 := by
    simpa only [← AspPerm.sf_func_eq_s, AspPerm.lres_spec] using hdrop_s
  have hflat : (α.sf ◃ β.sf) a (u + 1) = (α.sf ◃ β.sf) a u := by
    simpa only [← AspPerm.sf_func_eq_s, AspPerm.lres_spec] using hflat_s
  have hv_wit := (lres_b_step_one_iff_forall_witness α β a v).mp hdrop
  obtain ⟨l, hl, hβu⟩ :=
    (lres_b_step_eq_iff_exists_witness α β a u).mp hflat
  obtain ⟨l', hl', hll'⟩ :=
    lres_witness_move_b_up_of_le α β a u v l (le_of_lt huv.1) hl
  have hl'_le : l' ≤ β v := hv_wit l' hl'
  have : β u < β v := lt_of_lt_of_le (lt_of_lt_of_le hβu hll') hl'_le
  exact (not_lt_of_ge (le_of_lt hβ.2)) this

/-- Left residual is below its left factor in right weak order.
*Lemma 4.14 (`lem:invRes`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/2.* -/
theorem ler_of_lres (α β : AspPerm) : α ◃ β ≤R α := by
  -- Proof written by Codex.
  rintro ⟨u, v⟩ huv
  let b := (α ◃ β)⁻¹ u
  have hflat_s : (α ◃ β).s (v + 1) b = (α ◃ β).s v b := by
    exact ((α ◃ β).a_step_eq_iff v b).mpr huv.2
  have hone_s : (α ◃ β).s (u + 1) b = (α ◃ β).s u b + 1 := by
    exact ((α ◃ β).a_step_one_iff u b).mpr (by rfl)
  have hflat : (α.sf ◃ β.sf) (v + 1) b = (α.sf ◃ β.sf) v b := by
    simpa only [← AspPerm.sf_func_eq_s, AspPerm.lres_spec] using hflat_s
  have hone : (α.sf ◃ β.sf) (u + 1) b = (α.sf ◃ β.sf) u b + 1 := by
    simpa only [← AspPerm.sf_func_eq_s, AspPerm.lres_spec] using hone_s
  obtain ⟨l, hl, hαv⟩ :=
    (lres_a_step_eq_iff_exists_witness α β v b).mp hflat
  have hu_wit := (lres_a_step_one_iff_forall_witness α β u b).mp hone
  have huv_lt : u < v := huv.1
  have huv_le : u + 1 ≤ v + 1 := by omega
  obtain ⟨l', hl', hll'⟩ :=
    lres_witness_move_a_down_of_le α β (u + 1) (v + 1) b l huv_le hl
  refine ⟨huv.1, ?_⟩
  exact lt_of_lt_of_le (lt_of_lt_of_le hαv hll') (hu_wit l' hl')

/-- Right residual forms a reduced product with the inverse of its left
factor. *Corollary 4.15 (`cor:reducedResR`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 1/2.* -/
theorem reducedProduct_of_rres (α β : AspPerm) :
    AspPerm.ReducedProduct α⁻¹ (α ▹ β) := by
  -- Proof written by Codex.
  have hred : AspPerm.ReducedProduct (β⁻¹ ◃ α⁻¹) α := by
    simpa only [inv_inv] using reducedProduct_of_lres β⁻¹ α⁻¹
  have hswap :=
    (AspPerm.reducedProduct_inv_swap (β⁻¹ ◃ α⁻¹) α).mp hred
  simpa only [AspPerm.inverse_lres, inv_inv] using hswap

/-- Right residual is below its right factor in left weak order.
*Corollary 4.15 (`cor:reducedResR`) of
[An extended Demazure product](https://arxiv.org/abs/2206.14227), part 2/2.* -/
theorem lel_of_rres (α β : AspPerm) : α ▹ β ≤L β := by
  -- Proof written by Codex.
  have h := AspPerm.le_weak_L_of_R (ler_of_lres β⁻¹ α⁻¹)
  simpa only [AspPerm.inverse_lres, inv_inv] using h

end Submodular
