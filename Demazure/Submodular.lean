import Demazure.AspPerm
import Demazure.Valley
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace Submodular

lemma unique_a_helper {s : SlipFace} (hsub : s.submodular)
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

lemma unique_a {s : SlipFace} (hsub : s.submodular) (b : ℤ) :
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
  · simp; exact hΓ
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
    apply Finset.sum_eq_add_sum_diff_singleton a_Ico
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

lemma unique_b {s : SlipFace} (hsub : s.submodular) (a : ℤ) :
  ∃! b : ℤ, ⟨a, b⟩ ∈ s.Γ := by
  suffices ∃! b : ℤ, ⟨b, a⟩ ∈ s.dual.Γ by
    simpa [s.Γ_dual] using this
  have hsub_dual : s.dual.submodular := by
    intro a b
    rw [← s.dual.Δ_dual, s.dual_dual]
    exact hsub b a
  exact unique_a hsub_dual a

noncomputable def asp_func {s : SlipFace} (hsub : s.submodular) : ℤ → ℤ :=
  fun b => (unique_a hsub b).choose

lemma asp_func_spec {s : SlipFace} (hsub : s.submodular) (a b : ℤ) :
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

lemma asp_bijective {s : SlipFace} (hsub : s.submodular) :
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
        simpa using mem
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
        simpa using mem
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
      simp [lt, ge]

    apply Set.Finite.subset _ this
    apply Set.finite_Ico

theorem asp_spec (s : SlipFace) (hsub : s.submodular) :
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
    simp [ite]
    congr 1
    rw [And.comm]
  simp [ite]
  rw [τ.s_eq_se_card]
  suffices τ.se_finset a b = {x ∈ Finset.Ico b B | A ≤ τ.func x ∧ τ.func x < a} by congr
  ext b'
  simp only [τ.mem_se, Finset.mem_filter, Finset.mem_Ico]

  by_cases h : b' < b
  · have : ¬ (b' ≥ b) := by linarith
    simp [this]
  have b_le_b' : b ≤ b' := by linarith
  simp [b_le_b']

  by_cases h : τ b' ≥ a
  · have : ¬ (τ b' < a) := by linarith
    simp [this]
  have τb'_lt_a : τ b' < a := by linarith
  simp [τb'_lt_a]
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

/-- Proposition 4.3 -/
theorem submodular_iff_asp (s : SlipFace) : s.submodular ↔ ∃ α : AspPerm, α.sf = s := by
  constructor
  · intro hsub
    use asp hsub
    exact asp_spec s hsub
  · rintro ⟨α, rfl⟩
    exact α.submodular


/-- The `Demazure valley` of `α β a b` is the function of `l` that
  is minimized to compute sα ⋆ sβ (a,b). It is useful to consider
  the largest l where the minimum is attained, which is denoted
  M_{α ⋆ β}(a,b) in Definition 4.5. -/
noncomputable def AspValley (α β : AspPerm) (a b : ℤ) : Valley where
    f := fun l => α.s a l + β.s l b
    rises := by
      intro m
      let L := a - m + α.χ
      let R := b + m - β.χ
      suffices {n : ℤ | α.s a n + β.s n b ≤ m} ⊆ Finset.Icc L R by
        apply Set.Finite.subset _ this
        apply Set.Finite.ofFinset (Finset.Icc L R)
        intro x; simp
      intro n hn
      simp at hn
      suffices n ≥ L ∧ n ≤ R by simpa
      constructor
      · linarith [β.s_nonneg n b, α.s_ge a n]
      · linarith [α.s_nonneg a n, β.s_ge n b]

lemma AspSlipValley (α β : AspPerm) (a b : ℤ) :
  (AspValley α β a b) = (SlipFace.SlipValley α.sf β.sf a b) := by
  suffices (AspValley α β a b).f = (SlipFace.SlipValley α.sf β.sf a b).f by
    rwa [Valley.mk.injEq]
  ext l
  dsimp [AspValley, SlipFace.SlipValley, AspPerm.sf]

lemma AspValley_min_eq_s {α β τ : AspPerm} (dprod : τ.eq_dprod α β) (a b : ℤ) :
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

/-- Lemma 4.6 -/
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

/-- Lemma 4.7, in slightly different phrasing. -/
lemma AspValley_step_a (α β : AspPerm) (a b : ℤ) :
  let v := AspValley α β a b
  let w := AspValley α β (a+1) b
  w.min = v.min + (if v.M ≤ α⁻¹ a then 1 else 0) ∧ v.M ≤ w.M := by
  intro v w
  have : ∀ n : ℤ, w.f n = v.f n + (if n ≤ α⁻¹ a then 1 else 0) := by
    intro n
    subst v w; simp [AspValley]
    rw [α.a_step a n]
    omega
  have low : (∀ n : ℤ, n ≤ α⁻¹ a → w.f n = v.f n + 1) := by
    intro n hn
    rw [this n, if_pos hn]
  have high : (∀ n : ℤ, n > α⁻¹ a → w.f n = v.f n) := by
    intro n hn
    rw [this n]
    simp [hn]
  have sed := sediment v w low high
  by_cases h : v.M ≤ α⁻¹ a
  · simp [h]
    exact ⟨sed.1.1 h, sed.2⟩
  · simp [h]
    exact ⟨sed.1.2 (lt_of_not_ge h), sed.2⟩

/-- Lemma 4.8, in slightly different phrasing. -/
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
    subst v w; simp [AspValley]
    rw [β.b_step n b]
    unfold Valley.shift_down
    by_cases h : n ≤ β b
    · simp [h]
    · simp [not_le.mp h]
      omega
  have low : (∀ n : ℤ, n ≤ β b → w.f n = v.f n + 1) := by
    intro n hn
    rw [this n, if_pos hn]
  have high : (∀ n : ℤ, n > β b → w.f n = v.f n) := by
    intro n hn
    rw [this n, if_neg (not_le.mpr hn), add_zero]
  have sed := sediment v w low high
  by_cases h : v.M ≤ β b
  · simp [h]
    exact ⟨sed.1.1 h, sed.2⟩
  · simp [h]
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

/-- A useful submodularity criterion: s is submodular at a, b if and only if
  s (a+1) b not dropping when b increasing implies the same is true of
  s a b. This corresponds to the geometric situation: if a linear series L has a
  base point at p, then so does L - q if q ≠ p. -/
lemma submodular_of_basepoint_preserved (s : SlipFace) (a b : ℤ) :
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

/-- Theorem 4.4, part 1/5 -/
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
  simp at this
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
  simp [M_le_βb]

end Submodular

/- Back to AspPerm namespace to define Demazure product and its properties. -/
namespace AspPerm

lemma eq_of_sf_eq {α β : AspPerm} (eq_sf : α.sf = β.sf) : α = β := by
  suffices α.func = β.func by
    cases α; cases β
    congr
  ext n
  have : β.sf.Δ (β n) n = 1 := by
    simpa using β.Δ_eq (β n) n
  rw [← eq_sf] at this
  rw [α.Δ_eq (β n) n] at this
  contrapose! this with neq
  simp [neq]

/-- Theorem 4.4, part 2/5 -/
lemma star_exists : ∀ α β : AspPerm, ∃! τ : AspPerm, τ.sf = α.sf ⋆ β.sf := by
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

noncomputable def star (α β : AspPerm) : AspPerm :=
  Classical.choose (star_exists α β)

@[simp] lemma star_spec (α β : AspPerm) : (star α β).sf = α.sf ⋆ β.sf :=
  (Classical.choose_spec (star_exists α β)).1

infixl:70 " ⋆ " => star

/-- Theorem 4.4, part 3/5 -/
lemma star_assoc : ∀ α β γ : AspPerm, (α ⋆ β) ⋆ γ = α ⋆ (β ⋆ γ) := by
  intro α β γ
  apply AspPerm.eq_of_sf_eq
  simp only [star_spec, SlipFace.star_assoc]

lemma star_valley (α β : AspPerm) (a b : ℤ) : (α ⋆ β).s a b
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

/-- Theorem 4.4, part 4/5 -/
lemma inverse_star (α β : AspPerm) : (α ⋆ β)⁻¹ = β⁻¹ ⋆ α⁻¹ := by
  have ex := star_exists (β⁻¹) (α⁻¹)
  let τ := β⁻¹ ⋆ α⁻¹
  have τ_eq : τ.sf = β⁻¹.sf ⋆ α⁻¹.sf  := (ex.choose_spec).1
  apply (ex.choose_spec).2 (α ⋆ β)⁻¹
  simp only [SF_ext]
  intro a b
  repeat rw [← AspPerm.sf_dual]
  simp

/-- Theorem 4.4, part 5/5 -/
lemma chi_star (α β : AspPerm) : (α ⋆ β).χ = α.χ + β.χ := by
  have ex := star_exists α β
  let τ := α ⋆ β
  have τ_eq : τ.sf = α.sf ⋆ β.sf  := (ex.choose_spec).1
  repeat rw [← AspPerm.sf_chi_eq]
  simp [SlipFace.chi_star]

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
    simp [Int.card_Ico b a]
  rw [hcard]
  by_cases h : a - b ≥ 0
  · rw [max_eq_left h, Int.toNat_of_nonneg h]
  · have h' : a - b < 0 := lt_of_not_ge h
    rw [max_eq_right (le_of_lt h')]
    have : (a - b).toNat = 0 := Int.toNat_of_nonpos (le_of_lt h')
    simp [this]

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

def le_chi (σ τ : AspPerm) : Prop := σ ≤ τ ∧ σ.χ = τ.χ
infix:50 " ≤χ " => le_chi

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
    apply le_trans _ hl
    suffices v.f v.M ≤ v.f l by
      convert this using 1
      rw [star_valley]
      rw [v.f_M]
    rw [v.f_M]
    exact v.min_spec l

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

namespace Submodular

/-- Lemma 4.9, part 1 -/
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
    simp [h] at this
    rw [AspValley_min_eq_s dprod a (u + 1), AspValley_min_eq_s dprod a u,
      τ.b_step_eq_iff a u] at this
    exact this
  have Mav_le_βv : val_av.M ≤ β v := by
    by_contra h

    have := (AspValley_step_b α β a v).1
    subst val_av
    simp [h] at this
    rw [AspValley_min_eq_s dprod a (v+1), AspValley_min_eq_s dprod a v,
      τ.b_step_one_iff a v] at this
    exact lt_irrefl a this
  have Mau_le_Mav : val_au.M ≤ val_av.M := by
    apply AspValley_noninc α β a u v
    exact le_of_lt u_lt_v
  omega

/-- Lemma 4.9, part 2 -/
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

end Submodular
