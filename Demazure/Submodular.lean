import Demazure.AspPerm
import Demazure.Valley

/-- The ``Demazure valley of α β a b is the function of l that
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

lemma DemValley_min_eq_s {α β τ : AspPerm} (dprod : τ.eq_dprod α β) (a b : ℤ) :
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
lemma DemValley_step_a (α β : AspPerm) (a b : ℤ) :
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
lemma DemValley_step_b (α β : AspPerm) (a b : ℤ) :
  let v := (AspValley α β a b).shift_down 1
  let w := AspValley α β a (b+1)
  w.min = v.min + (if v.M ≤ β b then 1 else 0) ∧ v.M ≤ w.M := by
  intro v w
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

lemma DemValley_noninc (α β : AspPerm) (a b c : ℤ) (b_le_c : b ≤ c) :
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
    have := (DemValley_step_b α β a (b + n)).2
    rw [((AspValley α β a (b + ↑n))).shift_down_M] at this
    refine le_trans this ?_
    apply le_of_eq
    congr 2
    rw [Nat.cast_add, add_assoc, Nat.cast_one]

/-- Lemma 4.9, part 1 -/
theorem lel_of_dprod {τ α β : AspPerm} (dprod : τ.eq_dprod α β) : β ≤L τ := by
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
    have := (DemValley_step_b α β a u).1
    simp [Valley.shift_down_M, Valley.shift_down_min] at this
    subst val_au
    simp [h] at this
    rw [DemValley_min_eq_s dprod a (u+1), DemValley_min_eq_s dprod a u, τ.b_step_eq_iff a u] at this
    exact this
  have Mav_le_βv : val_av.M ≤ β v := by
    by_contra h

    have := (DemValley_step_b α β a v).1
    simp [Valley.shift_down_M, Valley.shift_down_min] at this
    subst val_av
    simp [h] at this
    rw [DemValley_min_eq_s dprod a (v+1), DemValley_min_eq_s dprod a v,
      τ.b_step_one_iff a v] at this
    exact lt_irrefl a this
  have Mau_le_Mav : val_au.M ≤ val_av.M := by
    apply DemValley_noninc α β a u v
    exact le_of_lt u_lt_v
  omega

/-- Lemma 4.9, part 2 -/
theorem ler_of_dprod {τ α β : AspPerm} (dprod : τ.eq_dprod α β) : α ≤R τ := by
  suffices α⁻¹ ≤L τ⁻¹ by
    simpa using AspPerm.le_weak_R_of_L this
  apply lel_of_dprod (α := β⁻¹) (β := α⁻¹) (τ := τ⁻¹)
  exact AspPerm.dprod_inv_eq_inv_dprod τ α β dprod
