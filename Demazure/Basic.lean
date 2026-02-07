import Mathlib

def southeast_set (τ : ℤ → ℤ) (m n : ℤ) : Set ℤ := { k : ℤ | n ≤ k ∧ τ k < m }

def northwest_set (τ : ℤ → ℤ) (m n : ℤ) : Set ℤ := { k : ℤ | k < n ∧ m ≤ τ k }

lemma se_finite_of_finite {τ : ℤ → ℤ} (h_inj : Function.Injective τ) (m n m' n' : ℤ) :
  (southeast_set τ m n).Finite → (southeast_set τ m' n').Finite := by
  let A := southeast_set τ m n
  let B := southeast_set τ m' n'
  let V := (Finset.Ico n' n).toSet
  let H₀ := (Finset.Ico m m').toSet
  let H := τ⁻¹' H₀

  change A.Finite → B.Finite
  intro fin_A

  have fin_V : V.Finite := by
    apply Finset.finite_toSet

  have fin_H₀ : H₀.Finite := by
    apply Finset.finite_toSet

  have fin_H : H.Finite := by
    refine Set.Finite.preimage ?_ fin_H₀
    exact Set.injOn_of_injective h_inj

  have h : B ⊆ A ∪ (H ∪ V) := by
    intro k hk
    simp [A, B] at hk ⊢
    unfold southeast_set at *
    by_cases k_lt_n : k < n
    · right; right
      simp only [V]
      simp [hk.1, k_lt_n]
    obtain k_ge_n : k ≥ n := by
      push_neg at k_lt_n; exact k_lt_n
    by_cases τk_ge_m : τ k ≥ m
    · right; left
      simp only [H, H₀]
      simp [τk_ge_m, hk.2]
    obtain τk_lt_m : τ k < m := by
      push_neg at τk_ge_m; exact τk_ge_m
    left; exact ⟨k_ge_n, τk_lt_m⟩

  refine Set.Finite.subset ?_ h
  exact Set.Finite.union fin_A (Set.Finite.union fin_H fin_V)

lemma nw_finite_of_finite {τ : ℤ → ℤ} (h_inj : Function.Injective τ) (m n m' n' : ℤ) :
  (northwest_set τ m n).Finite → (northwest_set τ m' n').Finite := by
  let A := northwest_set τ m n
  let B := northwest_set τ m' n'
  let V := (Finset.Ico n n').toSet
  let H₀ := (Finset.Ico m' m).toSet
  let H := τ⁻¹' H₀

  change A.Finite → B.Finite
  intro fin_A

  have fin_V : V.Finite := by
    apply Finset.finite_toSet

  have fin_H₀ : H₀.Finite := by
    apply Finset.finite_toSet

  have fin_H : H.Finite := by
    refine Set.Finite.preimage ?_ fin_H₀
    exact Set.injOn_of_injective h_inj

  have h : B ⊆ A ∪ (H ∪ V) := by
    intro k hk
    simp [A, B] at hk ⊢
    unfold northwest_set at *
    by_cases k_ge_n : k ≥ n
    · right; right
      simp only [V]
      simp [hk.1, k_ge_n]
    obtain k_lt_n : k < n := by
      push_neg at k_ge_n; exact k_ge_n
    by_cases τk_lt_m : τ k < m
    · right; left
      simp only [H, H₀]
      simp [τk_lt_m, hk.2]
    obtain τk_ge_m : τ k ≥ m := by
      push_neg at τk_lt_m; exact τk_lt_m
    left
    exact ⟨k_lt_n, τk_ge_m⟩

  refine Set.Finite.subset ?_ h
  exact Set.Finite.union fin_A (Set.Finite.union fin_H fin_V)

def is_asp (τ : ℤ → ℤ) : Prop :=
  { n : ℤ | n * (τ n) < 0 }.Finite

lemma se_finite_of_asp {τ : ℤ → ℤ} (h_inj : Function.Injective τ) (m n : ℤ) :
  is_asp τ → (southeast_set τ m n).Finite := by
  intro h_asp
  have h_se : (southeast_set τ 0 1).Finite := by
    unfold is_asp at h_asp
    have : southeast_set τ 0 1 ⊆ { n : ℤ | n * (τ n) < 0 } := by
      intro k hk
      simp [southeast_set] at hk
      obtain ⟨k_pos, τk_neg⟩ := hk
      have : k > 0 := by linarith
      exact mul_neg_of_pos_of_neg this τk_neg
    exact Set.Finite.subset h_asp this
  exact se_finite_of_finite h_inj 0 1 m n h_se

lemma nw_finite_of_asp {τ : ℤ → ℤ} (h_inj : Function.Injective τ) (m n : ℤ) :
  is_asp τ → (northwest_set τ m n).Finite := by
  intro h_asp
  have h_nw : (northwest_set τ 1 0).Finite := by
    unfold is_asp at h_asp
    have : northwest_set τ 1 0 ⊆ { n : ℤ | n * (τ n) < 0 } := by
      intro k hk
      simp [northwest_set] at hk
      obtain ⟨k_neg, τk_pos⟩ := hk
      have : τ k > 0 := by linarith
      exact mul_neg_of_neg_of_pos k_neg this
    exact Set.Finite.subset h_asp this
  exact nw_finite_of_finite h_inj 1 0 m n h_nw

lemma asp_of_finite_quadrants {τ : ℤ → ℤ} (h_inj : Function.Injective τ)
  {m n m' n' : ℤ} (fin_se : (southeast_set τ m n).Finite)
  (fin_nw : (northwest_set τ m' n').Finite) :
  is_asp τ := by
  unfold is_asp
  have : { n : ℤ | n * (τ n) < 0 } ⊆ (southeast_set τ 0 1) ∪ (northwest_set τ 1 0) := by
    intro n hn; simp at hn
    have := mul_neg_iff.mp hn
    rcases this with (pos_neg | neg_pos)
    · left
      unfold southeast_set
      simp; congr
    · right
      unfold northwest_set
      simp; congr
  refine Set.Finite.subset ?_ this
  apply Set.Finite.union
  · exact se_finite_of_finite h_inj m n 0 1 fin_se
  · exact nw_finite_of_finite h_inj m' n' 1 0 fin_nw
