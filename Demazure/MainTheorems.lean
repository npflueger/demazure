import Demazure.ReducedProducts

/-! ### Main theorems: greediness and the reduction theorem

This file formalizes the main theorems from the introduction of the paper:
Theorem B (`thm:starGreedy`) characterizes `α ⋆ β` as a greedy maximum, and
Theorem C (`thm:reduce`) reduces inequalities `α ⋆ β ≥ γ` to equalities of
reduced products. -/

namespace MainTheorems

open AspPerm

/-! ### Bookkeeping helpers -/

/-- Multiplying `α ⋆ β` on the right by `β⁻¹` recovers a permutation that lies
weakly below `α` in Bruhat order, has the same shift as `α`, and whose
product with `β` (ordinary or Demazure) returns `α ⋆ β`. -/
lemma star_left_witness (α β : AspPerm) :
    let α₁ := (α ⋆ β) * β⁻¹
    α₁ * β = α ⋆ β ∧ α₁ ⋆ β = α ⋆ β ∧ α₁ ≤χ α := by
  -- Proof written by Claude Opus 4.7.
  set α₁ := (α ⋆ β) * β⁻¹ with hα₁_def
  have h_mul : α₁ * β = α ⋆ β := by
    rw [hα₁_def, mul_assoc, inv_mul_cancel, mul_one]
  have hβL : β ≤L α ⋆ β := Submodular.lel_of_dprod α β
  have h_lc_eq : (α ⋆ β) ◃ β⁻¹ = α₁ := by
    rw [hα₁_def]
    apply (ReducedProducts.left_contract_eq_mul_iff (α ⋆ β) β⁻¹).mpr
    simpa using hβL
  have h_alpha1_le : α₁ ≤ α := by
    rw [← h_lc_eq]
    exact (ge_star_iff_ge_left_contract α β (α ⋆ β)).mpr (le_refl _)
  have h_alpha1_star_ge : α₁ ⋆ β ≥ α ⋆ β := by
    apply (ge_star_iff_ge_left_contract α₁ β (α ⋆ β)).mp
    rw [h_lc_eq]
  have h_star : α₁ ⋆ β = α ⋆ β :=
    le_antisymm (star_mono h_alpha1_le (le_refl β)) h_alpha1_star_ge
  have h_chi : α₁.χ = α.χ := by
    rw [hα₁_def, AspPerm.chi_mul, AspPerm.chi_star, AspPerm.chi_dual]
    ring
  exact ⟨h_mul, h_star, h_alpha1_le, h_chi⟩

/-- Multiplying `α ⋆ β` on the left by `α⁻¹` recovers a permutation that lies
weakly below `β` in Bruhat order, has the same shift as `β`, and whose
product with `α` (ordinary or Demazure) returns `α ⋆ β`. -/
lemma star_right_witness (α β : AspPerm) :
    let β₁ := α⁻¹ * (α ⋆ β)
    α * β₁ = α ⋆ β ∧ α ⋆ β₁ = α ⋆ β ∧ β₁ ≤χ β := by
  -- Proof written by GPT 5.5.
  obtain ⟨h_mul, h_star, h_leχ⟩ := star_left_witness β⁻¹ α⁻¹
  simp only [inv_inv] at h_mul h_star h_leχ
  refine ⟨?_, ?_, ?_⟩
  · simpa only [mul_inv_rev, AspPerm.inverse_star, inv_inv] using
      congrArg (fun τ : AspPerm => τ⁻¹) h_mul
  · simpa only [AspPerm.inverse_star, mul_inv_rev, inv_inv] using
      congrArg (fun τ : AspPerm => τ⁻¹) h_star
  · simpa only [mul_inv_rev, AspPerm.inverse_star, inv_inv] using
      (AspPerm.le_chi_inv_iff ((β⁻¹ ⋆ α⁻¹) * α) β⁻¹).mp h_leχ

/-! ### Theorem B: greedy characterization of `⋆` -/

/-- *Theorem B (`thm:starGreedy`)*, equation \eqref{eq:starGreedyAlpha}.

`α ⋆ β` is the Bruhat-maximum of the set
$\{ \alpha_1 \beta : \alpha_1 \leq_\chi \alpha\}$. -/
theorem starGreedy_alpha (α β : AspPerm) :
    IsGreatest { α₁ * β | (α₁ : AspPerm) (_ : α₁ ≤χ α) }
      (α ⋆ β) := by
  -- Proof written by Claude Opus 4.7.
  obtain ⟨h_mul, _, h_chi⟩ := star_left_witness α β
  refine ⟨⟨(α ⋆ β) * β⁻¹, h_chi, h_mul⟩, ?_⟩
  rintro τ ⟨α₁, hα₁_le, rfl⟩
  exact le_trans (ReducedProducts.mul_le_star α₁ β) (star_mono hα₁_le.1 (le_refl β))

/-- *Theorem B (`thm:starGreedy`)*, equation \eqref{eq:starGreedyBeta}.

`α ⋆ β` is the Bruhat-maximum of the set
$\{ \alpha \beta_1 : \beta_1 \leq_\chi \beta\}$. -/
theorem starGreedy_beta (α β : AspPerm) :
    IsGreatest { α * β₁ | (β₁ : AspPerm) (_ : β₁ ≤χ β) }
      (α ⋆ β) := by
  -- Proof written by Claude Opus 4.7.
  obtain ⟨h_mul, _, h_chi⟩ := star_right_witness α β
  refine ⟨⟨α⁻¹ * (α ⋆ β), h_chi, h_mul⟩, ?_⟩
  rintro τ ⟨β₁, hβ₁_le, rfl⟩
  exact le_trans (ReducedProducts.mul_le_star α β₁) (star_mono (le_refl α) hβ₁_le.1)

/-- *Theorem B (`thm:starGreedy`)*, equation \eqref{eq:starGreedy}.

`α ⋆ β` is the Bruhat-maximum of the set
$\{ \alpha_1 \beta_1 : \alpha_1 \leq \alpha, \beta_1 \leq \beta\}$. -/
theorem starGreedy (α β : AspPerm) :
    IsGreatest
      { α₁ * β₁ | (α₁ : AspPerm) (_ : α₁ ≤ α) (β₁ : AspPerm) (_ : β₁ ≤ β) }
      (α ⋆ β) := by
  -- Proof written by Claude Opus 4.7.
  -- Membership: the witness from `starGreedy_alpha` works with `β₁ = β`.
  obtain ⟨h_mul, _, h_chi_le⟩ := star_left_witness α β
  refine ⟨⟨(α ⋆ β) * β⁻¹, h_chi_le.1, β, le_refl β, h_mul⟩, ?_⟩
  rintro τ ⟨α₁, hα₁_le, β₁, hβ₁_le, rfl⟩
  exact le_trans (ReducedProducts.mul_le_star α₁ β₁) (star_mono hα₁_le hβ₁_le)

/-! ### Theorem C: reduction theorem for `α ⋆ β ≥ γ` -/

/-- *Theorem C (`thm:reduce`)*, second paragraph, Bruhat part.

If `α ⋆ β ≥ γ`, then `α₁ = γ ◃ β⁻¹` and `β₁ = α₁⁻¹ ▹ γ` satisfy
`α₁ ⋆ β₁ = α₁ * β₁ = γ` and `α₁ ≤ α`, `β₁ ≤ β`. -/
theorem reduce_witness (α β γ : AspPerm) (h : α ⋆ β ≥ γ) :
    let α₁ := γ ◃ β⁻¹
    let β₁ := α₁⁻¹ ▹ γ
    α₁ * β₁ = γ ∧ α₁ ⋆ β₁ = γ ∧ α₁ ≤ α ∧ β₁ ≤ β := by
  -- Proof written by Claude Opus 4.7.
  set α₁ := γ ◃ β⁻¹ with hα₁_def
  set β₁ := α₁⁻¹ ▹ γ with hβ₁_def
  -- Universal property of `◃`: `α₁ ≤ α` since `α ⋆ β ≥ γ`.
  have h_alpha1_le : α₁ ≤ α := (ge_star_iff_ge_left_contract α β γ).mpr h
  -- Universal property again: `α₁ ⋆ β ≥ γ`.
  have h_alpha1_star_ge : α₁ ⋆ β ≥ γ :=
    (ge_star_iff_ge_left_contract α₁ β γ).mp (le_refl _)
  -- Universal property of `▹`: `β₁ ≤ β`.
  have h_beta1_le : β₁ ≤ β :=
    (ge_star_iff_ge_right_contract α₁ β γ).mpr h_alpha1_star_ge
  -- `α₁ ⋆ β₁ ≥ γ` (achieved by `β₁ ≥ β₁`).
  have h_alpha1_star_beta1_ge : α₁ ⋆ β₁ ≥ γ :=
    (ge_star_iff_ge_right_contract α₁ β₁ γ).mp (le_refl _)
  -- `α₁ ≤R γ` (Lemma 4.14 / Cor 4.15), so by Lemma 5.2 right contraction
  -- collapses to the ordinary product `α₁⁻¹ * γ`.
  have h_alpha1_R : α₁ ≤R γ := Submodular.ler_of_left_contract γ β⁻¹
  have h_rc_eq : β₁ = α₁⁻¹ * γ := by
    rw [hβ₁_def]
    apply (ReducedProducts.right_contract_eq_mul_iff α₁⁻¹ γ).mpr
    simpa using h_alpha1_R
  -- Ordinary product collapses.
  have h_mul : α₁ * β₁ = γ := by
    rw [h_rc_eq, ← mul_assoc, mul_inv_cancel, one_mul]
  -- The pair `(α₁, β₁)` is reduced (Lemma 2.9), so `⋆` agrees with `*`.
  have h_reduced : AspPerm.ReducedProduct α₁ β₁ := by
    apply (AspPerm.reducedProduct_iff_le_weak_R_mul α₁ β₁).mpr
    rw [h_mul]
    exact h_alpha1_R
  have h_star_eq_mul : α₁ ⋆ β₁ = α₁ * β₁ :=
    (ReducedProducts.star_eq_mul_iff_reducedProduct α₁ β₁).mpr h_reduced
  have h_star : α₁ ⋆ β₁ = γ := h_star_eq_mul.trans h_mul
  exact ⟨h_mul, h_star, h_alpha1_le, h_beta1_le⟩

/-- *Theorem C (`thm:reduce`)*, second paragraph, including the shift
identities. Under the additional hypothesis $\chi_\alpha + \chi_\beta =
\chi_\gamma$ (which makes both shift equalities meaningful), we further have
$\alpha_1 \leq_\chi \alpha$ and $\beta_1 \leq_\chi \beta$. -/
theorem reduce_witness_chi (α β γ : AspPerm) (hχ : α.χ + β.χ = γ.χ)
    (h : α ⋆ β ≥ γ) :
    let α₁ := γ ◃ β⁻¹
    let β₁ := α₁⁻¹ ▹ γ
    α₁ * β₁ = γ ∧ α₁ ⋆ β₁ = γ ∧ α₁ ≤χ α ∧ β₁ ≤χ β := by
  -- Proof written by Claude Opus 4.7.
  obtain ⟨h_mul, h_star, h_alpha1_le, h_beta1_le⟩ := reduce_witness α β γ h
  set α₁ := γ ◃ β⁻¹ with hα₁_def
  set β₁ := α₁⁻¹ ▹ γ with hβ₁_def
  have h_chi_alpha : α₁.χ = α.χ := by
    rw [hα₁_def, AspPerm.chi_left_contract, AspPerm.chi_dual]
    linarith
  have h_chi_beta : β₁.χ = β.χ := by
    rw [hβ₁_def, AspPerm.chi_right_contract, AspPerm.chi_dual, h_chi_alpha]
    linarith
  exact ⟨h_mul, h_star, ⟨h_alpha1_le, h_chi_alpha⟩, ⟨h_beta1_le, h_chi_beta⟩⟩

/-- *Theorem C (`thm:reduce`)*, first paragraph, ASP form.

For all `α, β, γ ∈ ASP` with `α.χ + β.χ = γ.χ`, the inequality `α ⋆ β ≥ γ`
is equivalent to the existence of `α₁, β₁` with `α₁ ≤χ α`, `β₁ ≤χ β`, and
`α₁ ⋆ β₁ = α₁ * β₁ = γ`. -/
theorem reduce (α β γ : AspPerm) (hχ : α.χ + β.χ = γ.χ) :
    α ⋆ β ≥ γ ↔
      ∃ α₁ β₁ : AspPerm,
        α₁ ≤χ α ∧ β₁ ≤χ β ∧ α₁ ⋆ β₁ = γ ∧ α₁ * β₁ = γ := by
  -- Proof written by Claude Opus 4.7.
  constructor
  · intro h
    obtain ⟨h_mul, h_star, h_chi_α, h_chi_β⟩ := reduce_witness_chi α β γ hχ h
    exact ⟨_, _, h_chi_α, h_chi_β, h_star, h_mul⟩
  · rintro ⟨α₁, β₁, ⟨hα₁_le, _⟩, ⟨hβ₁_le, _⟩, h_star, _⟩
    rw [← h_star]
    exact star_mono hα₁_le hβ₁_le

/-! ### Theorem `tllStingy`: stingy characterization of `◃`

The dual story for `◃`, mirroring Theorem B. Equation \eqref{eq:tllGreedyAlpha}
in the paper. -/

/-- The contraction `α ◃ β⁻¹` is monotone in `α` for fixed `β`.

This is the ASP-level lift of `SlipFace.left_contract_mono`. -/
lemma left_contract_inv_mono_alpha {α α' β : AspPerm} (hα : α ≤ α') :
    α ◃ β⁻¹ ≤ α' ◃ β⁻¹ := by
  -- Proof written by Claude Opus 4.7.
  apply (sf_le_iff (α ◃ β⁻¹) (α' ◃ β⁻¹)).mp
  rw [left_contract_spec, left_contract_spec, ← sf_dual]
  exact SlipFace.left_contract_mono ((sf_le_iff α α').mpr hα) (le_refl β.sf)

/-- The contraction `α ◃ β⁻¹` is anti-monotone in `β`: if `β' ≤ β` then
`α ◃ β⁻¹ ≤ α ◃ β'⁻¹`. -/
lemma left_contract_inv_antimono_beta {α β β' : AspPerm} (hβ : β' ≤ β) :
    α ◃ β⁻¹ ≤ α ◃ β'⁻¹ := by
  -- Proof written by Claude Opus 4.7.
  apply (sf_le_iff (α ◃ β⁻¹) (α ◃ β'⁻¹)).mp
  rw [left_contract_spec, left_contract_spec, ← sf_dual, ← sf_dual]
  exact SlipFace.left_contract_mono (le_refl α.sf) ((sf_le_iff β' β).mpr hβ)

/-- *Theorem `tllStingy`*, equation \eqref{eq:tllGreedyAlpha}.

`α ◃ β⁻¹` is the Bruhat-minimum of the set
$\{\alpha_1 \beta^{-1}: \alpha_1 \geq_\chi \alpha\}$. -/
theorem tllStingy_alpha (α β : AspPerm) :
    IsLeast { α₁ * β⁻¹ | (α₁ : AspPerm) (_ : α ≤χ α₁) } (α ◃ β⁻¹) := by
  -- Proof written by Claude Opus 4.7.
  -- Membership: take α₁ = (α ◃ β⁻¹) * β.
  set α₁ := (α ◃ β⁻¹) * β with hα₁_def
  have h_alpha1_eq : α₁ = α ◃ β⁻¹ * β := hα₁_def
  -- The pair `(α ◃ β⁻¹, β)` is reduced (Lemma 4.14 applied to β⁻¹).
  have h_red : AspPerm.ReducedProduct (α ◃ β⁻¹) β := by
    have := Submodular.reducedProduct_of_left_contract α β⁻¹
    simpa using this
  have h_star_eq_mul : (α ◃ β⁻¹) ⋆ β = (α ◃ β⁻¹) * β :=
    (ReducedProducts.star_eq_mul_iff_reducedProduct _ _).mpr h_red
  have h_alpha1_star : α₁ = (α ◃ β⁻¹) ⋆ β := h_star_eq_mul.symm
  -- The universal property of `◃` gives `α₁ ≥ α`.
  have h_alpha_le_alpha1 : α ≤ α₁ := by
    rw [h_alpha1_star]
    exact (ge_star_iff_ge_left_contract (α ◃ β⁻¹) β α).mp (le_refl _)
  -- Shift: χ_{α₁} = χ_{α ◃ β⁻¹} + χ_β = (χ_α - χ_β) + χ_β = χ_α.
  have h_chi : α.χ = α₁.χ := by
    rw [hα₁_def, AspPerm.chi_mul, AspPerm.chi_left_contract, AspPerm.chi_dual]
    ring
  -- And α₁ * β⁻¹ = α ◃ β⁻¹ by cancellation.
  have h_α₁β_eq : α₁ * β⁻¹ = α ◃ β⁻¹ := by
    rw [hα₁_def, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨⟨α₁, ⟨h_alpha_le_alpha1, h_chi⟩, h_α₁β_eq⟩, ?_⟩
  -- Lower bound: any candidate is ≥ α ◃ β⁻¹.
  rintro τ ⟨α₂, hα₂_le, rfl⟩
  exact le_trans (left_contract_inv_mono_alpha hα₂_le.1)
                 (ReducedProducts.left_contract_le_mul α₂ β⁻¹)

/-- *Theorem `tllStingy`*, equation \eqref{eq:tllGreedyBeta}.

`α ◃ β⁻¹` is the Bruhat-minimum of the set
$\{\alpha \beta_1^{-1}: \beta_1 \leq_\chi \beta\}$. -/
theorem tllStingy_beta (α β : AspPerm) :
    IsLeast { α * β₁⁻¹ | (β₁ : AspPerm) (_ : β₁ ≤χ β) } (α ◃ β⁻¹) := by
  -- Proof written by Claude Opus 4.7.
  set β₁ := (β ▹ α⁻¹) * α with hβ₁_def
  -- Useful identity from `inverse_left_contract`.
  have h_lc_inv : (β ▹ α⁻¹)⁻¹ = α ◃ β⁻¹ := by
    have := AspPerm.inverse_left_contract α β⁻¹
    -- `(α ◃ β⁻¹)⁻¹ = β ▹ α⁻¹`, hence inverting gives the desired identity.
    have h := congrArg (·⁻¹) this
    simpa using h.symm
  have h_lc_inv' : (α ◃ β⁻¹)⁻¹ = β ▹ α⁻¹ := by
    have := AspPerm.inverse_left_contract α β⁻¹
    simpa using this
  -- `(α ◃ β⁻¹) ≤R α` (Lemma 4.14), so `(β ▹ α⁻¹)⁻¹ ≤R α`, i.e. Lemma 5.2
  -- collapses `(β ▹ α⁻¹) ▹ α` to the ordinary product `β₁`.
  have h_le_R : (β ▹ α⁻¹)⁻¹ ≤R α := by
    rw [h_lc_inv]
    exact Submodular.ler_of_left_contract α β⁻¹
  have h_rc_eq : (β ▹ α⁻¹) ▹ α = β₁ := by
    rw [hβ₁_def]
    exact (ReducedProducts.right_contract_eq_mul_iff (β ▹ α⁻¹) α).mpr h_le_R
  -- `α * β₁⁻¹ = α * α⁻¹ * (α ◃ β⁻¹) = α ◃ β⁻¹`.
  have h_mul : α * β₁⁻¹ = α ◃ β⁻¹ := by
    rw [hβ₁_def, mul_inv_rev, h_lc_inv, ← mul_assoc, mul_inv_cancel, one_mul]
  -- Shift: $\chi_{\beta_1} = (\chi_\beta + \chi_{\alpha^{-1}}) + \chi_\alpha = \chi_\beta$.
  have h_chi : β₁.χ = β.χ := by
    rw [hβ₁_def, AspPerm.chi_mul, AspPerm.chi_right_contract, AspPerm.chi_dual]
    ring
  -- `β₁ ≤ β` via the universal property of `▹` applied to the witness `β`.
  have h_β1_le : β₁ ≤ β := by
    rw [← h_rc_eq]
    have hstar_ge : (α ◃ β⁻¹) ⋆ β ≥ α :=
      (ge_star_iff_ge_left_contract (α ◃ β⁻¹) β α).mp (le_refl _)
    have hβ_ge_rc : β ≥ (α ◃ β⁻¹)⁻¹ ▹ α :=
      (ge_star_iff_ge_right_contract (α ◃ β⁻¹) β α).mpr hstar_ge
    rwa [h_lc_inv'] at hβ_ge_rc
  refine ⟨⟨β₁, ⟨h_β1_le, h_chi⟩, h_mul⟩, ?_⟩
  -- Lower bound.
  rintro τ ⟨β₂, hβ₂_le, rfl⟩
  exact le_trans (left_contract_inv_antimono_beta hβ₂_le.1)
                 (ReducedProducts.left_contract_le_mul α β₂⁻¹)

/-- *Theorem `tllStingy`*, equation \eqref{eq:tllGreedy}.

`α ◃ β⁻¹` is the Bruhat-minimum of the set
$\{\alpha_1 \beta_1^{-1}: \alpha_1 \geq \alpha,\, \beta_1 \leq \beta\}$. -/
theorem tllStingy (α β : AspPerm) :
    IsLeast
      { α₁ * β₁⁻¹ | (α₁ : AspPerm) (_ : α ≤ α₁) (β₁ : AspPerm) (_ : β₁ ≤ β) }
      (α ◃ β⁻¹) := by
  -- Proof written by Claude Opus 4.7.
  obtain ⟨⟨α₁, ⟨hα₁_le, _⟩, h_α₁β_eq⟩, _⟩ := tllStingy_alpha α β
  refine ⟨⟨α₁, hα₁_le, β, le_refl β, h_α₁β_eq⟩, ?_⟩
  rintro τ ⟨α₂, hα₂_ge, β₂, hβ₂_le, rfl⟩
  -- Chain three inequalities: monotonicity in α, anti-monotonicity in β,
  -- and the basic `◃ ≤ *` (Lemma 5.2).
  refine le_trans (left_contract_inv_mono_alpha hα₂_ge) ?_
  refine le_trans (left_contract_inv_antimono_beta hβ₂_le) ?_
  exact ReducedProducts.left_contract_le_mul α₂ β₂⁻¹

/-! ### Theorem `reduceSeveral`: three- and many-fold reduction

The reduction theorem for products of three or more permutations follows
from `reduce` by induction. We prove the three-fold case explicitly, and a
fully list-based version. -/

/-- If `γ ≤ id` and the shifts match, then `γ = id`.

This is the shift-zero special case of the antisymmetry of Bruhat order. -/
lemma eq_id_of_le_id_chi_zero {γ : AspPerm} (h : γ ≤ AspPerm.id)
    (hχ : γ.χ = 0) : γ = AspPerm.id := by
  -- Proof written by Claude Opus 4.7.
  -- `γ ≤χ id`, hence `γ⁻¹ ≤χ id`, and `id ≤ γ⁻¹` (since `γ⁻¹.χ = 0 ≥ 0`).
  -- Antisymmetry gives `γ⁻¹ = id`, hence `γ = id`.
  have hχid : γ.χ = AspPerm.id.χ := by rw [hχ, AspPerm.id_chi]
  have h_le_chi : γ ≤χ AspPerm.id := ⟨h, hχid⟩
  have h_inv_le_chi : γ⁻¹ ≤χ (AspPerm.id : AspPerm)⁻¹ :=
    (AspPerm.le_chi_inv_iff γ AspPerm.id).mp h_le_chi
  -- `id⁻¹ = id`.
  have h_id_inv : (AspPerm.id : AspPerm)⁻¹ = AspPerm.id := by
    change (1 : AspPerm)⁻¹ = 1
    exact inv_one
  rw [h_id_inv] at h_inv_le_chi
  have h_inv_ge : AspPerm.id ≤ γ⁻¹ := by
    apply AspPerm.id_le_of_chi_nonneg
    rw [AspPerm.chi_dual, hχ]; exact le_refl 0
  have : γ⁻¹ = AspPerm.id := le_antisymm h_inv_le_chi.1 h_inv_ge
  have h_eq : γ = (AspPerm.id : AspPerm)⁻¹ := by
    rw [← this, inv_inv]
  rw [h_eq, h_id_inv]

/-- *Theorem `reduceSeveral`*, ASP-level (list version).

For any list of permutations `αs` and a target `γ ∈ ASP` with matching total
shift, if the Demazure product over `αs` is Bruhat-≥ `γ`, then there exists a
list of "reduced witnesses" `βs` of the same length, with `βᵢ ≤χ αᵢ`
pointwise, whose Demazure product and ordinary product both equal `γ`. -/
theorem reduceList :
    ∀ (αs : List AspPerm) (γ : AspPerm),
      (αs.map AspPerm.χ).sum = γ.χ →
      DProd αs ≥ γ →
      ∃ βs : List AspPerm,
        List.Forall₂ (fun α β => β ≤χ α) αs βs ∧
        DProd βs = γ ∧ OrdProd βs = γ
  | [], γ, hχ, h => by
      -- Proof written by Claude Opus 4.7.
      -- Base case: γ ≤ id and γ.χ = 0, hence γ = id.
      simp only [List.map_nil, List.sum_nil, DProd_nil] at hχ h
      have hγ : γ = AspPerm.id := eq_id_of_le_id_chi_zero h hχ.symm
      exact ⟨[], List.Forall₂.nil, by simp only [DProd_nil, hγ],
        by simp only [OrdProd_nil, hγ]⟩
  | (α :: αs), γ, hχ, h => by
      -- Proof written by Claude Opus 4.7.
      -- Inductive step: apply `reduce` to split off `α` from the suffix.
      have hsuff : α.χ + (DProd αs).χ = γ.χ := by
        rw [AspPerm.chi_DProd]
        simpa [List.map_cons, List.sum_cons] using hχ
      have h' : α ⋆ DProd αs ≥ γ := by
        simpa only [DProd_cons] using h
      obtain ⟨α₁, π, hα₁, hπ, h_star, h_mul⟩ :=
        (reduce α (DProd αs) γ hsuff).mp h'
      -- Inductive hypothesis on the suffix targeting `π`.
      have hπ_χ : (αs.map AspPerm.χ).sum = π.χ := by
        rw [← AspPerm.chi_DProd, hπ.2]
      obtain ⟨βs, hβs_forall, hβs_star, hβs_mul⟩ :=
        reduceList αs π hπ_χ hπ.1
      refine ⟨α₁ :: βs, List.Forall₂.cons hα₁ hβs_forall, ?_, ?_⟩
      · simp only [DProd_cons, hβs_star, h_star]
      · simp only [OrdProd_cons, hβs_mul, h_mul]

end MainTheorems
