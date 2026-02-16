import Mathlib
import Demazure.AspPerm
import Demazure.InvSet
import Demazure.Utils


namespace ASP321a

structure set_321a_prop (I : Set (ℤ × ℤ)) where
  asp : AspSet_prop I
  tfree : ∀ u v w : ℤ, ⟨u,v⟩ ∉ I ∨ ⟨v,w⟩ ∉ I

structure set_321a : Type extends AspSet where
  prop_321a : set_321a_prop I

def func_321a_prop (τ : ℤ → ℤ) : Prop :=
  ∀ (i j k : ℤ), i < j → j < k → τ i < τ j ∨ τ j < τ k

def perm_321a := { τ : ℤ → ℤ // Function.Bijective τ ∧ func_321a_prop τ }

theorem asp_of_321a (τ : perm_321a) : is_asp τ.val := by
  have ex_src : ∃ u : ℤ, ∀ n : ℤ, ⟨n,u⟩ ∉ inv_set τ.val := by
    by_cases h : ∃ u : ℤ, ⟨u,0⟩ ∈ inv_set τ.val
    · obtain ⟨u, hu⟩ := h
      use u
      intro n hn
      have h := τ.property.2 n u 0 hn.1 hu.1
      have h' := hu.2
      have h'' := hn.2
      contrapose! h
      constructor <;> linarith
    · use 0
      push_neg at h
      exact h
  obtain ⟨u, h_src⟩ := ex_src
  have ex_snk : ∃ v : ℤ, ∀ n : ℤ, ⟨v,n⟩ ∉ inv_set τ.val := by
    by_cases h : ∃ v : ℤ, ⟨0,v⟩ ∈ inv_set τ.val
    · obtain ⟨v, hv⟩ := h
      use v
      intro n hn
      have h := τ.property.2 0 v n hv.1 hn.1
      have h' := hv.2
      have h'' := hn.2
      contrapose! h
      constructor <;> linarith
    · use 0
      push_neg at h
      exact h
  obtain ⟨v, h_snk⟩ := ex_snk

  have se_empty : (southeast_set τ.val (τ.val v) v) = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro n hn
    unfold southeast_set at hn
    specialize h_snk n
    simp at hn h_snk
    obtain ⟨v_le_n, τ_n_lt_v⟩ := hn
    unfold inv_set at h_snk
    simp at h_snk
    have : v ≠ n := by
      intro heq
      rw [heq] at τ_n_lt_v
      linarith
    have := h_snk (lt_of_le_of_ne v_le_n this)
    linarith

  have se_finite : (southeast_set τ.val (τ.val v) v).Finite := by simp [se_empty]

  have nw_empty : (northwest_set τ.val (τ.val u + 1) (u+1)) = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    intro n hn
    unfold northwest_set at hn; simp at hn
    specialize h_src n
    simp at hn h_src
    obtain ⟨n_lt_u_plus_1, τ_n_ge_u_plus_1⟩ := hn
    unfold inv_set at h_src
    simp at h_src
    have n_le_u : n ≤ u := by linarith
    have : n ≠ u := by
      intro heq
      rw [heq] at τ_n_ge_u_plus_1
      linarith
    have n_lt_u : n < u := lt_of_le_of_ne n_le_u this
    have := h_src n_lt_u
    linarith

  have nw_finite : (northwest_set τ.val (τ.val u + 1) (u+1)).Finite := by simp [nw_empty]

  exact asp_of_finite_quadrants τ.property.1.injective se_finite nw_finite

theorem criterion_321a (τ : ℤ → ℤ) (hperm : Function.Bijective τ) : func_321a_prop τ ↔
  set_321a_prop (inv_set τ) := by
  constructor
  -- Forward direction
  · intro h321a
    let τ_321a : perm_321a := ⟨τ, hperm, h321a⟩
    have h_asp := asp_of_321a τ_321a
    let τ_asp : AspPerm := ⟨τ, hperm, h_asp⟩
    constructor
    · show AspSet_prop (inv_set τ)
      exact AspSet.AspSet_InvSet_of_AspPerm τ_asp
    · intro u v w
      by_contra! h
      obtain ⟨uv_inv, vw_inv⟩ := h
      specialize h321a u v w
      have : τ u < τ v ∨ τ v < τ w := h321a uv_inv.1 vw_inv.1
      contrapose! this
      exact ⟨le_of_lt uv_inv.2, le_of_lt vw_inv.2⟩
  -- Converse
  · rintro h i j k i_lt_j j_lt_k
    have := h.tfree i j k
    contrapose! this
    obtain ⟨h1, h2⟩ := this
    have h1 : τ j < τ i := by
      apply lt_of_le_of_ne h1
      intro heq; apply hperm.injective at heq
      linarith
    have h2 : τ k < τ j := by
      apply lt_of_le_of_ne h2
      intro heq; apply hperm.injective at heq
      linarith
    exact ⟨ ⟨i_lt_j, h1⟩, ⟨j_lt_k, h2⟩ ⟩

lemma set_321a_of_func (avset : set_321a) : set_321a_prop (inv_set avset.to_func) := by
  constructor
  · show AspSet_prop (inv_set avset.to_func)
    rw [avset.invSet_func]
    refine avset.prop
  · simp [avset.prop_321a.tfree, avset.invSet_func]

theorem inv_321a_char (I : Set (ℤ × ℤ)) :
  set_321a_prop I
  ↔ (∃ τ : (ℤ → ℤ), (func_321a_prop τ ∧ Function.Bijective τ ∧ inv_set τ = I)) := by
  constructor
  · intro Ip
    let I_asp : AspSet := ⟨I, Ip.asp⟩
    let I_321a : set_321a := ⟨I_asp, Ip⟩
    let τ : AspPerm := I_321a.toAspPerm
    use τ.func
    constructor
    · rw [criterion_321a τ.func τ.bijective]
      have : inv_set τ.func = I := I_321a.invSet_func
      rwa [this]
    constructor
    · exact τ.bijective
    · exact I_321a.invSet_func
  · rintro ⟨τ, ⟨h_321a, h_bij, h_inv⟩⟩
    have := (criterion_321a τ h_bij).mp h_321a
    rwa [h_inv] at this

end ASP321a
