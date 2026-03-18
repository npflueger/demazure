import Demazure.InvSet
import Demazure.Submodular

def is_321a (τ : ℤ → ℤ) : Prop :=
  ∀ (i j k : ℤ), i < j → j < k → τ i < τ j ∨ τ j < τ k

namespace ASP321a

structure set_321a_prop (I : Set (ℤ × ℤ)) where
  asp : AspSet_prop I
  tfree : ∀ u v w : ℤ, ⟨u,v⟩ ∉ I ∨ ⟨v,w⟩ ∉ I

/-- `tfas` = triangle-free ASP set. -/
structure tfas : Type extends AspSet where
  prop_321a : set_321a_prop I

theorem is_asp_of_is_321a (τ : ℤ → ℤ) (h_bij : Function.Bijective τ)
    (h_321a : is_321a τ) : is_asp τ := by
  have ex_src : ∃ u : ℤ, ∀ n : ℤ, ⟨n,u⟩ ∉ inv_set τ := by
    by_cases h : ∃ u : ℤ, ⟨u,0⟩ ∈ inv_set τ
    · obtain ⟨u, hu⟩ := h
      use u
      intro n hn
      have h := h_321a n u 0 hn.1 hu.1
      have h' := hu.2
      have h'' := hn.2
      contrapose! h
      constructor <;> linarith
    · use 0
      push_neg at h
      exact h
  obtain ⟨u, h_src⟩ := ex_src
  have ex_snk : ∃ v : ℤ, ∀ n : ℤ, ⟨v,n⟩ ∉ inv_set τ := by
    by_cases h : ∃ v : ℤ, ⟨0,v⟩ ∈ inv_set τ
    · obtain ⟨v, hv⟩ := h
      use v
      intro n hn
      have h := h_321a 0 v n hv.1 hn.1
      have h' := hv.2
      have h'' := hn.2
      contrapose! h
      constructor <;> linarith
    · use 0
      push_neg at h
      exact h
  obtain ⟨v, h_snk⟩ := ex_snk

  have se_empty : (southeast_set τ (τ v) v) = ∅ := by
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

  have se_finite : (southeast_set τ (τ v) v).Finite := by simp [se_empty]

  have nw_empty : (northwest_set τ (τ u + 1) (u+1)) = ∅ := by
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

  have nw_finite : (northwest_set τ (τ u + 1) (u+1)).Finite := by simp [nw_empty]

  exact asp_of_finite_quadrants h_bij.injective se_finite nw_finite

lemma tfree_of_is_321a (τ : ℤ → ℤ) (h_321a : is_321a τ) :
  ∀ u v w : ℤ, ⟨u,v⟩ ∉ inv_set τ ∨ ⟨v,w⟩ ∉ inv_set τ := by
  intro u v w
  by_contra! h
  obtain ⟨uv_inv, vw_inv⟩ := h
  specialize h_321a u v w uv_inv.1 vw_inv.1
  have : τ u < τ v ∨ τ v < τ w := h_321a
  contrapose! this
  exact ⟨le_of_lt uv_inv.2, le_of_lt vw_inv.2⟩

theorem is_321a_iff_set_321a_prop (τ : ℤ → ℤ) (hperm : Function.Bijective τ) :
    is_321a τ ↔ set_321a_prop (inv_set τ) := by
  constructor
  -- Forward direction
  · intro h321a
    have h_asp := is_asp_of_is_321a τ hperm h321a
    let τ_asp : AspPerm := ⟨τ, hperm, h_asp⟩
    constructor
    · show AspSet_prop (inv_set τ)
      exact AspSet.AspSet_InvSet_of_AspPerm τ_asp
    · exact tfree_of_is_321a τ h321a
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

def tfas_of_perm {τ : AspPerm} (h_321a : is_321a τ) : tfas := ⟨AspSet.of_AspPerm τ, by
  constructor
  · exact AspSet.AspSet_InvSet_of_AspPerm τ
  · exact tfree_of_is_321a τ h_321a⟩

noncomputable def Perm321a_equiv_BijectiveFunc321a :
  {τ : AspPerm | is_321a τ} ≃ {τ : ℤ → ℤ // Function.Bijective τ ∧ is_321a τ} where
  toFun τ := ⟨τ.val.func, ⟨τ.val.bijective, τ.prop⟩⟩
  invFun := fun ⟨τ, hτ⟩ =>
    ⟨⟨τ, hτ.1, is_asp_of_is_321a τ hτ.1 hτ.2⟩, hτ.2⟩
  left_inv := by
    intro τ
    apply Subtype.ext
    apply AspPerm.ext.mpr
    rfl
  right_inv := by
    intro τ
    apply Subtype.ext
    rfl

noncomputable def Perm321a_equiv_Tfas :
  {τ : AspPerm | is_321a τ} ≃ tfas × ℤ where
  toFun τ :=
    ⟨⟨AspSet.of_AspPerm τ,
        (is_321a_iff_set_321a_prop τ τ.val.bijective).mp τ.prop⟩, τ.val.χ⟩
  invFun := fun ⟨I, χ⟩ =>
    ⟨I.toAspPerm χ,
      (is_321a_iff_set_321a_prop (I.recon χ) (I.toAspPerm χ).bijective).mpr
        { asp := by
            show AspSet_prop (inv_set (I.recon χ))
            rw [I.invSet_func χ]
            exact I.prop
          tfree := by
            simpa [I.invSet_func χ] using I.prop_321a.tfree }⟩
  left_inv := by
    intro τ
    apply Subtype.ext
    refine AspPerm.eq_of_inv_set_eq_of_chi_eq _ _ ?_ ?_
    · change inv_set ((AspSet.of_AspPerm τ).toAspPerm τ.val.χ) = inv_set τ
      simpa using (AspSet.of_AspPerm τ).invSet_of_toAspPerm τ.val.χ
    · change ((AspSet.of_AspPerm τ).toAspPerm τ.val.χ).χ = τ.val.χ
      simpa using (AspSet.of_AspPerm τ).chi_of_toAspPerm τ.val.χ
  right_inv := by
    intro ⟨I, χ⟩
    rw [Prod.mk.injEq]
    constructor
    · cases I
      case mk toAspSet prop_321a =>
        rw [tfas.mk.injEq]
        apply SetLike.coe_injective
        exact toAspSet.invSet_of_toAspPerm χ
    · exact I.chi_of_toAspPerm χ



theorem inv_321a_char (I : Set (ℤ × ℤ)) :
  set_321a_prop I
  ↔ (∃ τ : (ℤ → ℤ), (is_321a τ ∧ Function.Bijective τ ∧ inv_set τ = I)) := by
  constructor
  · intro Ip
    let I_asp : AspSet := ⟨I, Ip.asp⟩
    let I_321a : tfas := ⟨I_asp, Ip⟩
    let τ : AspPerm := I_321a.toAspPerm 0
    use τ.func
    constructor
    · rw [is_321a_iff_set_321a_prop τ.func τ.bijective]
      have : inv_set τ.func = I := I_321a.invSet_func 0
      rwa [this]
    constructor
    · exact τ.bijective
    · exact I_321a.invSet_func 0
  · rintro ⟨τ, ⟨h_321a, h_bij, h_inv⟩⟩
    have := (is_321a_iff_set_321a_prop τ h_bij).mp h_321a
    rwa [h_inv] at this

def is_src (τ : AspPerm) (u : ℤ) : Prop :=
  ∃ v : ℤ, ⟨u, v⟩ ∈ inv_set τ

lemma src_of_inv {τ : AspPerm} {u v : ℤ} (uv_inv : ⟨u, v⟩ ∈ inv_set τ) :
  is_src τ u := by use v

def is_snk (τ : AspPerm) (v : ℤ) : Prop :=
  ∃ u : ℤ, (u, v) ∈ inv_set τ

lemma snk_of_inv {τ : AspPerm} {u v : ℤ} (uv_inv : ⟨u, v⟩ ∈ inv_set τ) :
  is_snk τ v := by use u

section fixed_321a
variable {τ : AspPerm} (h_321a : is_321a τ)
include h_321a

lemma inv_is_321a : is_321a τ⁻¹.func := by
  intro i j k i_lt_j j_lt_k
  have h := h_321a (τ⁻¹ k) (τ⁻¹ j) (τ⁻¹ i)
  simp only [τ.mul_inv_cancel_eval] at h
  by_contra!
  obtain ⟨h1, h2⟩ := this
  have h1 : τ⁻¹ j < τ⁻¹ i := by
    apply lt_of_le_of_ne h1
    intro heq; apply τ⁻¹.injective at heq
    exact ne_of_lt i_lt_j (Eq.symm heq)
  have h2 : τ⁻¹ k < τ⁻¹ j := by
    apply lt_of_le_of_ne h2
    intro heq; apply τ⁻¹.injective at heq
    exact ne_of_lt j_lt_k (Eq.symm heq)
  have := h h2 h1
  rcases this <;> linarith

lemma not_src_and_snk (n : ℤ) :
  ¬ (is_src τ n) ∨ ¬(is_snk τ) n := by
  by_contra!
  obtain ⟨h_src, h_snk⟩ := this
  rcases h_snk with ⟨u, hu⟩
  rcases h_src with ⟨v, hv⟩
  have := tfree_of_is_321a τ h_321a u n v
  rcases this <;> contradiction

lemma snk_lt {v x : ℤ} (v_snk : is_snk τ v) (v_lt_x : v < x) :
  τ v < τ x := by
  by_contra! h
  have : ⟨v, x⟩ ∈ inv_set τ := by
    use v_lt_x
    refine lt_of_le_of_ne h ?_
    intro heq
    apply τ.injective at heq
    rw [heq] at v_lt_x
    exact lt_irrefl v v_lt_x
  rcases v_snk with ⟨u, _⟩
  have := tfree_of_is_321a τ h_321a u v x
  rcases this <;> contradiction

lemma snk_le {v x : ℤ} (v_snk : is_snk τ v) (v_le_x : v ≤ x) :
  τ v ≤ τ x := by
  by_cases heq : v = x
  · rw [heq]
  · have v_lt_x : v < x := lt_of_le_of_ne v_le_x heq
    apply le_of_lt
    exact snk_lt h_321a v_snk v_lt_x

lemma src_gt {u x : ℤ} (u_src : is_src τ u) (x_lt_u : x < u) :
  τ x < τ u := by
  by_contra! h
  have : ⟨x, u⟩ ∈ inv_set τ := by
    use x_lt_u
    refine lt_of_le_of_ne h ?_
    intro heq
    apply τ.injective at heq
    rw [heq] at x_lt_u
    exact lt_irrefl x x_lt_u
  rcases u_src with ⟨v, _⟩
  have := tfree_of_is_321a τ h_321a x u v
  rcases this <;> contradiction

lemma src_ge {u x : ℤ} (u_src : is_src τ u) (x_le_u : x ≤ u) :
  τ x ≤ τ u := by
  by_cases h : x = u
  · rw [h]
  · have x_lt_u := lt_of_le_of_ne x_le_u h
    apply le_of_lt
    exact src_gt h_321a u_src x_lt_u

structure between_inv_prop (u x v : ℤ) where
  src_or_snk : is_src τ x ∨ is_snk τ x
  src_iff_right_inv : is_src τ x ↔ ⟨x, v⟩ ∈ inv_set τ
  src_iff_left_ninv : is_src τ x ↔ ⟨u, x⟩ ∉ inv_set τ
  snk_iff_left_inv : is_snk τ x ↔ ⟨u, x⟩ ∈ inv_set τ
  snk_iff_right_ninv : is_snk τ x ↔ ⟨x, v⟩ ∉ inv_set τ

lemma between_inv {u x v : ℤ}
  (uv_inv : ⟨u, v⟩ ∈ inv_set τ) (u_le_x : u ≤ x) (x_le_v : x ≤ v) :
  between_inv_prop (τ := τ) u x v := by
  by_cases h_ux : ⟨u, x⟩ ∈ inv_set τ
  · have x_snk : is_snk τ x := snk_of_inv h_ux
    have x_not_src : ¬ is_src τ x := by
      intro h_src
      have := not_src_and_snk h_321a x
      rcases this <;> contradiction
    have h_xv : ⟨x, v⟩ ∉ inv_set τ := by
      intro h_xv
      have := tfree_of_is_321a τ h_321a u x v
      rcases this <;> contradiction
    constructor <;> simp [x_snk, x_not_src, h_ux, h_xv]
  · have h_xv : ⟨x, v⟩ ∈ inv_set τ := by
      have ineq : τ u ≤ τ x := by
        by_contra! h
        have neq : u ≠ x := by
          intro heq
          rw [heq] at h
          exact lt_irrefl (τ x) h
        have u_lt_x : u < x := lt_of_le_of_ne u_le_x neq
        have : ⟨u, x⟩ ∈ inv_set τ := ⟨u_lt_x, h⟩
        contradiction
      have τ_x_gt_v : τ x > τ v := by
        linarith [uv_inv.2]
      have neq : x ≠ v := by
        intro heq
        rw [heq] at τ_x_gt_v
        exact lt_irrefl (τ v) τ_x_gt_v
      have x_lt_v : x < v := lt_of_le_of_ne x_le_v neq
      exact ⟨x_lt_v, τ_x_gt_v⟩
    have x_src : is_src τ x := src_of_inv h_xv
    have x_nsnk : ¬ is_snk τ x := by
      intro h_snk
      have := not_src_and_snk h_321a x
      rcases this <;> contradiction
    constructor <;> simp [x_src, x_nsnk, h_ux, h_xv]

omit h_321a in
lemma inv_of_quadrants {τ : AspPerm} {a b u v : ℤ}
  (hu : u ∈ northwest_set τ a b) (hv : v ∈ southeast_set τ a b) :
  ⟨u, v⟩ ∈ inv_set τ := by
  have u_lt_v : u < v := lt_of_lt_of_le hu.1 hv.1
  have τ_u_gt_v : τ v < τ u := lt_of_lt_of_le hv.2 hu.2
  exact ⟨u_lt_v, τ_u_gt_v⟩

lemma split_s {u v : ℤ} {a b : ℤ}
  (u_lt_b : u < b) (b_le_v : b ≤ v) (τv_lt_a : τ v < a) (τu_ge_a : τ u ≥ a) :
  τ.s a v + τ.s (τ v) b = τ.s a b := by
  have uv_inv : ⟨u, v⟩ ∈ inv_set τ :=
    ⟨ lt_of_lt_of_le u_lt_b b_le_v, lt_of_lt_of_le τv_lt_a τu_ge_a⟩
  have h_union : southeast_set τ a b = southeast_set τ a v ∪ southeast_set τ (τ v) b := by
    ext n
    simp only [Set.mem_union, southeast_set, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n_ge_b, τn_lt_a⟩
      by_cases n_v : n ≥ v
      · left
        exact ⟨n_v, τn_lt_a⟩
      · right
        push_neg at n_v
        suffices τ n < τ v by exact ⟨n_ge_b, this⟩
        by_contra! τv_le_τn
        have nv_inv : ⟨n, v⟩ ∈ inv_set τ := (τ.inv_iff_le n_v).mpr τv_le_τn
        have un_inv : ⟨u, n⟩ ∈ inv_set τ :=
          ⟨lt_of_lt_of_le u_lt_b n_ge_b, lt_of_lt_of_le τn_lt_a τu_ge_a⟩
        have := tfree_of_is_321a τ h_321a u n v
        rcases this <;> contradiction
    · rintro (⟨n_ge_v, τn_lt_a⟩ | ⟨n_ge_b, τn_lt_τv⟩)
      · exact ⟨le_trans b_le_v n_ge_v, τn_lt_a⟩
      · exact ⟨n_ge_b, lt_trans τn_lt_τv τv_lt_a⟩
  have h_disj : Disjoint (southeast_set τ a v) (southeast_set τ (τ v) b) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    simp only [Set.mem_inter_iff, southeast_set, Set.mem_setOf_eq] at hx
    obtain ⟨⟨x_ge_v, τx_lt_a⟩, ⟨x_ge_b, τx_lt_τv⟩⟩ := hx
    have vx_inv : ⟨v, x⟩ ∈ inv_set τ := (τ.inv_iff_lt x_ge_v).mpr τx_lt_τv
    have := tfree_of_is_321a τ h_321a u v x
    rcases this <;> contradiction
  have h_ncard : (southeast_set τ a b).ncard =
      (southeast_set τ a v).ncard + (southeast_set τ (τ v) b).ncard := by
    rw [h_union]
    exact Set.ncard_union_eq h_disj (τ.se_finite a v) (τ.se_finite (τ v) b)
  have h_cast : ((southeast_set τ a b).ncard : ℤ) =
      ((southeast_set τ a v).ncard : ℤ) + ((southeast_set τ (τ v) b).ncard : ℤ) := by
    exact_mod_cast h_ncard
  simpa [AspPerm.s, add_comm] using h_cast.symm

lemma uv_duality {u : ℤ} {a b : ℤ}
  (u_lt_b : u < b) (τu_ge_a : τ u ≥ a)
  {m m' : ℤ} (m_pos : m > 0) (m'_pos : m' > 0) (m_sum : m + m' = τ.s a b + 1) :
  τ (τ.v b m_pos) = τ⁻¹.u a m'_pos := by
  rw [τ⁻¹.u_crit a m'_pos (τ (τ.v b m_pos))]
  have s_ge_m : τ.s a b ≥ m := by
    linarith
  let b_le_v : b ≤ τ.v b m_pos := τ.v_ge b m_pos
  let τv_lt_a : τ (τ.v b m_pos) < a := τ.τv_lt b m_pos s_ge_m

  constructor
  · suffices τ.s a (τ.v b m_pos) = m' by simp [τ⁻¹.dual_inverse, this]
    have split := split_s h_321a u_lt_b b_le_v τv_lt_a τu_ge_a
    have : τ.s (τ (τ.v b m_pos)) b = m - 1 := by
      exact ((τ.v_crit b m_pos (τ.v b m_pos)).mp rfl).1
    rw [this] at split
    linarith
  · exact τv_lt_a

lemma uv_duality_ge {a b : ℤ}
  {m m' : ℤ} (m_pos : m > 0) (m'_pos : m' > 0) (m_sum : m + m' = τ.s a b + 1) :
  is_snk τ (τ.v b m_pos) → is_snk τ (τ⁻¹ (τ⁻¹.u a m'_pos)) →
    (τ (τ.v b m_pos) ≥ τ⁻¹.u a m'_pos) ∧
      (τ.v b m_pos ≥ τ⁻¹ (τ⁻¹.u a m'_pos)) := by
  let v := τ.v b m_pos
  let w := τ⁻¹.u a m'_pos
  suffices is_snk τ v → is_snk τ (τ⁻¹ w) → (τ v ≥ w ∧ v ≥ τ⁻¹ w) by
    assumption
  intro v_snk τiw_snk
  have equiv : τ v ≥ w ↔ v ≥ τ⁻¹ w := by
    constructor
    · intro h; contrapose! h
      simpa using snk_lt h_321a v_snk h
    · intro h
      simpa using snk_le h_321a τiw_snk h
  suffices τ v ≥ w by
    rw [← equiv]
    exact ⟨this, this⟩
  by_contra! τv_lt_w
  let A := τ.se_finset (τ v) b
  let B := τ.se_finset a (τ⁻¹ w)
  let S := τ.se_finset a b
  have disj : Disjoint A B := by
    rw [Finset.disjoint_iff_ne]
    intro n nA _ nB rfl
    rw [τ.mem_se] at nA nB
    obtain ⟨_, τn_lt_τv⟩ := nA
    obtain ⟨n_ge_τiw, _⟩ := nB
    have τn_ge_w : τ n ≥ w := by simpa using snk_le h_321a τiw_snk n_ge_τiw
    have w_lt_τv : w < τ v := lt_of_le_of_lt τn_ge_w τn_lt_τv
    have w_lt_w := lt_trans w_lt_τv τv_lt_w
    exact lt_irrefl w w_lt_w
  have union_card : (A ∪ B).card = S.card := by
    rw [Finset.card_union_of_disjoint disj]
    suffices (A.card : ℤ) + (B.card : ℤ) = (S.card : ℤ) by
      rw [← Nat.cast_add] at this
      exact Nat.cast_inj.mp this
    have : A.card = m - 1 := by
      rw [← τ.s_eq_se_card (τ v) b]
      simpa [A] using τ.s_τv_b b m_pos
    rw [this]
    have : B.card = m' := by
      have hB : τ.s a (τ⁻¹ w) = m' := by
        simpa [w, AspPerm.dual_inverse] using (τ⁻¹.s'_b_τu a m'_pos)
      rw [τ.s_eq_se_card a (τ⁻¹ w)] at hB
      simpa [B] using hB
    rw [this]
    have : S.card + 1 = τ.s a b + 1 := by
      rw [τ.s_eq_se_card a b]
    linarith
  have union_sub : A ∪ B ⊆ S := by
    intro x
    rw [Finset.mem_union, τ.mem_se, τ.mem_se, τ.mem_se]
    intro hx
    rcases hx with ( ⟨x_ge_b, τx_lt_τv⟩ | ⟨x_ge_τiw, τx_lt_a⟩)
    · have τv_lt_a : τ v < a := by
        have : τ.s a b ≥ m := by linarith
        exact τ.τv_lt b m_pos this
      exact ⟨x_ge_b, lt_trans τx_lt_τv τv_lt_a⟩
    · have τiw_ge_b : τ⁻¹ w ≥ b := by
        apply τ⁻¹.τu_ge a m'_pos (a := b)
        suffices m' ≤ τ.s a b by simpa [τ⁻¹.dual_inverse]
        linarith
      exact ⟨le_trans τiw_ge_b x_ge_τiw, τx_lt_a⟩

  have union_eq : A ∪ B = S := by
    apply (Finset.eq_iff_card_le_of_subset union_sub).mp
    rw [union_card]

  have v_mem : v ∈ A ∪ B := by
    rw [union_eq]
    unfold S; rw [τ.mem_se]
    have v_ge_b : v ≥ b := τ.v_ge b m_pos
    have τv_lt_a : τ v < a := by
      apply τ.τv_lt b m_pos (a := a)
      linarith
    exact ⟨v_ge_b, τv_lt_a⟩

  rw [Finset.mem_union] at v_mem
  rcases v_mem with (vA | vB)
  · rw [τ.mem_se] at vA
    exact lt_irrefl (τ v) vA.2
  · rw [τ.mem_se] at vB
    have v_ge_τiw : v ≥ τ⁻¹ w := vB.1
    have τv_ge_w : τ v ≥ w := by
      simpa using snk_le h_321a τiw_snk v_ge_τiw
    exact lt_irrefl w (lt_of_le_of_lt τv_ge_w τv_lt_w)


lemma uv_duality_lt (a b : ℤ) {m m' : ℤ} (m_pos : m > 0) (m'_pos : m' > 0)
  (h_sum : m + m' ≥ τ.s a b + 2) :
  let v := τ.v b m_pos
  let w := τ⁻¹.u a m'_pos
  is_snk τ v → is_snk τ (τ⁻¹ w) → τ⁻¹ w < v
  := by
  rintro v w v_snk τiw_snk
  by_contra! v_le_iw

  -- Collect a bunch of inequalities
  have τv_le_w : τ v ≤ w := by
    by_cases h : v = τ⁻¹ w
    · simp [h]
    have v_lt_iw : v < τ⁻¹ w := lt_of_le_of_ne v_le_iw h
    simpa using le_of_lt <| snk_lt h_321a v_snk v_lt_iw
  have b_le_v : b ≤ v := τ.v_ge b m_pos
  have w_lt_a : w < a := τ⁻¹.u_lt a m'_pos

  -- Define the relevant sets and establish inclusions
  let S := τ.se_finset a b
  let A := τ.se_finset a (τ⁻¹ w)
  let B := τ.se_finset (τ v) b
  have A_subset : A ⊆ S := by
    intro n nA
    obtain ⟨iw_le_n, τn_lt_a⟩ := (τ.mem_se _ _ _).mp nA
    suffices n ≥ b ∧ τ n < a by exact (τ.mem_se a b n).mpr this
    exact ⟨le_trans b_le_v (le_trans v_le_iw iw_le_n), τn_lt_a⟩
  have B_subset : B ⊆ S := by
    intro n nB
    obtain ⟨b_le_n, τn_lt_τv⟩ := (τ.mem_se _ _ _).mp nB
    suffices n ≥ b ∧ τ n < a by exact (τ.mem_se a b n).mpr this
    exact ⟨b_le_n, lt_trans τn_lt_τv (lt_of_le_of_lt τv_le_w w_lt_a)⟩

  have disj : Disjoint A B := by
    apply Finset.disjoint_iff_ne.mpr
    rintro n nA _ nB rfl
    apply (τ.mem_se _ _ _).mp at nA
    obtain ⟨n_ge_iw, _⟩ := nA
    apply (τ.mem_se _ _ _).mp at nB
    obtain ⟨_, τn_lt_τv⟩ := nB
    have v_le_n : v ≤ n := le_trans v_le_iw n_ge_iw
    have : ⟨v, n⟩ ∈ inv_set τ := (τ.inv_iff_lt v_le_n).mpr τn_lt_τv
    have : is_src τ v := src_of_inv this
    rcases not_src_and_snk h_321a v <;> contradiction

  have ineq : ((A ∪ B).card : ℤ) > S.card := by
    rw [Finset.card_union_of_disjoint disj, Nat.cast_add]

    have : A.card = m' := by
      have hA : τ.s a (τ⁻¹ w) = m' := by
        simpa [w, AspPerm.dual_inverse] using (τ⁻¹.s'_b_τu a m'_pos)
      rw [τ.s_eq_se_card a (τ⁻¹ w)] at hA
      simpa [A] using hA
    rw [this]
    have : B.card = m - 1 := by
      rw [← τ.s_eq_se_card (τ v) b]
      simpa [B] using τ.s_τv_b b m_pos
    rw [this]
    have : S.card = τ.s a b := by
      rw [τ.s_eq_se_card a b]
    rw [this]
    linarith [h_sum]

  have := Finset.card_le_card (Finset.union_subset A_subset B_subset)
  linarith [this, ineq]

lemma split_s' {u v : ℤ} {a b : ℤ}
  (u_lt_b : u < b) (b_le_v : b ≤ v) (τv_lt_a : τ v < a) (τu_ge_a : τ u ≥ a) :
  τ⁻¹.s b (τ u) + τ⁻¹.s u a = τ⁻¹.s b a := by
  let u' := τ v
  let v' := τ u
  have := split_s (τ := τ⁻¹) (h_321a := inv_is_321a h_321a)
    (a := b) (b := a) (u := u') (v := v')
  have := this (τv_lt_a) (τu_ge_a) (by unfold v'; simpa) (by unfold u'; simpa)
  unfold u' v' at this; simpa using this

section fixed_321a_and_lel
variable {β : AspPerm} (h_L : β ≤L τ)
include h_L

omit h_321a in
lemma src_of_src {n : ℤ} (h_src : is_src β n) : is_src τ n := by
  rcases h_src with ⟨v, h_inv⟩
  exact src_of_inv (h_L h_inv)

omit h_321a in
lemma snk_of_snk {n : ℤ} (h_snk : is_snk β n) : is_snk τ n := by
  rcases h_snk with ⟨u, h_inv⟩
  exact snk_of_inv (h_L h_inv)

lemma is_321a_of_lel : is_321a β := by
  rw [is_321a_iff_set_321a_prop τ τ.bijective] at h_321a
  rw [is_321a_iff_set_321a_prop β β.bijective]
  constructor
  · have := (AspSet.of_AspPerm β).prop
    congr
  · intro u v w
    by_contra! h
    obtain ⟨uv_inv, vw_inv⟩ := h
    have uv_inv : ⟨u, v⟩ ∈ inv_set τ := h_L uv_inv
    have vw_inv : ⟨v, w⟩ ∈ inv_set τ := h_L vw_inv
    have := h_321a.tfree u v w
    rcases this <;> contradiction

structure between_inv_lel_prop (β τ : AspPerm) (u x v : ℤ) where
  propτ : between_inv_prop (τ := τ) u x v
  propβ : between_inv_prop (τ := β) u x v
  inv_iff_left : ⟨u, x⟩ ∈ inv_set β ↔ ⟨u, x⟩ ∈ inv_set τ
  inv_iff_right : ⟨x, v⟩ ∈ inv_set β ↔ ⟨x, v⟩ ∈ inv_set τ
  src_iff : is_src β x ↔ is_src τ x
  snk_iff : is_snk β x ↔ is_snk τ x

lemma between_inv_lel
  {u x v : ℤ} (uv_inv : ⟨u, v⟩ ∈ inv_set β) (u_le_x : u ≤ x) (x_le_v : x ≤ v)
  : between_inv_lel_prop β τ u x v  := by
  have bp := between_inv h_321a (h_L uv_inv) u_le_x x_le_v
  have h_321a_β : is_321a β := is_321a_of_lel h_321a h_L
  have bpβ := between_inv h_321a_β uv_inv u_le_x x_le_v
  by_cases h_src : is_src β x
  · have h_ux : ⟨u, x⟩ ∉ inv_set τ := bp.src_iff_left_ninv.mp
      (src_of_src h_L h_src)
    have h_xv : ⟨x, v⟩ ∈ inv_set β := bpβ.src_iff_right_inv.mp h_src
    have h_ux_β : ⟨u, x⟩ ∉ inv_set β := by
      contrapose! h_ux
      exact h_L h_ux
    have x_src : is_src β x := src_of_inv h_xv
    have x_snk : ¬ is_snk τ x := not_imp_not.mpr bp.snk_iff_left_inv.mp h_ux
    have x_snk_β : ¬ is_snk β x := not_imp_not.mpr
      (snk_of_snk h_L) x_snk
    refine ⟨bp, bpβ, ?_, ?_, ?_, ?_⟩
    · constructor
      · intro h
        exact (h_ux_β h).elim
      · intro h
        exact (h_ux h).elim
    · constructor
      · intro h
        exact h_L h
      · intro _
        exact h_xv
    · constructor
      · intro _
        exact src_of_src h_L h_src
      · intro _
        exact x_src
    · constructor
      · intro h
        exact (x_snk_β h).elim
      · intro h
        exact (x_snk h).elim
  · have h_snk : is_snk β x := by
      have := bpβ.src_or_snk
      exact this.resolve_left h_src
    have h_ux : ⟨u, x⟩ ∈ inv_set β := bpβ.snk_iff_left_inv.mp h_snk
    have h_xv : ⟨x, v⟩ ∉ inv_set τ := bp.snk_iff_right_ninv.mp
      (snk_of_snk h_L h_snk)
    have h_xv_β : ⟨x, v⟩ ∉ inv_set β := by
      contrapose! h_xv
      exact h_L h_xv
    have x_src : ¬ is_src τ x := not_imp_not.mpr bp.src_iff_right_inv.mp h_xv
    have x_snk : is_snk β x := snk_of_inv h_ux
    refine ⟨bp, bpβ, ?_, ?_, ?_, ?_⟩
    · constructor
      · intro h
        exact h_L h
      · intro _
        exact h_ux
    · constructor
      · intro h
        exact (h_xv_β h).elim
      · intro h
        exact (h_xv h).elim
    · constructor
      · intro h
        exact (h_src h).elim
      · intro h
        exact (x_src h).elim
    · constructor
      · intro _
        exact snk_of_snk h_L h_snk
      · intro _
        exact x_snk

def interval_sub (i₁ i₂ : (ℤ × ℤ)) : Prop :=
  i₂.1 ≤ i₁.1 ∧ i₁.2 ≤ i₂.2
infix:50 " ≼ " => interval_sub

lemma inv_of_lel_iff
  {u v u' v' : ℤ} (uv_inv : ⟨u, v⟩ ∈ inv_set β) (nested : ⟨u', v'⟩ ≼ ⟨u, v⟩) :
  ⟨u', v'⟩ ∈ inv_set β ↔ ⟨u', v'⟩ ∈ inv_set τ := by
  have h_321a_β := is_321a_of_lel h_321a h_L
  wlog u'_lt_v' : u' < v'
  · constructor <;> (intro u'v'_inv; have := u'v'_inv.1; contradiction)
  -- Do the easy direction first
  constructor
  · intro h
    exact h_L h
  -- Now focus on the converse
  intro u'v'_inv

  have u'_src_τ : is_src τ u' := src_of_inv u'v'_inv
  have bpu' : between_inv_lel_prop β τ u u' v :=
    between_inv_lel h_321a h_L
    uv_inv nested.1 (le_trans (le_of_lt u'v'_inv.1) nested.2)
  have u'_src : is_src β u' := bpu'.src_iff.mpr u'_src_τ
  have u'v_inv : ⟨u', v⟩ ∈ inv_set β := bpu'.propβ.src_iff_right_inv.mp u'_src

  have v'_snk_τ : is_snk τ v' := snk_of_inv u'v'_inv
  have bpv' : between_inv_lel_prop β τ u' v' v :=
    between_inv_lel h_321a h_L
    u'v_inv (le_of_lt u'v'_inv.1) nested.2
  have v'_snk : is_snk β v' := bpv'.snk_iff.mpr v'_snk_τ
  have u'v'_inv : ⟨u', v'⟩ ∈ inv_set β := bpv'.propβ.snk_iff_left_inv.mp v'_snk

  exact u'v'_inv

omit h_L in
lemma sr_inv_of_ler_iff {α : AspPerm} (h_R : α ≤R τ)
  {u v u' v' : ℤ} (uv_inv : ⟨u, v⟩ ∈ (τ.sr α) '' inv_set α)
  (nested : ⟨u, v⟩ ≼ ⟨u', v'⟩) :
  ⟨u', v'⟩ ∈ (τ.sr α) '' inv_set α ↔ ⟨u', v'⟩ ∈ inv_set τ := by
  let I : ℤ × ℤ := ⟨τ v, τ u⟩
  let J : ℤ × ℤ := ⟨τ v', τ u'⟩
  have invI : I ∈ inv_set α⁻¹.func := by
    simpa [I] using (τ.sr_crit α u v).mp uv_inv
  have uv_inv_τ : ⟨u, v⟩ ∈ inv_set τ := AspPerm.sr_subset τ α h_R uv_inv
  have hJI : J ≼ I := by
    constructor
    · have v_snk : is_snk τ v := snk_of_inv uv_inv_τ
      simpa [I, J] using snk_le h_321a v_snk nested.2
    · have u_src : is_src τ u := src_of_inv uv_inv_τ
      simpa [I, J] using src_ge h_321a u_src nested.1
  have lel : α⁻¹ ≤L τ⁻¹ := AspPerm.le_weak_L_of_R h_R
  constructor
  · intro h
    exact AspPerm.sr_subset τ α h_R h
  · intro h
    have invJτ : J ∈ inv_set τ⁻¹.func := by
      simpa [J] using (τ.inv_set_inverse u' v').mp h
    have invJ : J ∈ inv_set α⁻¹.func := by
      exact (inv_of_lel_iff (τ := τ⁻¹) (β := α⁻¹)
        (inv_is_321a h_321a) lel invI hJI).mpr invJτ
    simpa [J] using (τ.sr_crit α u' v').mpr invJ

omit h_321a h_L in
lemma set_321a_prop_of_func (avset : tfas) (χ : ℤ) :
    set_321a_prop (inv_set (avset.recon χ)) := by
  constructor
  · show AspSet_prop (inv_set (avset.recon χ))
    rw [avset.invSet_func χ]
    refine avset.prop
  · simp [avset.prop_321a.tfree, avset.invSet_func χ]

theorem eq_s_of_lel
  {u b v : ℤ} (uv_inv : ⟨u, v⟩ ∈ inv_set β) (u_lt_b : u < b) :
  β.s (β v) b = τ.s (τ v) b := by
  rw [β.s_eq_se_card (β v) b, τ.s_eq_se_card (τ v) b]
  suffices hse : β.se_finset (β v) b = τ.se_finset (τ v) b by rw [hse]
  ext x
  suffices x ≥ b → (β x < β v ↔ τ x < τ v) by
    simpa [AspPerm.se_finset, southeast_set, this]
  intro x_ge_b
  have u_lt_x : u < x := lt_of_lt_of_le u_lt_b x_ge_b

  wlog x_le_v : x ≤ v
  · have v_lt_x : v < x := by linarith
    have v_snk : is_snk β v := snk_of_inv uv_inv
    have β_lt: β v < β x := snk_lt (is_321a_of_lel h_321a h_L)
      v_snk v_lt_x
    have τ_lt : τ v < τ x := snk_lt h_321a (snk_of_inv <| h_L uv_inv) v_lt_x
    constructor <;> (intro h; linarith)
  wlog x_lt_v : x < v
  · have v_eq_x : v = x := by linarith
    rw [v_eq_x]; simp

  suffices ⟨x, v⟩ ∈ inv_set β ↔ ⟨x, v⟩ ∈ inv_set τ by
    rw [β.inv_iff_le x_lt_v, τ.inv_iff_le x_lt_v] at this
    constructor <;> (intro h; contrapose! h; rwa [this] at *)
  have nested : ⟨x, v⟩ ≼ ⟨u, v⟩ := by constructor <;> linarith
  exact inv_of_lel_iff h_321a h_L uv_inv nested


lemma eq_s'_of_lel
  {u b v : ℤ} (uv_inv : ⟨u, v⟩ ∈ inv_set β) (b_le_v : b ≤ v) :
  β.s' b (β u) = τ.s' b (τ u) := by
  rw [β.s'_eq_nw_card b (β u), τ.s'_eq_nw_card b (τ u)]
  suffices hnw : β.nw_finset (β u) b = τ.nw_finset (τ u) b by rw [hnw]
  ext x
  suffices x < b → (β x ≥ β u ↔ τ x ≥ τ u) by
    simpa [AspPerm.nw_finset, northwest_set, this]
  intro x_lt_b

  wlog u_le_x : u ≤ x
  · have x_lt_u : x < u := by linarith
    have u_src : is_src β u := src_of_inv uv_inv
    have β_gt: β x < β u := src_gt (is_321a_of_lel h_321a h_L)
      u_src x_lt_u
    have τ_gt : τ x < τ u := src_gt h_321a (src_of_inv <| h_L uv_inv) x_lt_u
    constructor <;> (intro h; linarith)

  suffices ⟨u, x⟩ ∈ inv_set β ↔ ⟨u, x⟩ ∈ inv_set τ by
    rw [β.inv_iff_lt u_le_x, τ.inv_iff_lt u_le_x] at this
    constructor <;> (intro h; contrapose! h; rwa [this] at *)
  have nested : ⟨u, x⟩ ≼ ⟨u, v⟩ := by constructor <;> linarith
  exact inv_of_lel_iff h_321a h_L uv_inv nested

lemma uv_eq_of_lel
  (b : ℤ) {m n : ℤ} (m_pos : m > 0) (n_pos : n > 0) :
  ⟨τ.u b n_pos, τ.v b m_pos⟩ ∈ inv_set β
  → τ.u b n_pos = β.u b n_pos ∧ τ.v b m_pos = β.v b m_pos
  := by
  let u := τ.u b n_pos
  let v := τ.v b m_pos
  intro uv_inv; obtain uv_inv : ⟨u, v⟩ ∈ inv_set β := uv_inv
  have u_crit :=  (τ.u_crit b n_pos u).mp (by rfl)
  have s'_eq : τ.s' b (τ u) = n := u_crit.1
  have u_lt_b : u < b := u_crit.2
  have v_crit := (τ.v_crit b m_pos v).mp (by rfl)
  have s_eq : τ.s (τ v) b = m - 1 := v_crit.1
  have b_le_v : b ≤ v := v_crit.2

  have m_eq : β.s (β v) b = m-1 := by
    rw [eq_s_of_lel h_321a h_L uv_inv u_lt_b, s_eq]
  have n_eq : β.s' b (β u) = n := by
    rw [eq_s'_of_lel h_321a h_L uv_inv b_le_v, s'_eq]

  exact ⟨ (β.u_crit b n_pos u).mpr ⟨n_eq, u_lt_b⟩,
    (β.v_crit b m_pos v).mpr ⟨m_eq, b_le_v⟩ ⟩

lemma uv_eq_of_lel'
  (b : ℤ) {m n : ℤ} (m_pos : m > 0) (n_pos : n > 0) :
  ⟨β.u b n_pos, β.v b m_pos⟩ ∈ inv_set β
  → β.u b n_pos = τ.u b n_pos ∧ β.v b m_pos = τ.v b m_pos
  := by
  let u := β.u b n_pos
  let v := β.v b m_pos
  intro uv_inv; obtain uv_inv : ⟨u, v⟩ ∈ inv_set β := uv_inv
  have u_crit :=  (β.u_crit b n_pos u).mp (by rfl)
  have s'_eq : β.s' b (β u) = n := u_crit.1
  have u_lt_b : u < b := u_crit.2
  have v_crit := (β.v_crit b m_pos v).mp (by rfl)
  have s_eq : β.s (β v) b = m - 1 := v_crit.1
  have b_le_v : b ≤ v := v_crit.2

  have m_eq : τ.s (τ v) b = m-1 := by
    rw [← eq_s_of_lel h_321a h_L uv_inv u_lt_b, s_eq]
  have n_eq : τ.s' b (τ u) = n := by
    rw [← eq_s'_of_lel h_321a h_L uv_inv b_le_v, s'_eq]

  exact ⟨ (τ.u_crit b n_pos u).mpr ⟨n_eq, u_lt_b⟩,
    (τ.v_crit b m_pos v).mpr ⟨m_eq, b_le_v⟩ ⟩

theorem lel_ramp
  (b : ℤ) {m n : ℤ} (m_pos : m > 0) (n_pos : n > 0) :
  ⟨τ.u b n_pos, τ.v b m_pos⟩ ∈ inv_set β
  ↔ ⟨m, n⟩ ∈ β.ramp b
  := by
  rw [β.inv_ramp_correspondence b m_pos n_pos]
  constructor
  · intro uv_inv
    have uv_eq := uv_eq_of_lel h_321a h_L
      b m_pos n_pos uv_inv
    rwa [← uv_eq.1, ← uv_eq.2]
  · intro uv_inv
    have uv_eq := uv_eq_of_lel' h_321a h_L
      b m_pos n_pos uv_inv
    rwa [← uv_eq.1, ← uv_eq.2]

omit h_L in
theorem lel_lamp {α : AspPerm} (h_R : α ≤R τ)
  (a : ℤ) {m n : ℤ} (m_pos : m > 0) (n_pos : n > 0) :
  ⟨τ⁻¹.u a m_pos, τ⁻¹.v a n_pos⟩ ∈ inv_set α⁻¹.func
  ↔ ⟨m, n⟩ ∈ α.lamp a
  := by
  have := lel_ramp (τ := τ⁻¹) (β := α⁻¹)
    (inv_is_321a h_321a) h_R a n_pos m_pos
  rw [this]
  simp [α⁻¹.ramp_lamp_dual a]

theorem inv_of_lel_iff_ramp
  {u b v : ℤ} (u_lt_b : u < b) (b_le_v : b ≤ v) :
  let m := τ.s (τ v) b + 1
  let n := τ.s' b (τ u)
  ⟨u, v⟩ ∈ inv_set β ↔ ⟨m, n⟩ ∈ β.ramp b
  := by
  intro m n
  have m_pos : m > 0 := by linarith [τ.s_nonneg (τ v) b]
  have n_pos : n > 0 := τ.s'_pos_of_lt u_lt_b

  rw [← lel_ramp h_321a h_L b m_pos n_pos]
  have u_eq: u = τ.u b n_pos := by
    rw [τ.u_crit b n_pos u]
    exact ⟨rfl, u_lt_b⟩
  have v_eq: v = τ.v b m_pos := by
    rw [τ.v_crit b m_pos v]
    exact ⟨by linarith, b_le_v⟩
  rw [u_eq, v_eq]

section factorization
variable {α : AspPerm} (h_R : α ≤R τ) (h_χ : τ.χ = α.χ + β.χ)
include τ α β h_321a h_R h_L h_χ

lemma inversion_in_union (a b u v : ℤ) (dprod : α.dprod_val_ge β a b (τ.s a b)) :
  u < b → b ≤ v → τ u ≥ a → τ v < a
  → ⟨u, v⟩ ∈ (τ.sr α) '' (inv_set α) ∪ inv_set β := by
  intro u_lt_b b_le_v τu_ge_a τv_lt_a

  let M := τ.s a b
  let N := τ⁻¹.s b a
  let m := τ.s (τ v + 1) b
  have m_eq : m = τ.s (τ v) b + 1 := by exact (τ.a_step_one_iff' v b).mpr b_le_v
  let n := τ⁻¹.s b (τ u)

  have m_icc : m ∈ Set.Icc 1 M := by
    constructor
    · dsimp [m]
      linarith [m_eq, τ.s_nonneg (τ v) b]
    · dsimp [m,M]
      have : τ v + 1 ≤ a := by linarith [τv_lt_a]
      exact (τ.s_nondec this b).1
  have n_icc : n ∈ Set.Icc 1 N := by
    constructor
    · dsimp only [n]; rw [← τ.dual_inverse]; exact τ.s'_pos_of_lt u_lt_b
    · dsimp [n, N]
      exact (τ⁻¹.s_noninc b τu_ge_a).1

  have habMN : a - b + α.χ + β.χ = M - N := by
    linarith [τ.duality a b]

  have legos := (α.ramp_dprod_legos β a b M N habMN).mp dprod m m_icc n n_icc
  rcases legos with (hβ | hα)
  · right
    apply (inv_of_lel_iff_ramp h_321a h_L
      u_lt_b b_le_v).mpr
    rw [τ.dual_inverse]
    convert hβ
    rw [m_eq]
  · left
    have := α⁻¹.ramp_lamp_dual a (N+1-n) (M+1-m)
    rw [inv_inv] at this
    rw [← this] at hα

    have h :
        (τ v, τ u) ∈ inv_set α⁻¹.func ↔
          (τ⁻¹.s u a + 1, τ.s a v) ∈ α⁻¹.ramp a := by
      have := inv_of_lel_iff_ramp (τ := τ⁻¹) (β := α⁻¹)
        (inv_is_321a h_321a) h_R τv_lt_a τu_ge_a
      rw [τ⁻¹.dual_inverse, inv_inv] at this
      simpa using this

    have : τ⁻¹.s u a + 1 = N + 1 - n ∧ τ.s a v = M + 1 - m := by
      constructor
      · have : τ⁻¹ (τ u) < b ∧ τ⁻¹ (τ v) ≥ b := by
          constructor <;> (simp; assumption)
        have := split_s (τ := τ⁻¹) (inv_is_321a h_321a)
          τv_lt_a τu_ge_a this.1 this.2
        simp [τ.inv_mul_cancel_eval] at this
        linarith [this]
      · linarith [split_s h_321a u_lt_b b_le_v τv_lt_a τu_ge_a]

    rw [this.1, this.2] at h
    apply h.mpr at hα

    exact (τ.sr_crit α u v).mpr hα

lemma union_sufficient (a b : ℤ)
    (h_union : inv_set τ ⊆ ((τ.sr α) '' inv_set α) ∪ inv_set β) :
   α.dprod_val_ge β a b (τ.s a b)
  := by
  let M := τ.s a b
  let N := τ.s' b a
  have habMN : a - b + α.χ + β.χ = M - N := by
    have : N = τ⁻¹.s b a := by rw [← τ.dual_inverse]
    linarith [τ.duality a b]
  apply (α.ramp_dprod_legos β a b M N habMN).mpr

  rintro m ⟨m_ge_1, m_le_M⟩ n ⟨n_ge_1, n_le_N⟩
  let m' := M+1 - m
  let n' := N+1 - n
  have m'_ge_1 : m' ≥ 1 := by linarith [m_le_M]
  have n'_ge_1 : n' ≥ 1 := by linarith [n_le_N]
  suffices ⟨m, n⟩ ∈ β.ramp b ∨ ⟨m', n'⟩ ∈ α.lamp a by
    convert this

  let u := τ.u b n_ge_1
  let v := τ.v b m_ge_1
  have u_lt_b : u < b := τ.u_lt b n_ge_1
  have v_ge_b : v ≥ b := (τ.v_ge b m_ge_1)
  have τv_lt_a : τ v < a := τ.τv_lt b m_ge_1 m_le_M
  have τu_ge_a : τ u ≥ a := τ.τu_ge b n_ge_1 n_le_N

  have : ⟨u, v⟩ ∈ inv_set β ↔ ⟨m, n⟩ ∈ β.ramp b :=
    lel_ramp h_321a h_L b m_ge_1 n_ge_1
  rw [← this]

  let u' := τ⁻¹.u a m'_ge_1
  let v' := τ⁻¹.v a n'_ge_1

  have u'_eq : τ v = u' := by
    apply (τ⁻¹.u_crit a m'_ge_1 (τ v)).mpr
    simp only [τ⁻¹.dual_inverse, inv_inv, τ.inv_mul_cancel_eval]
    constructor
    · suffices m + τ.s a v = M + 1 by linarith
      have := split_s h_321a (τ.u_lt b n_ge_1) (τ.v_ge b m_ge_1)
        (τ.τv_lt b m_ge_1 m_le_M) (τ.τu_ge b n_ge_1 n_le_N)
      rw [τ.s_τv_b b m_ge_1] at this
      linarith [this]
    · exact  τ.τv_lt b m_ge_1 m_le_M

  have v'_eq : τ u = v' := by
    apply (τ⁻¹.v_crit a n'_ge_1 (τ u)).mpr
    simp only [τ.inv_mul_cancel_eval]
    constructor
    · suffices n + τ⁻¹.s u a = N by (unfold n'; linarith)
      have split := split_s' h_321a (τ.u_lt b n_ge_1) (τ.v_ge b m_ge_1)
        (τ.τv_lt b m_ge_1 m_le_M) (τ.τu_ge b n_ge_1 n_le_N)
      have := τ.s'_b_τu b n_ge_1; rw [τ.dual_inverse] at this
      rw [this] at split
      convert split using 1; rw [← τ.dual_inverse]
    · exact τ.τu_ge b n_ge_1 n_le_N

  have lamp_equiv : ⟨u', v'⟩ ∈ inv_set α⁻¹.func
    ↔ ⟨m', n'⟩ ∈ α.lamp a := lel_lamp h_321a h_R a m'_ge_1 n'_ge_1
  suffices ⟨u, v⟩ ∈ (τ.sr α) '' inv_set α ∨ ⟨u, v⟩ ∈ inv_set β by
    rwa [← lamp_equiv, ← u'_eq, ← v'_eq, ← τ.sr_crit α u v, Or.comm]

  have uv_inv : ⟨u, v⟩ ∈ inv_set τ := by
    exact ⟨lt_of_lt_of_le u_lt_b v_ge_b, lt_of_lt_of_le τv_lt_a τu_ge_a⟩
  exact h_union uv_inv

lemma excess_of_not_isolated {u v₁ v₂ : ℤ} (v₁_lt_v₂ : v₁ < v₂)
    (uv₁_inv : ⟨u, v₁⟩ ∈ (τ.sr α) '' inv_set α)
    (uv₂_inv : ⟨u, v₂⟩ ∈ inv_set β) :
  let a := τ v₁ + 1
  let b := v₁ + 1

  α.dprod_val_ge β a b (τ.s a b + 1)
  := by
  intro a b
  have uv₁_inv_τ : ⟨u, v₁⟩ ∈ inv_set τ := by
      exact τ.sr_subset α h_R uv₁_inv
  have τ_zero : τ.s a b + 1 = 1 := by
    suffices τ.s a b = 0 by linarith
    have h_empty : southeast_set τ a b = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x x_mem
      simp [southeast_set] at x_mem
      have v₁x_inv : ⟨v₁, x⟩ ∈ inv_set τ := by
        refine (τ.inv_iff_le ?_).mpr ?_
        linarith [x_mem.1]
        linarith [x_mem.2]
      have := tfree_of_is_321a τ h_321a u v₁ x
      rcases this <;> contradiction
    have h_ncard : (southeast_set τ a b).ncard = 0 := by
      exact (Set.ncard_eq_zero (s := southeast_set τ a b) (hs := τ.se_finite a b)).2 h_empty
    have h_cast : ((southeast_set τ a b).ncard : ℤ) = 0 := by exact_mod_cast h_ncard
    simpa [AspPerm.s] using h_cast
  rw [τ_zero]
  let N := τ⁻¹.s b a + 1
  have habMN : a - b + α.χ + β.χ = 1 - N := by
    linarith [τ.duality a b, τ_zero]
  apply (α.ramp_dprod_legos β  a b 1 N habMN).mpr
  rintro m ⟨m_ge_1, m_le_1⟩ n ⟨n_ge_1, n_le_N⟩

  obtain m_one : m = 1 := le_antisymm m_le_1 m_ge_1
  subst m_one

  let n' := N + 1 - n
  change ⟨1, n⟩ ∈ β.ramp b ∨ ⟨1, n'⟩ ∈ α.lamp a

  have u_lt_v₁ : u < v₁ := by linarith [uv₁_inv_τ.1]
  have v₁_le_v₂ : v₁ ≤ v₂ := by linarith
  have τu_ge_a : τ u ≥ a := by linarith [uv₁_inv_τ.2]
  have τv₁_lt_a : τ v₁ < a := by linarith

  have split_eq := split_s' h_321a u_lt_v₁ (le_refl v₁) τv₁_lt_a τu_ge_a
  have : τ⁻¹.s b (τ u) = τ⁻¹.s v₁ (τ u) := by
    apply (τ⁻¹.a_step_eq_iff v₁ (τ u)).mpr
    simpa using uv₁_inv_τ.2
  rw [← this] at split_eq
  have : τ⁻¹.s b a  = τ⁻¹.s v₁ a  := by
    apply (τ⁻¹.a_step_eq_iff v₁ a).mpr
    simpa [inv_inv]
  rw [← this] at split_eq

  have n_bounds : n ≤ τ⁻¹.s b (τ u) ∨ n' ≤ τ⁻¹.s u a + 1:= by
    by_contra!
    have n_sum : n + n' ≥ τ⁻¹.s b a + 3 := by linarith
    have : n + n' = τ⁻¹.s b a + 2 := by linarith [n']
    rw [this] at n_sum
    linarith [n_sum]
  rcases n_bounds with (n_le | n'_le)
  · left
    have u_lt_b : u < b := by linarith [u_lt_v₁]
    have v₂_ge_b : v₂ ≥ b := by linarith
    have := (inv_of_lel_iff_ramp h_321a h_L u_lt_b v₂_ge_b).mp uv₂_inv
    refine β.ramp_closed b ?_ ?_ this
    · linarith [τ.s_nonneg (τ v₂) b]
    · rw [τ.dual_inverse]
      exact n_le
  · right
    suffices ⟨n', 1⟩ ∈ α⁻¹.ramp a by
      rw [α⁻¹.ramp_lamp_dual a] at this
      simpa using this
    have h_inv : ⟨τ v₁, τ u⟩ ∈ inv_set α⁻¹.func := by
      exact  (τ.sr_crit α u v₁).mp uv₁_inv
    have := (inv_of_lel_iff_ramp (inv_is_321a h_321a) h_R τv₁_lt_a τu_ge_a).mp h_inv
    simp [τ.inv_mul_cancel_eval] at this
    refine α⁻¹.ramp_closed a ?_ ?_ this
    · apply le_trans n'_le (le_refl _)
    · rw [τ⁻¹.dual_inverse, inv_inv]
      have : τ.s a v₁ = 1 + τ.s a (v₁ + 1) := by
        linarith [(τ.b_step_one_iff a v₁).mpr τv₁_lt_a]
      rw [this]
      linarith [τ.s_nonneg a (τ v₁ + 1)]

omit h_χ in
lemma not_isolated_of_domino (a b m m' n n' : ℤ)
  (m_pos : m ≥ 1) (m'_pos : m' ≥ 1) (n_pos : n ≥ 1) (n'_pos : n' ≥ 1)
  (msum : m + m' = τ.s a b + 2) (nsum : n + n' = τ⁻¹.s b a + 1)
  (hα : ⟨m', n'⟩ ∈ α.lamp a) (hβ : ⟨m, n⟩ ∈ β.ramp b) :
  ∃ (I J : ℤ × ℤ), {I, J} ⊆ (τ.sr α '' inv_set α) ∩ inv_set β ∧ I ≼ J ∧ I ≠ J
  := by

  have invβ : ⟨β.u b n_pos, β.v b m_pos⟩ ∈ inv_set β :=
    (β.inv_ramp_correspondence b m_pos n_pos).mp hβ
  have := uv_eq_of_lel' h_321a h_L b m_pos n_pos invβ
  let u := τ.u b n_pos
  let v := τ.v b m_pos
  have invβ : ⟨u, v⟩ ∈ inv_set β := by
    rwa [this.1, this.2] at invβ

  have invα := (α⁻¹.inv_ramp_correspondence a n'_pos m'_pos).mp
  have := ((α⁻¹.ramp_lamp_dual a n' m').mpr )
  simp only [inv_inv] at this
  have invα := invα (this hα)
  have := uv_eq_of_lel' (inv_is_321a h_321a) h_R a n'_pos m'_pos invα
  let u' := τ⁻¹.u a m'_pos
  let v' := τ⁻¹.v a n'_pos
  have invα : ⟨u', v'⟩ ∈ inv_set α⁻¹.func := by
    rwa [this.1, this.2] at invα
  have sr : ⟨τ⁻¹ v', τ⁻¹ u'⟩ ∈ (τ.sr α) '' (inv_set α) := by
    apply (τ.sr_crit α (τ⁻¹ v') (τ⁻¹ u')).mpr
    simpa using invα

  have u_lt_b : u < b := τ.u_lt b n_pos
  have s'_ge : τ.s' b a ≥ n := by
    rw [τ.dual_inverse]; linarith
  have s'_ge' : τ⁻¹.s b a ≥ n := by
    rwa [τ.dual_inverse] at s'_ge
  have τu_ge_a : τ u ≥ a := τ.τu_ge b n_pos s'_ge
  have u'_lt_a : u' < a := τ⁻¹.u_lt a m'_pos

  have : n' + n = τ⁻¹.s b a + 1 := by linarith [nsum]
  have := uv_duality_ge (inv_is_321a h_321a) n'_pos n_pos this
  have duality :
      is_snk τ⁻¹ v' → is_snk τ⁻¹ (τ u) → (τ⁻¹ v' ≥ u) ∧ (v' ≥ τ u) := by
    simpa using this
  have v'_snk : is_snk τ⁻¹ v' := snk_of_inv (h_R invα)
  have τiu_snk : is_snk τ⁻¹ (τ u) := by
    have : ⟨τ v, τ u⟩ ∈ inv_set τ⁻¹.func := by
      have := h_L invβ
      use this.2
      simp; exact this.1
    exact snk_of_inv this
  have ineqs := duality v'_snk τiu_snk
  have u_le_τiv' : u ≤ τ⁻¹ v' := ineqs.1
  have τu_le_v' : τ u ≤ v' := ineqs.2
  clear ineqs duality this v'_snk τiu_snk -- bit of cleanup

  have Iτ : ⟨τ⁻¹ v', τ⁻¹ u'⟩ ∈ inv_set τ := by
    apply h_R at invα
    use invα.2
    simp; use invα.1

  have lt_v : τ⁻¹ u' < v :=
    uv_duality_lt h_321a a b m_pos m'_pos (le_of_eq <| Eq.symm msum)
      (snk_of_inv <| h_L invβ) (snk_of_inv Iτ)

  let I : ℤ × ℤ :=  ⟨τ⁻¹ v', τ⁻¹ u'⟩
  let J : ℤ × ℤ := ⟨u, v⟩
  have Iα : I ∈ (τ.sr α) '' (inv_set α) := sr
  have Jβ : J ∈ inv_set β := invβ

  have I_prec_J : I ≼ J := by
    constructor
    · exact u_le_τiv'
    · change τ⁻¹ u' ≤ v
      exact le_of_lt lt_v

  have Iβ : I ∈ inv_set β :=
    (inv_of_lel_iff h_321a h_L Jβ I_prec_J).mpr Iτ
  have Jα : J ∈ (τ.sr α) '' (inv_set α) := by
    let K : ℤ × ℤ := ⟨τ v, τ u⟩
    suffices K ∈ inv_set α⁻¹.func by exact (τ.sr_crit α u v).mpr this
    have prec : K ≼ ⟨u', v'⟩ := by
      constructor
      · have u'_snk : is_snk τ (τ⁻¹ u')  := snk_of_inv Iτ
        have v_snk : is_snk τ v := snk_of_inv (h_L Jβ)
        have := le_of_lt <| snk_lt h_321a u'_snk lt_v
        simpa using this
      · exact τu_le_v'
    have lel : α⁻¹ ≤L τ⁻¹ := by
      intro x hx
      exact h_R hx
    apply  (inv_of_lel_iff (τ := τ⁻¹) (β := α⁻¹) (inv_is_321a h_321a) lel invα prec).mpr
    use (h_L Jβ).2
    simp
    exact Jβ.1

  have I_ne_J : I ≠ J := by
    intro heq
    have : I.2 = J.2 := by rw [heq]
    linarith

  use I, J
  constructor
  · intro x hx
    rcases hx with (xI | xJ)
    · subst xI; exact ⟨Iα, Iβ⟩
    · subst xJ; exact ⟨Jα, Jβ⟩
  exact ⟨I_prec_J, I_ne_J⟩

lemma not_isolated_of_excess {a b : ℤ} (h_s : α.dprod_val_ge β a b (τ.s a b + 1)) :
  ∃ (I J : ℤ × ℤ), {I, J} ⊆ (τ.sr α '' inv_set α) ∩ inv_set β ∧ I ≼ J ∧ I ≠ J
  := by
  let M := τ.s a b + 1
  let N := τ⁻¹.s b a + 1
  have N_pos : N ≥ 1 := by linarith [τ⁻¹.s_nonneg b a]
  have M_pos : M ≥ 1 := by linarith [τ.s_nonneg a b]
  have hMN : a - b + α.χ + β.χ = M - N := by linarith [τ.duality a b]

  have legos : ∀ m ∈ Set.Icc 1 M, ∀ n ∈ Set.Icc 1 N,
    ⟨m, n⟩ ∈ β.ramp b ∨ ⟨M+1-m, N+1-n⟩ ∈ α.lamp a :=
    (AspPerm.ramp_dprod_legos α β a b M N hMN).mp h_s

  have corner_nramp : ⟨M, N⟩ ∉ β.ramp b := by
    intro mem_ramp
    have M_pos : M > 0 := by linarith [τ.s_nonneg a b]
    have N_pos : N > 0 := by linarith [τ⁻¹.s_nonneg b a]
    have uv_inv_β : ⟨β.u b N_pos, β.v b M_pos⟩ ∈ inv_set β := by
      exact (β.inv_ramp_correspondence b M_pos N_pos).mp mem_ramp
    have uv_eq := uv_eq_of_lel' h_321a h_L b M_pos N_pos uv_inv_β
    have uv_inv_τ : ⟨τ.u b N_pos, τ.v b M_pos⟩ ∈ inv_set τ := by
      simpa [uv_eq.1, uv_eq.2] using (h_L uv_inv_β)
    have mem_ramp_τ : ⟨M, N⟩ ∈ τ.ramp b := by
      exact (τ.inv_ramp_correspondence b M_pos N_pos).mpr uv_inv_τ
    have : τ.s a b ≥ M := by
      convert (τ.mem_ramp_iff_s_ge b M N).mp mem_ramp_τ
      linarith [hMN]
    linarith [this]

  have corner_nlamp : ⟨M, N⟩ ∉ α.lamp a := by
    intro mem_lamp
    have mem_ramp_inv : ⟨N, M⟩ ∈ α⁻¹.ramp a := by
      simpa [α⁻¹.ramp_lamp_dual a] using mem_lamp

    have uv_inv_αi : ⟨α⁻¹.u a M_pos, α⁻¹.v a N_pos⟩ ∈ inv_set α⁻¹.func := by
      exact (α⁻¹.inv_ramp_correspondence a N_pos M_pos).mp mem_ramp_inv
    have uv_eq := uv_eq_of_lel' (τ := τ⁻¹) (β := α⁻¹)
      (inv_is_321a h_321a) h_R a N_pos M_pos uv_inv_αi
    have uv_inv_τi : ⟨(τ⁻¹).u a M_pos, (τ⁻¹).v a N_pos⟩ ∈ inv_set τ⁻¹.func := by
      simpa [uv_eq.1, uv_eq.2] using (h_R uv_inv_αi)
    have mem_ramp_τi : ⟨N, M⟩ ∈ τ⁻¹.ramp a := by
      exact (τ⁻¹.inv_ramp_correspondence a N_pos M_pos).mpr uv_inv_τi
    have : τ⁻¹.s b a ≥ N := by
      have hba : a + N - M - τ⁻¹.χ = b := by
        rw [τ.chi_dual]
        linarith [hMN, h_χ]
      simpa [hba] using (τ⁻¹.mem_ramp_iff_s_ge a N M).mp mem_ramp_τi
    have : τ⁻¹.s b a ≥ τ⁻¹.s b a + 1 := by simp [N, this]
    linarith

  have corner_lamp: ⟨1, 1⟩ ∈ α.lamp a := by
    have icc : M ∈ Set.Icc 1 M := ⟨M_pos, le_refl M⟩
    have icc' : N ∈ Set.Icc 1 N := ⟨N_pos, le_refl N⟩
    have options := legos M icc N icc'
    rcases options with (hβ | hα)
    · exfalso; exact corner_nramp hβ
    · simpa using hα

  have domino : ∃ m ∈ Set.Icc 1 M, ∃ n ∈ Set.Icc 1 N,
      ⟨M + 1 - m, N + 1 - n⟩ ∈ α.lamp a ∧
        ((⟨m - 1, n⟩ ∈ β.ramp b ∧ m ≥ 2) ∨
          (⟨m, n - 1⟩ ∈ β.ramp b ∧ n ≥ 2)) := by
    -- S encodes α.lamp a via the coordinate flip (m,n) ↦ (M+1-m, N+1-n).
    -- (M,N) ∈ S since corner_lamp gives (1,1) ∈ α.lamp a;
    -- (1,1) ∉ S since corner_nlamp gives (M,N) ∉ α.lamp a.
    -- A minimal element of S then gives the desired domino via legos.
    let S : Set (ℤ × ℤ) :=
      {p | p.1 ∈ Set.Icc 1 M ∧ p.2 ∈ Set.Icc 1 N ∧ ⟨M+1-p.1, N+1-p.2⟩ ∈ α.lamp a}
    have hMN_S : ⟨M, N⟩ ∈ S :=
      ⟨⟨M_pos, le_refl M⟩, ⟨N_pos, le_refl N⟩, by simpa using corner_lamp⟩
    have h11_nS : ⟨(1 : ℤ), 1⟩ ∉ S := fun h => corner_nlamp (by simpa [S] using h.2.2)
    obtain ⟨m, n, _, _, hmn_S, hmin⟩ :=
      Utils.min_helper (m_pos := M_pos) (n_pos := N_pos) hMN_S h11_nS
    obtain ⟨m_Icc, n_Icc, hLamp⟩ :
        m ∈ Set.Icc 1 M ∧ n ∈ Set.Icc 1 N ∧ ⟨M+1-m, N+1-n⟩ ∈ α.lamp a :=
      by simpa [S] using hmn_S
    refine ⟨m, m_Icc, n, n_Icc, hLamp, ?_⟩
    rcases hmin with (⟨hnotS, hm_ge⟩ | ⟨hnotS, hn_ge⟩)
    · left
      have m1_Icc : m - 1 ∈ Set.Icc 1 M := ⟨by linarith, by linarith [m_Icc.2]⟩
      rcases legos (m - 1) m1_Icc n n_Icc with (hβ | hα')
      · exact ⟨hβ, hm_ge⟩
      · exact absurd ⟨m1_Icc, ⟨n_Icc, hα'⟩⟩ hnotS
    · right
      have n1_Icc : n - 1 ∈ Set.Icc 1 N := ⟨by linarith, by linarith [n_Icc.2]⟩
      rcases legos m m_Icc (n - 1) n1_Icc with (hβ | hα')
      · exact ⟨hβ, hn_ge⟩
      · exact absurd ⟨m_Icc, ⟨n1_Icc, hα'⟩⟩ hnotS

  rcases domino with ⟨m, m_Icc, n, n_Icc, hα, (⟨hβ,m_ge_2⟩ | ⟨hβ,n_ge_2⟩)⟩
  · -- Switch to τ⁻¹ to apply the domino helper lemma
    have leR : β⁻¹ ≤R τ⁻¹ := AspPerm.le_weak_R_of_L h_L
    have h_χ' : τ⁻¹.χ = β⁻¹.χ + α⁻¹.χ := by
      rw [τ.chi_dual, α.chi_dual, β.chi_dual]
      linarith [h_χ]
    have hβi : ⟨n, m-1⟩ ∈ β⁻¹.lamp b := (β.ramp_lamp_dual b (m-1) n).mp hβ
    have hαi : ⟨N+1-n, M+1-m⟩ ∈ α⁻¹.ramp a := by
      simpa [α⁻¹.ramp_lamp_dual a]
    have := not_isolated_of_domino (inv_is_321a h_321a) h_R leR b a (N + 1 - n) n
      (M + 1 - m) (m - 1)
      (by linarith [n_Icc.2]) n_Icc.1
      (by linarith [m_Icc.2]) (by linarith [m_ge_2]) (by linarith) (by simp; linarith) hβi hαi
    rcases this with ⟨⟨u₁, v₁⟩, ⟨u₂, v₂⟩, ⟨h_mem, h_nest⟩⟩
    have h1_mem :
        ⟨u₁, v₁⟩ ∈
          ((τ⁻¹.sr β⁻¹) '' inv_set β⁻¹.func) ∩ inv_set α⁻¹.func :=
      h_mem (by simp : (u₁, v₁) ∈ ({(u₁, v₁), (u₂, v₂)} : Set (ℤ × ℤ)))
    have h2_mem :
        ⟨u₂, v₂⟩ ∈
          ((τ⁻¹.sr β⁻¹) '' inv_set β⁻¹.func) ∩ inv_set α⁻¹.func :=
      h_mem (by simp : (u₂, v₂) ∈ ({(u₁, v₁), (u₂, v₂)} : Set (ℤ × ℤ)))

    have h1_sr : ⟨τ⁻¹ v₁, τ⁻¹ u₁⟩ ∈ (τ.sr α) '' inv_set α := by
      apply (τ.sr_crit α (τ⁻¹ v₁) (τ⁻¹ u₁)).mpr
      simpa using h1_mem.2
    have h2_sr : ⟨τ⁻¹ v₂, τ⁻¹ u₂⟩ ∈ (τ.sr α) '' inv_set α := by
      apply (τ.sr_crit α (τ⁻¹ v₂) (τ⁻¹ u₂)).mpr
      simpa using h2_mem.2

    have h1_inv : ⟨τ⁻¹ v₁, τ⁻¹ u₁⟩ ∈ inv_set β := by
      have : ⟨τ⁻¹ v₁, τ⁻¹ u₁⟩ ∈ inv_set ((β⁻¹)⁻¹).func := by
        exact ((τ⁻¹).sr_crit β⁻¹ u₁ v₁).mp h1_mem.1
      simpa [inv_inv] using this
    have h2_inv : ⟨τ⁻¹ v₂, τ⁻¹ u₂⟩ ∈ inv_set β := by
      have : ⟨τ⁻¹ v₂, τ⁻¹ u₂⟩ ∈ inv_set ((β⁻¹)⁻¹).func := by
        exact ((τ⁻¹).sr_crit β⁻¹ u₂ v₂).mp h2_mem.1
      simpa [inv_inv] using this

    have h_uv : ⟨u₁, v₁⟩ ≼ ⟨u₂, v₂⟩ := h_nest.1
    have hu : u₂ ≤ u₁ := h_uv.1
    have hv : v₁ ≤ v₂ := h_uv.2

    have u1_src : is_src (τ⁻¹) u₁ :=
      src_of_src h_R (src_of_inv h1_mem.2)
    have u2_src : is_src (τ⁻¹) u₂ :=
      src_of_src h_R (src_of_inv h2_mem.2)
    have v1_snk : is_snk (τ⁻¹) v₁ :=
      snk_of_snk h_R (snk_of_inv h1_mem.2)
    have v2_snk : is_snk (τ⁻¹) v₂ :=
      snk_of_snk h_R (snk_of_inv h2_mem.2)

    have hu_inv : τ⁻¹ u₂ ≤ τ⁻¹ u₁ :=
      src_ge (inv_is_321a h_321a) u1_src hu
    have hv_inv : τ⁻¹ v₁ ≤ τ⁻¹ v₂ :=
      snk_le (inv_is_321a h_321a) v1_snk hv

    use ⟨τ⁻¹ v₂, τ⁻¹ u₂⟩, ⟨τ⁻¹ v₁, τ⁻¹ u₁⟩
    refine ⟨?_, ?_, ?_⟩
    · intro I hI
      rcases hI with (rfl | rfl)
      · exact ⟨h2_sr, h2_inv⟩
      · exact ⟨h1_sr, h1_inv⟩
    · exact ⟨hv_inv, hu_inv⟩
    · intro h_eq
      apply h_nest.2
      apply Prod.ext
      · apply τ⁻¹.injective
        have h := congrArg Prod.snd h_eq
        simpa [τ.inv_mul_cancel_eval] using h.symm
      · apply τ⁻¹.injective
        have h := congrArg Prod.fst h_eq
        simpa [τ.inv_mul_cancel_eval] using h.symm
  · exact not_isolated_of_domino h_321a h_L h_R a b m (M+1-m)
      (n-1) (N+1-n) m_Icc.1 (by linarith [m_Icc.2])
      (by linarith [n_ge_2]) (by linarith [n_Icc.2])
      (by linarith) (by linarith)
      hα hβ

-- Main result

theorem dprod_ge_iff_union :
    τ ≤ α ⋆ β ↔ inv_set τ ⊆ (τ.sr α) '' inv_set α ∪ inv_set β := by
  rw [τ.le_star_iff α β]
  constructor
  · intro ge
    rintro ⟨u, v⟩ uv_inv
    let a := τ u
    let b := v
    exact inversion_in_union h_321a h_L h_R h_χ (τ u) v u v
      (ge a b) uv_inv.1 (le_refl _) (le_refl _) uv_inv.2
  · intro h_sub a b
    apply union_sufficient h_321a h_L h_R h_χ a b h_sub

def isolated (S : Set (ℤ × ℤ)) : Prop := ∀ I ∈ S, ∀ J ∈ S, I ≼ J → I = J

theorem dprod_le_iff_isolated : α ⋆ β ≤ τ
  ↔ isolated ((τ.sr α) '' (inv_set α) ∩ inv_set β)  := by
  rw [τ.ge_star_iff α β]
  constructor
  · rintro le ⟨u, v⟩ I_mem ⟨u', v'⟩ J_mem h_prec
    have u'_le_u : u' ≤ u := h_prec.1
    have v_le_v' : v ≤ v' := h_prec.2
    contrapose! le with I_ne_J
    dsimp [AspPerm.ge_dprod, AspPerm.dprod_val_le]; push_neg

    by_cases u_eq_u' : u = u'
    · have v_lt_v' : v < v' := by
        by_contra!
        have v_eq_v' : v = v' := le_antisymm v_le_v' this
        subst v_eq_v' u_eq_u'
        exact I_ne_J rfl
      rw [← u_eq_u'] at J_mem
      have excess := excess_of_not_isolated h_321a h_L h_R h_χ v_lt_v' I_mem.1 J_mem.2
      use τ v + 1, v+1
      exact excess
    -- Now assume u' < u instead
    have u'_ne_u : u' ≠ u := by
      intro h; rw [h] at u_eq_u'; exact u_eq_u' rfl
    have v_snk_β : is_snk β v := snk_of_inv I_mem.2
    have v_snk_τ : is_snk τ v := snk_of_inv (h_L I_mem.2)
    have u_src_τ : is_src τ u := src_of_inv (h_L I_mem.2)
    have βv'_ge_βv : β v' ≥ β v:= snk_le (is_321a_of_lel h_321a h_L) v_snk_β v_le_v'
    have τu'_le_τu : τ u' ≤ τ u := src_ge h_321a u_src_τ u'_le_u

    have u'_lt_v : u' < v := lt_of_le_of_lt h_prec.1 I_mem.2.1
    have βu'_gt_βv : β u' > β v := lt_of_le_of_lt βv'_ge_βv J_mem.2.2
    have hb : ⟨τ v, τ u'⟩ ∈ (τ⁻¹.sr β⁻¹) '' (inv_set β⁻¹.func) := by
      apply ((τ⁻¹).sr_crit β⁻¹ (τ v) (τ u')).mpr
      suffices ⟨u', v⟩ ∈ inv_set β by simpa
      exact ⟨u'_lt_v, βu'_gt_βv⟩
    have dualχ : τ⁻¹.χ = β⁻¹.χ + α⁻¹.χ := by
      repeat rw [AspPerm.chi_dual]
      linarith [h_χ]

    have τu'_lt_τu : τ u' < τ u := by
      apply lt_of_le_of_ne τu'_le_τu
      intro h
      apply τ.injective at h
      contradiction
    have h := excess_of_not_isolated (inv_is_321a h_321a) h_R (AspPerm.le_weak_R_of_L h_L) dualχ
      (u := τ v) (v₁ := τ u') (v₂ := τ u) τu'_lt_τu hb
      ((τ.sr_crit α u v).mp I_mem.1)
    let a := u' + 1
    let b := τ u' + 1
    use b, a
    obtain excess : β⁻¹.dprod_val_ge α⁻¹ a b (τ⁻¹.s a b + 1) := by simpa using h
    dsimp [AspPerm.dprod_val_ge] at excess
    intro x; specialize excess x
    rw [α.s'_eq, β.s'_eq, τ.s'_eq] at excess
    omega
  · intro no_excess a b
    contrapose! no_excess with ne_le
    dsimp [AspPerm.dprod_val_le] at ne_le; push_neg at ne_le
    have ge : α.dprod_val_ge β a b (τ.s a b + 1) := by
      intro x
      specialize ne_le x
      linarith
    have concl := not_isolated_of_excess h_321a h_L h_R h_χ ge
    contrapose! concl with isolated
    intro I J mems prec
    have I_mem : I ∈ (τ.sr α) '' (inv_set α) ∩ inv_set β := by
      apply mems; simp
    have J_mem : J ∈ (τ.sr α) '' (inv_set α) ∩ inv_set β := by
      apply mems; simp
    exact isolated I I_mem J J_mem prec

omit h_L h_R h_χ in
theorem dprod_eq_iff : τ = α ⋆ β
  ↔ (α.χ + β.χ = τ.χ)
    ∧ inv_set τ = (τ.sr α) '' (inv_set α) ∪ inv_set β
    ∧ isolated ((τ.sr α) '' (inv_set α) ∩ inv_set β)
  := by
  constructor
  · intro dprod
    have h_χ : α.χ + β.χ = τ.χ := by
      rw [dprod]
      exact Eq.symm <| AspPerm.chi_star α β
    apply And.intro h_χ
    have h_R : α ≤R τ := by
      rw [dprod]
      exact Submodular.ler_of_dprod α β
    have h_L : β ≤L τ := by
      rw [dprod]
      exact Submodular.lel_of_dprod α β
    have : τ ≤ α ⋆ β := by
      rw [dprod]
    have subset := (dprod_ge_iff_union h_321a h_L h_R (Eq.symm h_χ)).mp this
    constructor
    · apply subset.antisymm
      rintro ⟨u, v⟩ uv_union
      rcases uv_union with (h_sr | h_β)
      · exact (τ.sr_subset α) h_R h_sr
      · exact h_L h_β
    · rw [← dprod_le_iff_isolated h_321a h_L h_R (Eq.symm h_χ) ]
      rw [dprod]
  · rintro ⟨h_χ, ⟨h_union, h_isol⟩⟩
    have h_L : β ≤L τ := by
      intro x hx
      rw [h_union]
      exact Or.inr hx
    have h_R : α ≤R τ := by
      rintro ⟨u, v⟩ hx
      have sr := (τ.sr_crit α (τ⁻¹ v) (τ⁻¹ u)).mpr
      simp only [τ.mul_inv_cancel_eval] at sr
      apply sr at hx
      have := τ.inv_set_inverse (τ⁻¹ v) (τ⁻¹ u)
      simp only [τ.mul_inv_cancel_eval] at this
      rw [← this]
      rw [h_union]
      exact Or.inl hx
    rw [AspPerm.eq_star_iff]
    constructor
    · rw [← τ.le_star_iff]
      rw [dprod_ge_iff_union h_321a h_L h_R (Eq.symm h_χ)]
      rw [h_union]
    · rw [← τ.ge_star_iff]
      exact (dprod_le_iff_isolated h_321a h_L h_R (Eq.symm h_χ)).mpr h_isol

end factorization
end fixed_321a_and_lel
end fixed_321a

section Link

def linked (A : Set (ℤ × ℤ)) (B : Set (ℤ × ℤ)) : Prop :=
  ∀ p ∈ A, ∀ q ∈ B, p ≼ q → p = q

structure Link where
  A : Set (ℤ × ℤ)
  B : Set (ℤ × ℤ)
  S : tfas
  χa : ℤ
  χb : ℤ
  union_eq : A ∪ B = S.I
  sep : linked A B

def link_of_sets {A B : Set (ℤ × ℤ)} (sep : linked A B) (tf : set_321a_prop (A ∪ B))
  (χa χb : ℤ) : Link :=
  ⟨A, B, ⟨⟨A ∪ B, tf.asp⟩, tf⟩, χa, χb, rfl, sep⟩

namespace Link
def chi (L : Link) : ℤ :=
  L.χa + L.χb

lemma B_subset (L : Link) : L.B ⊆ L.S.I := by
  rw [← L.union_eq]
  apply Set.subset_union_right

lemma A_subset (L : Link) : L.A ⊆ L.S.I := by
  rw [← L.union_eq]
  apply Set.subset_union_left

lemma mem_A_of_mem_inv_not_mem_B (L : Link) {p : ℤ × ℤ}
  (hpτ : p ∈ L.S.I) (hpB : p ∉ L.B) : p ∈ L.A := by
  rw [← L.union_eq] at hpτ
  rcases hpτ with (hpA | hpB')
  · exact hpA
  · exact (hpB hpB').elim

theorem ext {L₁ L₂ : Link}
    (hA : L₁.A = L₂.A) (hB : L₁.B = L₂.B)
    (hχa : L₁.χa = L₂.χa) (hχb : L₁.χb = L₂.χb) : L₁ = L₂ := by
  have hS : L₁.S = L₂.S := by
    cases hs1 : L₁.S with
    | mk S1 p1 =>
      cases hs2 : L₂.S with
      | mk S2 p2 =>
        have hI : S1.I = S2.I := by
          simpa [hs1, hs2] using (by
            rw [← L₁.union_eq, ← L₂.union_eq, hA, hB] : L₁.S.I = L₂.S.I)
        have hAsp : S1 = S2 := _root_.AspSet.ext hI
        rw [tfas.mk.injEq]
        simpa using hAsp
  cases L₁
  cases L₂
  cases hA
  cases hB
  cases hχa
  cases hχb
  simpa

lemma B_AspSet_prop (L : Link) :
  AspSet_prop L.B where
  directed := by
    intro u v huv
    exact L.S.directed u v (L.B_subset huv)
  closed := by
    intro u v w huv hvw
    exfalso
    have huvS : ⟨u, v⟩ ∈ L.S.I := L.B_subset huv
    have hvwS : ⟨v, w⟩ ∈ L.S.I := L.B_subset hvw
    rcases L.S.prop_321a.tfree u v w with (huv' | hvw')
    · exact huv' huvS
    · exact hvw' hvwS
  coclosed := by
    intro u v w u_lt_v v_lt_w huv hvw
    by_contra! huw

    have := L.S.coclosed u v w u_lt_v v_lt_w
    have h : ⟨u, v⟩ ∈ L.S.I ∨ ⟨v, w⟩ ∈ L.S.I := by
      by_contra! h'
      exact this h'.1 h'.2 (L.B_subset huw)
    rcases h with (h_uv | h_vw)
    · have huv' : ⟨u, v⟩ ∈ L.A := L.mem_A_of_mem_inv_not_mem_B h_uv huv
      have : ⟨u, v⟩ ≼ ⟨u, w⟩ := by
        constructor
        · exact le_refl u
        · exact le_of_lt v_lt_w
      have := L.sep ⟨u, v⟩ huv' ⟨u, w⟩ huw this
      have : v = w := by
        simpa
      rw [this] at v_lt_w
      exact lt_irrefl w v_lt_w
    · have hvw' : ⟨v, w⟩ ∈ L.A := L.mem_A_of_mem_inv_not_mem_B h_vw hvw
      have : ⟨v, w⟩ ≼ ⟨u, w⟩ := by
        constructor
        · exact le_of_lt u_lt_v
        · exact le_refl w
      have := L.sep ⟨v, w⟩ hvw' ⟨u, w⟩ huw this
      have : v = u := by
        simpa
      rw [this] at u_lt_v
      exact lt_irrefl u u_lt_v
  finite_outdegree := by
    intro u
    exact (L.S.finite_outdegree u).subset (by
      intro v hv
      exact L.B_subset hv)
  finite_indegree := by
    intro v
    exact (L.S.finite_indegree v).subset (by
      intro u hu
      exact L.B_subset hu)

lemma B_set_321a_prop (L : Link) : set_321a_prop L.B where
  asp := L.B_AspSet_prop
  tfree := by
    intro u v w
    rcases L.S.prop_321a.tfree u v w with (huv | hvw)
    · left
      intro huvB
      exact huv (L.B_subset huvB)
    · right
      intro hvwB
      exact hvw (L.B_subset hvwB)

def B_AspSet (L : Link) : AspSet :=
  ⟨L.B, L.B_AspSet_prop⟩

noncomputable def τ (L : Link) : AspPerm :=
  L.S.toAspPerm L.chi

@[simp]
lemma inv_set_τ (L : Link) : inv_set L.τ = L.S.I := by
  simpa [Link.τ] using (L.S.toAspSet.invSet_of_toAspPerm L.chi)

lemma is_321a_τ (L : Link) : is_321a L.τ := by
  rw [is_321a_iff_set_321a_prop L.τ L.τ.bijective]
  simpa [Link.τ] using set_321a_prop_of_func L.S L.chi

@[simp]
lemma chi_tau (L : Link) : L.τ.χ = L.chi := by
  simpa [Link.τ] using (L.S.toAspSet.chi_of_toAspPerm L.chi)

noncomputable def β (L : Link) : AspPerm :=
  L.B_AspSet.toAspPerm L.χb

@[simp]
lemma inv_set_β (L : Link) : inv_set L.β = L.B := by
  simpa [Link.β, Link.B_AspSet] using (L.B_AspSet.invSet_of_toAspPerm L.χb)

@[simp]
lemma chi_beta (L : Link) : L.β.χ = L.χb := by
  simpa [Link.β] using (L.B_AspSet.chi_of_toAspPerm L.χb)

lemma A_AspSet_prop (L : Link) :
  AspSet_prop (L.τ.rev_map '' L.A) := by
  let L' : Link := {
    A := L.τ.rev_map '' L.B
    B := L.τ.rev_map '' L.A
    S := tfas_of_perm (inv_is_321a (L.is_321a_τ))
    χa := -L.χb
    χb := -L.χa
    union_eq := by
      ext ⟨u, v⟩
      change ⟨u, v⟩ ∈ L.τ.rev_map '' L.B ∪ L.τ.rev_map '' L.A ↔
        ⟨u, v⟩ ∈ inv_set (((L.τ)⁻¹).func)
      constructor
      · intro h
        rcases h with (hB | hA)
        · rcases hB with ⟨⟨u', v'⟩, hu'v', hEq⟩
          simp [AspPerm.rev_map] at hEq
          rcases hEq with ⟨rfl, rfl⟩
          have hu'v'τ : ⟨u', v'⟩ ∈ inv_set L.τ := by
            simpa [L.inv_set_τ] using L.B_subset hu'v'
          exact (L.τ.inv_set_inverse u' v').mp hu'v'τ
        · rcases hA with ⟨⟨u', v'⟩, hu'v', hEq⟩
          simp [AspPerm.rev_map] at hEq
          rcases hEq with ⟨rfl, rfl⟩
          have hu'v'τ : ⟨u', v'⟩ ∈ inv_set L.τ := by
            simpa [L.inv_set_τ] using L.A_subset hu'v'
          exact (L.τ.inv_set_inverse u' v').mp hu'v'τ
      · intro h
        have h' : ⟨L.τ⁻¹ v, L.τ⁻¹ u⟩ ∈ inv_set L.τ := by
          have hτi :
              ⟨L.τ (L.τ⁻¹ u), L.τ (L.τ⁻¹ v)⟩ ∈ inv_set ((L.τ)⁻¹).func := by
            simpa using h
          have := (L.τ.inv_set_inverse (L.τ⁻¹ v) (L.τ⁻¹ u)).mpr hτi
          simpa using this
        have h'' : ⟨L.τ⁻¹ v, L.τ⁻¹ u⟩ ∈ L.S.I := by
          simpa [L.inv_set_τ] using h'
        rw [← L.union_eq] at h''
        rcases h'' with (hA | hB)
        · right
          refine ⟨⟨L.τ⁻¹ v, L.τ⁻¹ u⟩, hA, ?_⟩
          simp [AspPerm.rev_map]
        · left
          refine ⟨⟨L.τ⁻¹ v, L.τ⁻¹ u⟩, hB, ?_⟩
          simp [AspPerm.rev_map]
    sep := by
      intro p hp q hq hpq
      rcases hp with ⟨⟨u, v⟩, huv, rfl⟩
      rcases hq with ⟨⟨u', v'⟩, hu'v', rfl⟩
      simp [AspPerm.rev_map] at hpq
      have hpτi : ⟨L.τ v, L.τ u⟩ ∈ inv_set (((L.τ)⁻¹).func) := by
        have huvτ : ⟨u, v⟩ ∈ inv_set L.τ := by
          simpa [L.inv_set_τ] using L.B_subset huv
        exact (L.τ.inv_set_inverse u v).mp huvτ
      have hqτi : ⟨L.τ v', L.τ u'⟩ ∈ inv_set (((L.τ)⁻¹).func) := by
        have hu'v'τ : ⟨u', v'⟩ ∈ inv_set L.τ := by
          simpa [L.inv_set_τ] using L.A_subset hu'v'
        exact (L.τ.inv_set_inverse u' v').mp hu'v'τ
      have hqup : u ≤ u' := by
        have hu_snk : is_snk (L.τ⁻¹) (L.τ u) := snk_of_inv hpτi
        simpa using snk_le (inv_is_321a (L.is_321a_τ)) hu_snk hpq.2
      have hvpv : v' ≤ v := by
        have hv_src : is_src (L.τ⁻¹) (L.τ v) := src_of_inv hpτi
        simpa using src_ge (inv_is_321a (L.is_321a_τ)) hv_src hpq.1
      have hqp : ⟨u', v'⟩ ≼ ⟨u, v⟩ := by
        exact ⟨hqup, hvpv⟩
      have hEq : (u', v') = (u, v) := L.sep (u', v') hu'v' (u, v) huv hqp
      simpa [AspPerm.rev_map] using congrArg L.τ.rev_map hEq.symm
    }
  have h' := B_AspSet_prop L'
  simpa [L'] using h'

def A_AspSet (L : Link) : AspSet :=
  ⟨L.τ.rev_map '' L.A, A_AspSet_prop L⟩

noncomputable def α (L : Link) : AspPerm :=
  (L.A_AspSet.toAspPerm (-L.χa))⁻¹

@[simp]
lemma inv_set_α (L : Link) : L.A = L.τ.sr L.α '' inv_set L.α := by
  have hAinv : inv_set (((Link.α L)⁻¹).func) = L.τ.rev_map '' L.A := by
    simpa [Link.α, Link.A_AspSet] using (L.A_AspSet.invSet_of_toAspPerm (-L.χa))
  ext ⟨u, v⟩
  constructor
  · intro huv
    apply (L.τ.sr_crit L.α u v).mpr
    rw [hAinv]
    exact ⟨⟨u, v⟩, huv, by simp [AspPerm.rev_map]⟩
  · intro huv
    have hrev : ⟨L.τ v, L.τ u⟩ ∈ L.τ.rev_map '' L.A := by
      rw [← hAinv]
      exact (L.τ.sr_crit L.α u v).mp huv
    rcases hrev with ⟨⟨u', v'⟩, hu'v', hEq⟩
    simp [AspPerm.rev_map] at hEq
    rcases hEq with ⟨hv, hu⟩
    apply L.τ.injective at hv
    apply L.τ.injective at hu
    simpa [hu, hv] using hu'v'

@[simp]
lemma chi_alpha (L : Link) : L.α.χ = L.χa := by
  rw [Link.α, AspPerm.chi_dual]
  have hχ := L.A_AspSet.chi_of_toAspPerm (-L.χa)
  linarith

lemma dprod (L : Link) : L.α ⋆ L.β = L.τ := by
  have hτ : L.τ = L.α ⋆ L.β := by
    apply (dprod_eq_iff (τ := L.τ) (α := L.α) (β := L.β) (L.is_321a_τ)).mpr
    constructor
    · rw [L.chi_alpha, L.chi_beta, L.chi_tau, Link.chi]
    constructor
    · simpa [L.inv_set_τ, L.inv_set_α, L.inv_set_β] using L.union_eq.symm
    · intro p hp q hq hpq
      have hp' : p ∈ L.A ∩ L.B := by
        simpa [L.inv_set_α, L.inv_set_β] using hp
      have hq' : q ∈ L.A ∩ L.B := by
        simpa [L.inv_set_α, L.inv_set_β] using hq
      exact L.sep p hp'.1 q hq'.2 hpq
  exact hτ.symm

end Link

variable {τ : AspPerm} (h_321a : is_321a τ)
include h_321a

noncomputable def Link_of_dprod {α β : AspPerm}
  (dprod : α ⋆ β = τ) : Link where
  A := (τ.sr α) '' inv_set α
  B := inv_set β
  S := tfas_of_perm h_321a
  χa := α.χ
  χb := β.χ
  union_eq := by
    have hboxes := ((dprod_eq_iff (τ := τ) (α := α) (β := β) h_321a).mp dprod.symm).2
    exact hboxes.1.symm
  sep := by
    intro p hp q hq hpq
    have h_L : β ≤L τ := by
      rw [← dprod]
      exact Submodular.lel_of_dprod α β
    have h_R : α ≤R τ := by
      rw [← dprod]
      exact Submodular.ler_of_dprod α β
    have hp' : p ∈ inv_set β := by
      exact (inv_of_lel_iff (τ := τ) (β := β) h_321a h_L hq hpq).mpr
        ((AspPerm.sr_subset τ α h_R) hp)
    have hq' : q ∈ (τ.sr α) '' (inv_set α) := by
      exact (sr_inv_of_ler_iff (τ := τ) h_321a h_R hp hpq).mpr (h_L hq)
    have hboxes := ((dprod_eq_iff (τ := τ) (α := α) (β := β) h_321a).mp dprod.symm).2
    exact hboxes.2 p ⟨hp, hp'⟩ q ⟨hq', hq⟩ hpq

lemma rev_A_eq_inv_inv_of_Link_of_dprod {α β : AspPerm} (dprod : α ⋆ β = τ) :
  τ.rev_map '' (Link_of_dprod h_321a dprod).A = inv_set α⁻¹.func := by
  ext ⟨u, v⟩
  change
    ⟨u, v⟩ ∈ τ.rev_map '' (τ.sr α '' inv_set α.func) ↔
      ⟨u, v⟩ ∈ inv_set α⁻¹.func
  constructor
  · intro h
    rcases h with ⟨⟨u', v'⟩, hu'v', hEq⟩
    have hα : ⟨τ v', τ u'⟩ ∈ inv_set α⁻¹.func := (τ.sr_crit α u' v').mp hu'v'
    simp [AspPerm.rev_map] at hEq
    rcases hEq with ⟨hv, hu⟩
    simpa [hv, hu] using hα
  · intro huv
    have hsr : ⟨τ⁻¹ v, τ⁻¹ u⟩ ∈ τ.sr α '' inv_set α := by
      apply (τ.sr_crit α (τ⁻¹ v) (τ⁻¹ u)).mpr
      simpa using huv
    refine ⟨⟨τ⁻¹ v, τ⁻¹ u⟩, hsr, ?_⟩
    simp [AspPerm.rev_map]

noncomputable def link_equiv_dprod :
  {L : Link | L.τ = τ } ≃ {⟨α, β⟩ : AspPerm × AspPerm | α ⋆ β = τ } where
  toFun L := ⟨⟨L.val.α, L.val.β⟩, by simp; rw [L.val.dprod, L.prop]⟩
  invFun x := ⟨Link_of_dprod h_321a x.property, by
    rcases x with ⟨⟨α, β⟩, h_dprod⟩
    change α ⋆ β = τ at h_dprod
    apply AspPerm.eq_of_inv_set_eq_of_chi_eq
    · change inv_set ((tfas_of_perm h_321a).toAspPerm (α.χ + β.χ)) = inv_set τ
      simpa [Link.τ, Link.chi, Link_of_dprod] using
        (AspSet.of_AspPerm τ).invSet_of_toAspPerm (α.χ + β.χ)
    · change ((tfas_of_perm h_321a).toAspPerm (α.χ + β.χ)).χ = τ.χ
      have hχ' : ((tfas_of_perm h_321a).toAspPerm (α.χ + β.χ)).χ = α.χ + β.χ := by
        simpa using (AspSet.of_AspPerm τ).chi_of_toAspPerm (α.χ + β.χ)
      rw [hχ']
      rw [← h_dprod]
      exact (AspPerm.chi_star α β).symm⟩
  left_inv L := by
    have hdp : L.val.α ⋆ L.val.β = τ := by
      rw [L.val.dprod, L.prop]
    apply Subtype.ext
    apply Link.ext
    · dsimp [Link_of_dprod]
      have hsr : τ.sr L.val.α '' inv_set L.val.α = L.val.τ.sr L.val.α '' inv_set L.val.α := by
        simpa using congrArg (fun t => t.sr L.val.α '' inv_set L.val.α) L.prop.symm
      exact hsr.trans L.val.inv_set_α.symm
    · change inv_set L.val.β = L.val.B
      exact L.val.inv_set_β
    · change L.val.α.χ = L.val.χa
      exact L.val.chi_alpha
    · change L.val.β.χ = L.val.χb
      exact L.val.chi_beta
  right_inv x := by
    rcases x with ⟨⟨α, β⟩, h_dprod⟩
    change α ⋆ β = τ at h_dprod
    have hτL : (Link_of_dprod h_321a h_dprod).τ = τ := by
      apply AspPerm.eq_of_inv_set_eq_of_chi_eq
      · change inv_set ((tfas_of_perm h_321a).toAspPerm (α.χ + β.χ)) = inv_set τ
        simpa [Link.τ, Link.chi, Link_of_dprod] using
          (AspSet.of_AspPerm τ).invSet_of_toAspPerm (α.χ + β.χ)
      · change ((tfas_of_perm h_321a).toAspPerm (α.χ + β.χ)).χ = τ.χ
        have hχ' : ((tfas_of_perm h_321a).toAspPerm (α.χ + β.χ)).χ = α.χ + β.χ := by
          simpa using (AspSet.of_AspPerm τ).chi_of_toAspPerm (α.χ + β.χ)
        rw [hχ']
        rw [← h_dprod]
        exact (AspPerm.chi_star α β).symm
    apply Subtype.ext
    apply Prod.ext
    · dsimp
      let asps := (Link_of_dprod h_321a h_dprod).A_AspSet
      suffices asps.toAspPerm (-(Link_of_dprod h_321a h_dprod).χa) = α⁻¹ by
        calc
          (Link_of_dprod h_321a h_dprod).α
              = (asps.toAspPerm (-(Link_of_dprod h_321a h_dprod).χa))⁻¹ := by
                  rfl
          _ = (α⁻¹)⁻¹ := by rw [this]
          _ = α := by simp
      apply AspPerm.eq_of_inv_set_eq_of_chi_eq
      · rw [AspSet.invSet_of_toAspPerm]
        subst asps
        simpa [Link.A_AspSet, hτL] using
          rev_A_eq_inv_inv_of_Link_of_dprod (τ := τ) h_321a h_dprod
      · rw [AspSet.chi_of_toAspPerm]
        simp [Link_of_dprod, AspPerm.chi_dual]
    · dsimp
      let asps := (Link_of_dprod h_321a h_dprod).B_AspSet
      suffices asps.toAspPerm (Link_of_dprod h_321a h_dprod).χb = β by
        calc
          (Link_of_dprod h_321a h_dprod).β
              = asps.toAspPerm (Link_of_dprod h_321a h_dprod).χb := by
                  rfl
          _ = β := this
      apply AspPerm.eq_of_inv_set_eq_of_chi_eq
      · rw [AspSet.invSet_of_toAspPerm]
        subst asps
        change inv_set β.func = inv_set β.func
        rfl
      · rw [AspSet.chi_of_toAspPerm]
        simp [Link_of_dprod]

end Link

section Chains
variable {τ : AspPerm} (h_321a : is_321a τ)

noncomputable abbrev DProd (L : List AspPerm) : AspPerm :=
  List.foldr AspPerm.star AspPerm.id L

lemma DProd_cons (α : AspPerm) (Q : List AspPerm) :
  DProd (α :: Q) = α ⋆ DProd Q := by
  unfold DProd
  rw [List.foldr_cons]

def HeckeFactorization (τ : AspPerm) : Type :=
  {P : List AspPerm //
    DProd P = τ}

def boxUnion : List (Set (ℤ × ℤ) × ℤ) → Set (ℤ × ℤ)
  | [] => ∅
  | head :: tail => head.1 ∪ boxUnion tail

def chiSum : List (Set (ℤ × ℤ) × ℤ) → ℤ
  | [] => 0
  | head :: tail => head.2 + chiSum tail

def isChain : List (Set (ℤ × ℤ) × ℤ) → Prop
  | [] => True
  | ⟨A,_⟩ :: Q =>
      linked A (boxUnion Q)
      ∧ isChain Q

/-- Chain matching a given permutation τ in box union and shift. -/
def PChain (τ : AspPerm) : Type :=
  {C : List (Set (ℤ × ℤ) × ℤ) // isChain C ∧ boxUnion C = inv_set τ ∧ chiSum C = τ.χ}

noncomputable def LSet_of_LPerm : List AspPerm → List (Set (ℤ × ℤ) × ℤ)
  | [] => []
  | α :: L =>
    ((DProd (α :: L)).sr α '' (inv_set α), α.χ) :: LSet_of_LPerm L

lemma LSet_cons (α : AspPerm) (L : List AspPerm) :
    LSet_of_LPerm (α :: L) =
      ((DProd (α :: L)).sr α '' inv_set α, α.χ) :: LSet_of_LPerm L := by
  rfl

include h_321a

lemma LSet_chiSum (A : HeckeFactorization τ) :
  chiSum (LSet_of_LPerm A.val) = τ.χ := by
  rcases A with ⟨AL, dprodA⟩
  induction AL generalizing τ with
  | nil =>
      simp [LSet_of_LPerm, chiSum, ← dprodA]
  | cons α L ih =>
      let β := DProd L
      have h_L : β ≤L τ := by
        rw [← dprodA, DProd_cons]
        exact Submodular.lel_of_dprod α β
      have h_321a_β : is_321a β := is_321a_of_lel h_321a h_L
      have ih' := ih h_321a_β (by rfl)
      have τ_eq : α ⋆ β = τ := by
        rw [← dprodA, ← DProd_cons]
      have h_χ : τ.χ = α.χ + β.χ := by
        rw [← dprodA]
        exact (AspPerm.chi_star α β)
      rw [LSet_cons, chiSum, ih']
      linarith

lemma LSet_boxUnion (A : HeckeFactorization τ) :
  boxUnion (LSet_of_LPerm A.val) = inv_set τ := by
  rcases A with ⟨AL, dprodA⟩
  induction AL generalizing τ with
  | nil =>
      simp [LSet_of_LPerm, boxUnion, ← dprodA]
  | cons α L ih =>
      let β := DProd L
      have h_L : β ≤L τ := by
        rw [← dprodA, DProd_cons]
        exact Submodular.lel_of_dprod α β
      have h_R : α ≤R τ := by
        rw [← dprodA, DProd_cons]
        exact Submodular.ler_of_dprod α β
      have h_321a_β : is_321a β := is_321a_of_lel h_321a h_L
      have ih' := ih h_321a_β (by rfl)
      have τ_eq : α ⋆ β = τ := by
        rw [← dprodA, ← DProd_cons]
      have h_R : α ≤R τ := by
        rw [← dprodA]
        exact Submodular.ler_of_dprod α β
      have h_χ : τ.χ = α.χ + β.χ := by
        rw [← dprodA]
        exact (AspPerm.chi_star α β)
      rw [LSet_cons, boxUnion, ih']
      have := ((ASP321a.dprod_eq_iff h_321a).mp τ_eq.symm).2.1.symm
      convert this

lemma LSet_isChain (A : HeckeFactorization τ) :
  isChain (LSet_of_LPerm A.val) := by
  rcases A with ⟨AL, dprodA⟩
  induction AL generalizing τ with
  | nil =>
      simp [LSet_of_LPerm, isChain]
  | cons α L ih =>
      let β := DProd L
      have h_L : β ≤L τ := by
        rw [← dprodA, DProd_cons]
        exact Submodular.lel_of_dprod α β
      have h_R : α ≤R τ := by
        rw [← dprodA, DProd_cons]
        exact Submodular.ler_of_dprod α β
      have h_321a_β : is_321a β := is_321a_of_lel h_321a h_L
      have ih' := ih h_321a_β (by rfl)
      have τ_eq : α ⋆ β = τ := by
        rw [← dprodA, ← DProd_cons]
      rw [LSet_cons]
      constructor
      · rw [LSet_boxUnion h_321a_β ⟨L, rfl⟩]
        unfold linked
        rw [dprodA]
        intro p hp q hq hpq
        refine ((ASP321a.dprod_eq_iff h_321a).mp τ_eq.symm).2.2 p ?_ q ?_ hpq
        · suffices p ∈ inv_set β by
            exact ⟨hp, this⟩
          exact (inv_of_lel_iff (τ := τ) (β := β) h_321a h_L hq hpq).mpr
            ((AspPerm.sr_subset τ α h_R) hp)
        · suffices q ∈ τ.sr α '' inv_set α by
            exact ⟨this, hq⟩
          exact (sr_inv_of_ler_iff (τ := τ) h_321a h_R hp hpq).mpr (h_L hq)
      · exact ih'

noncomputable def PChain_of_HF (A : HeckeFactorization τ) : PChain τ :=
  ⟨LSet_of_LPerm A.val, LSet_isChain h_321a A, LSet_boxUnion h_321a A, LSet_chiSum h_321a A⟩

omit h_321a in
noncomputable def LPerm_of_Chain :
  (C : List (Set (ℤ × ℤ) × ℤ)) → isChain C → set_321a_prop (boxUnion C) → List AspPerm
  | [], _, _ => []
  | ⟨A, χ⟩ :: Q, hC, htfas =>
    let L := link_of_sets hC.1 htfas χ (chiSum Q)
    L.α :: LPerm_of_Chain Q hC.2 (by
      simpa [L] using L.B_set_321a_prop)

omit h_321a in
theorem DProd_LPerm_of_Chain :
    (C : List (Set (ℤ × ℤ) × ℤ)) → (hC : isChain C) →
      (htfas : set_321a_prop (boxUnion C)) →
        DProd (LPerm_of_Chain C hC htfas) =
          ((⟨boxUnion C, htfas.asp⟩ : AspSet).toAspPerm (chiSum C))
  | [], _, htfas => by
      let asps : AspSet := ⟨∅, htfas.asp⟩
      apply AspPerm.eq_of_inv_set_eq_of_chi_eq
      · simpa [asps, LPerm_of_Chain, DProd, boxUnion] using (asps.invSet_of_toAspPerm 0).symm
      · simpa [asps, LPerm_of_Chain, DProd, chiSum] using (asps.chi_of_toAspPerm 0).symm
  | ⟨A, χ⟩ :: Q, hC, htfas => by
      let L := link_of_sets hC.1 htfas χ (chiSum Q)
      have htfasQ : set_321a_prop (boxUnion Q) := by
        simpa [L] using L.B_set_321a_prop
      have ih := DProd_LPerm_of_Chain Q hC.2 htfasQ
      rw [LPerm_of_Chain, DProd_cons, ih]
      simpa [L] using L.dprod

noncomputable def HF_of_PChain (C : PChain τ) : HeckeFactorization τ := by
  have tfas : set_321a_prop (boxUnion C.val) := by
    simp only [C.prop.2]
    exact (is_321a_iff_set_321a_prop τ.func τ.bijective).mp h_321a
  refine ⟨LPerm_of_Chain C.val C.prop.1 tfas, ?_⟩
  let asps : AspSet := ⟨boxUnion C.val, tfas.asp⟩
  have h_asps : asps.toAspPerm (chiSum C.val) = τ := by
    apply AspPerm.eq_of_inv_set_eq_of_chi_eq
    · simpa [asps, C.prop.2.1] using (asps.invSet_of_toAspPerm (chiSum C.val))
    · simpa [asps, C.prop.2.2] using (asps.chi_of_toAspPerm (chiSum C.val))
  exact (DProd_LPerm_of_Chain C.val C.prop.1 tfas).trans h_asps

omit h_321a in
lemma LSet_of_LPerm_of_Chain :
  ∀ (C : List (Set (ℤ × ℤ) × ℤ)) (hC : isChain C) (htfas : set_321a_prop (boxUnion C)),
    LSet_of_LPerm (LPerm_of_Chain C hC htfas) = C
  | [], _, _ => by
      simp [LPerm_of_Chain, LSet_of_LPerm]
  | ⟨A, χ⟩ :: Q, hC, htfas => by
      let L := link_of_sets hC.1 htfas χ (chiSum Q)
      have htfasQ : set_321a_prop (boxUnion Q) := by
        simpa [L] using L.B_set_321a_prop
      have ih := LSet_of_LPerm_of_Chain Q hC.2 htfasQ
      have hβ : DProd (LPerm_of_Chain Q hC.2 htfasQ) = L.β := by
        simpa [L] using DProd_LPerm_of_Chain Q hC.2 htfasQ
      have hτ : DProd (L.α :: LPerm_of_Chain Q hC.2 htfasQ) = L.τ := by
        simpa [DProd_cons, hβ] using L.dprod
      have hA : (DProd (L.α :: LPerm_of_Chain Q hC.2 htfasQ)).sr L.α '' inv_set L.α = A := by
        have hsr :
            (DProd (L.α :: LPerm_of_Chain Q hC.2 htfasQ)).sr L.α '' inv_set L.α
              = L.τ.sr L.α '' inv_set L.α := by
          simpa using congrArg (fun t => t.sr L.α '' inv_set L.α) hτ
        calc
          (DProd (L.α :: LPerm_of_Chain Q hC.2 htfasQ)).sr L.α '' inv_set L.α
              = L.τ.sr L.α '' inv_set L.α := hsr
          _ = L.A := L.inv_set_α.symm
          _ = A := by rfl
      rw [LPerm_of_Chain, LSet_of_LPerm]
      simp [ih]
      constructor
      · exact hA
      · rfl

lemma PChain_of_HF_of_PChain (C : PChain τ) :
  PChain_of_HF h_321a (HF_of_PChain h_321a C) = C := by
  have tfas : set_321a_prop (boxUnion C.val) := by
    simp only [C.prop.2]
    exact (is_321a_iff_set_321a_prop τ.func τ.bijective).mp h_321a
  apply Subtype.ext
  simpa [PChain_of_HF, HF_of_PChain] using
    (LSet_of_LPerm_of_Chain C.val C.prop.1 tfas)

lemma HF_of_PChain_of_HF (A : HeckeFactorization τ) :
  HF_of_PChain h_321a (PChain_of_HF h_321a A) = A := by
  rcases A with ⟨AL, dprodA⟩
  induction AL generalizing τ with
  | nil =>
      apply Subtype.ext
      rfl
  | cons α T ih =>
      let β := DProd T
      have h_L : β ≤L τ := by
        rw [← dprodA, DProd_cons]
        exact Submodular.lel_of_dprod α β
      have h_321a_β : is_321a β := is_321a_of_lel h_321a h_L
      have τ_eq : α ⋆ β = τ := by
        rw [← dprodA, DProd_cons]
      have ih' := ih h_321a_β (by rfl)
      apply Subtype.ext
      have htfas : set_321a_prop (boxUnion (LSet_of_LPerm (α :: T))) := by
        rw [LSet_boxUnion h_321a ⟨α :: T, dprodA⟩]
        exact (is_321a_iff_set_321a_prop τ.func τ.bijective).mp h_321a
      change
        LPerm_of_Chain (LSet_of_LPerm (α :: T)) (LSet_isChain h_321a ⟨α :: T, dprodA⟩) htfas
          = α :: T
      simp only [LSet_cons, LPerm_of_Chain]
      let Lnk : Link := link_of_sets
        (A := (DProd (α :: T)).sr α '' inv_set α)
        (B := boxUnion (LSet_of_LPerm T))
        (LSet_isChain h_321a ⟨α :: T, dprodA⟩).1
        htfas α.χ (chiSum (LSet_of_LPerm T))
      have htfasT :
          set_321a_prop (boxUnion (LSet_of_LPerm T)) := by
        simpa [Lnk] using Lnk.B_set_321a_prop
      have hTail :
          LPerm_of_Chain (LSet_of_LPerm T)
            (LSet_isChain h_321a ⟨α :: T, dprodA⟩).2
            htfasT = T := by
        simpa [PChain_of_HF, HF_of_PChain] using congrArg Subtype.val ih'
      have hLink : Lnk = Link_of_dprod h_321a τ_eq := by
        have hA : Lnk.A = (Link_of_dprod h_321a τ_eq).A := by
          change (DProd (α :: T)).sr α '' inv_set α = τ.sr α '' inv_set α
          simp [dprodA]
        have hB : Lnk.B = (Link_of_dprod h_321a τ_eq).B := by
          change boxUnion (LSet_of_LPerm T) = inv_set β
          simpa [Lnk, Link_of_dprod] using (LSet_boxUnion h_321a_β ⟨T, rfl⟩)
        have hχa : Lnk.χa = (Link_of_dprod h_321a τ_eq).χa := by
          rfl
        have hχb : Lnk.χb = (Link_of_dprod h_321a τ_eq).χb := by
          change chiSum (LSet_of_LPerm T) = β.χ
          simpa [Lnk, Link_of_dprod] using (LSet_chiSum h_321a_β ⟨T, rfl⟩)
        exact Link.ext hA hB hχa hχb
      let e := link_equiv_dprod (τ := τ) h_321a
      let x : {⟨α', β'⟩ : AspPerm × AspPerm | α' ⋆ β' = τ } := ⟨⟨α, β⟩, τ_eq⟩
      have hα₀ : (Link_of_dprod h_321a τ_eq).α = α := by
        simpa [e, x] using congrArg Prod.fst (congrArg Subtype.val (e.right_inv x))
      have hα : Lnk.α = α := by
        rw [hLink]
        exact hα₀
      calc
        Lnk.α :: LPerm_of_Chain (LSet_of_LPerm T)
            (LSet_isChain h_321a ⟨α :: T, dprodA⟩).2 htfasT
          = α :: LPerm_of_Chain (LSet_of_LPerm T)
              (LSet_isChain h_321a ⟨α :: T, dprodA⟩).2 htfasT := by
                simpa using congrArg (fun γ => γ :: LPerm_of_Chain (LSet_of_LPerm T)
                  (LSet_isChain h_321a ⟨α :: T, dprodA⟩).2 htfasT) hα
        _ = α :: T := by simp [hTail]

noncomputable def HF_equiv_PChain :
  HeckeFactorization τ ≃ PChain τ
  where
  toFun := PChain_of_HF h_321a
  invFun := HF_of_PChain h_321a
  left_inv A := by
    exact HF_of_PChain_of_HF h_321a A
  right_inv C := by
    exact PChain_of_HF_of_PChain h_321a C

end Chains

section SetValuedTableaux

/-- A set-valued tableau on `inv_set τ` with symbols `1, ..., n`, encoded as
`Fin n` labels. The order convention is chosen to match `IsLayering`: if
`p ≼ q` and `p ≠ q`, then every label in `q` is at most every label in `p`. -/
structure SetValuedTableau_prop {τ : AspPerm} {n : ℕ}
    (T : ↥(inv_set τ) → Finset (Fin n)) : Prop where
  nonempty : ∀ p, (T p).Nonempty
  weak :
    ∀ {p q : ↥(inv_set τ)} {i j : Fin n},
      i ∈ T p → j ∈ T q → p.val ≼ q.val → p ≠ q → j ≤ i

/-- A set-valued tableau on `inv_set τ` with symbols `1, ..., n`. -/
def SetValuedTableau (τ : AspPerm) (n : ℕ) : Type :=
  {T : ↥(inv_set τ) → Finset (Fin n) // SetValuedTableau_prop (τ := τ) T}

/-- A length-`n` chain of box sets, where the `i`th set records the boxes
carrying symbol `i + 1`. Earlier labels are separated from later labels in the
same way as in `IsLayering`. -/
structure LabelChain_prop {τ : AspPerm} {n : ℕ}
    (C : Fin n → Set (ℤ × ℤ)) : Prop where
  cover : ∀ p, p ∈ inv_set τ ↔ ∃ i, p ∈ C i
  sep :
    ∀ {i j : Fin n}, i < j → ∀ p ∈ C i, ∀ q ∈ C j, p ≼ q → p = q

/-- A fixed-length chain of subsets of `inv_set τ`, indexed by the symbols
`1, ..., n`. -/
def LabelChain (τ : AspPerm) (n : ℕ) : Type :=
  {C : Fin n → Set (ℤ × ℤ) // LabelChain_prop (τ := τ) C}

variable {τ : AspPerm} {n : ℕ}

/-- Convert a tableau to the corresponding family of label sets. -/
def labelChainOfTableau (T : SetValuedTableau τ n) : LabelChain τ n := by
  refine ⟨fun i p => ∃ hp : p ∈ inv_set τ, i ∈ T.1 ⟨p, hp⟩, ?_⟩
  refine ⟨?_, ?_⟩
  · intro p
    constructor
    · intro hp
      rcases T.2.nonempty ⟨p, hp⟩ with ⟨i, hi⟩
      exact ⟨i, hp, hi⟩
    · rintro ⟨i, hp⟩
      exact hp.1
  · intro i j hij p hp q hq hpq
    by_cases hEq : p = q
    · exact hEq
    · rcases hp with ⟨hpτ, hip⟩
      rcases hq with ⟨hqτ, hjq⟩
      have hneq : (⟨p, hpτ⟩ : ↥(inv_set τ)) ≠ ⟨q, hqτ⟩ := by
        intro h
        apply hEq
        exact congrArg Subtype.val h
      exfalso
      exact (not_le_of_gt hij) (T.2.weak hip hjq hpq hneq)

/-- Convert a fixed-length chain of label sets to the corresponding tableau. -/
noncomputable def tableauOfLabelChain (C : LabelChain τ n) :
    SetValuedTableau τ n := by
  classical
  refine ⟨fun p => Finset.univ.filter fun i => p.1 ∈ C.1 i, ?_⟩
  refine ⟨?_, ?_⟩
  · intro p
    rcases (C.2.cover p.1).mp p.2 with ⟨i, hi⟩
    exact ⟨i, by simp [hi]⟩
  · intro p q i j hi hj hpq hneq
    have hpC : p.1 ∈ C.1 i := by simpa using hi
    have hqC : q.1 ∈ C.1 j := by simpa using hj
    by_cases hlt : i < j
    · have hpq_eq : p.1 = q.1 := C.2.sep hlt p.1 hpC q.1 hqC hpq
      exfalso
      apply hneq
      apply Subtype.ext
      exact hpq_eq
    · exact le_of_not_gt hlt

lemma mem_labelChainOfTableau_iff (T : SetValuedTableau τ n)
    (p : ↥(inv_set τ)) (i : Fin n) :
    p.1 ∈ (labelChainOfTableau T).1 i ↔ i ∈ T.1 p := by
  constructor
  · rintro ⟨hp, hi⟩
    have hp_eq : (⟨p.1, hp⟩ : ↥(inv_set τ)) = p := by
      apply Subtype.ext
      rfl
    simpa [hp_eq] using hi
  · intro hi
    exact ⟨p.2, hi⟩

lemma mem_labelChainOfTableau_tableauOfLabelChain_iff (C : LabelChain τ n)
    (p : ℤ × ℤ) (i : Fin n) :
    p ∈ (labelChainOfTableau (tableauOfLabelChain C)).1 i ↔ p ∈ C.1 i := by
  constructor
  · rintro ⟨hp, hi⟩
    simpa [tableauOfLabelChain] using hi
  · intro hp
    have hpτ : p ∈ inv_set τ := (C.2.cover p).mpr ⟨i, hp⟩
    exact ⟨hpτ, by simp [tableauOfLabelChain, hp]⟩

/-- The tableau reconstructed from the label-chain of `T` is `T` itself. -/
lemma tableauOfLabelChain_labelChainOfTableau (T : SetValuedTableau τ n) :
    tableauOfLabelChain (labelChainOfTableau T) = T := by
  exact Subtype.ext (by
    funext p
    apply Finset.ext
    intro i
    calc
      i ∈ (tableauOfLabelChain (labelChainOfTableau T)).1 p
        ↔ p.1 ∈ (labelChainOfTableau T).1 i := by
            simp [tableauOfLabelChain]
      _ ↔ i ∈ T.1 p := mem_labelChainOfTableau_iff T p i)

/-- The label-chain reconstructed from the tableau of `C` is `C` itself. -/
lemma labelChainOfTableau_tableauOfLabelChain (C : LabelChain τ n) :
    labelChainOfTableau (tableauOfLabelChain C) = C := by
  exact Subtype.ext (by
    funext i
    ext p
    exact mem_labelChainOfTableau_tableauOfLabelChain_iff C p i)

/-- Fixed-length label-chains and set-valued tableaux are equivalent. -/
noncomputable def setValuedTableauEquivLabelChain (τ : AspPerm) (n : ℕ) :
    SetValuedTableau τ n ≃ LabelChain τ n where
  toFun := labelChainOfTableau
  invFun := tableauOfLabelChain
  left_inv := tableauOfLabelChain_labelChainOfTableau
  right_inv := labelChainOfTableau_tableauOfLabelChain

end SetValuedTableaux
end ASP321a
