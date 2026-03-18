import Demazure.InvSet
import Demazure.Submodular

def is_321a (τ : ℤ → ℤ) : Prop :=
  ∀ (i j k : ℤ), i < j → j < k → τ i < τ j ∨ τ j < τ k

namespace ASP321a

structure set_321a_prop (I : Set (ℤ × ℤ)) where
  asp : AspSet_prop I
  tfree : ∀ u v w : ℤ, ⟨u,v⟩ ∉ I ∨ ⟨v,w⟩ ∉ I

structure set_321a : Type extends AspSet where
  prop_321a : set_321a_prop I

theorem asp_of_321a (τ : ℤ → ℤ) (h_bij : Function.Bijective τ) (h_321a : is_321a τ) : is_asp τ := by
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

lemma tfree_of_321a (τ : ℤ → ℤ) (h_321a : is_321a τ) :
  ∀ u v w : ℤ, ⟨u,v⟩ ∉ inv_set τ ∨ ⟨v,w⟩ ∉ inv_set τ := by
  intro u v w
  by_contra! h
  obtain ⟨uv_inv, vw_inv⟩ := h
  specialize h_321a u v w uv_inv.1 vw_inv.1
  have : τ u < τ v ∨ τ v < τ w := h_321a
  contrapose! this
  exact ⟨le_of_lt uv_inv.2, le_of_lt vw_inv.2⟩

theorem criterion_321a (τ : ℤ → ℤ) (hperm : Function.Bijective τ) : is_321a τ ↔
  set_321a_prop (inv_set τ) := by
  constructor
  -- Forward direction
  · intro h321a
    have h_asp := asp_of_321a τ hperm h321a
    let τ_asp : AspPerm := ⟨τ, hperm, h_asp⟩
    constructor
    · show AspSet_prop (inv_set τ)
      exact AspSet.AspSet_InvSet_of_AspPerm τ_asp
    · exact tfree_of_321a τ h321a
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

noncomputable def Perm321a_equiv_BijectiveFunc321a :
  {τ : AspPerm | is_321a τ} ≃ {τ : ℤ → ℤ // Function.Bijective τ ∧ is_321a τ} where
  toFun τ := ⟨τ.val.func, ⟨τ.val.bijective, τ.prop⟩⟩
  invFun := fun ⟨τ, hτ⟩ =>
    ⟨⟨τ, hτ.1, asp_of_321a τ hτ.1 hτ.2⟩, hτ.2⟩
  left_inv := by
    intro τ
    apply Subtype.ext
    apply AspPerm.ext.mpr
    rfl
  right_inv := by
    intro τ
    apply Subtype.ext
    rfl

noncomputable def Perm321a_equiv_Set321a :
  {τ : AspPerm | is_321a τ} ≃ set_321a × ℤ where
  toFun τ :=
    ⟨⟨AspSet.of_AspPerm τ, (criterion_321a τ τ.val.bijective).mp τ.prop⟩, τ.val.χ⟩
  invFun := fun ⟨I, χ⟩ =>
    ⟨I.toAspPerm χ,
      (criterion_321a (I.recon χ) (I.toAspPerm χ).bijective).mpr
        { asp := by
            show AspSet_prop (inv_set (I.recon χ))
            rw [I.invSet_func χ]
            exact I.prop
          tfree := by
            simpa [I.invSet_func χ] using I.prop_321a.tfree }⟩
  left_inv := by
    intro τ
    apply Subtype.ext
    refine AspPerm.unique_from_inv_and_χ _ _ ?_ ?_
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
        rw [set_321a.mk.injEq]
        apply SetLike.coe_injective
        exact toAspSet.invSet_of_toAspPerm χ
    · exact I.chi_of_toAspPerm χ



theorem inv_321a_char (I : Set (ℤ × ℤ)) :
  set_321a_prop I
  ↔ (∃ τ : (ℤ → ℤ), (is_321a τ ∧ Function.Bijective τ ∧ inv_set τ = I)) := by
  constructor
  · intro Ip
    let I_asp : AspSet := ⟨I, Ip.asp⟩
    let I_321a : set_321a := ⟨I_asp, Ip⟩
    let τ : AspPerm := I_321a.toAspPerm 0
    use τ.func
    constructor
    · rw [criterion_321a τ.func τ.bijective]
      have : inv_set τ.func = I := I_321a.invSet_func 0
      rwa [this]
    constructor
    · exact τ.bijective
    · exact I_321a.invSet_func 0
  · rintro ⟨τ, ⟨h_321a, h_bij, h_inv⟩⟩
    have := (criterion_321a τ h_bij).mp h_321a
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
  have := tfree_of_321a τ h_321a u n v
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
  have := tfree_of_321a τ h_321a u v x
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
  have := tfree_of_321a τ h_321a x u v
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
      have := tfree_of_321a τ h_321a u x v
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

-- structure s_witness (τ : AspPerm) (a b : ℤ) where
--   v : ℤ
--   s_val : τ.s a b = τ.s (τ v) b + 1
--   mem_se : v ∈ southeast_set τ a b


-- noncomputable def find_s_witness {τ : AspPerm} {a b : ℤ}
--   (hab : τ.s a b ≥ 1) : s_witness τ a b := by
--   have se_nonempty : (τ.se a b).Nonempty := by
--     dsimp [AspPerm.s] at hab
--     have : (τ.se a b).card ≠ 0 := by linarith
--     exact Finset.card_ne_zero.mp this
--   let S := Finset.image τ (τ.se a b)
--   have : (Finset.image τ (τ.se a b)).Nonempty := by
--     simp [se_nonempty]
--   let y := Finset.max' (Finset.image τ (τ.se a b)) this
--   let v := τ⁻¹ y
--   have y_mem : y ∈ τ '' southeast_set τ a b := by
--     -- Start with the Finset version
--     have h : y ∈ Finset.image τ (τ.se a b) := Finset.max'_mem (Finset.image τ (τ.se a b)) this
--     simp [Finset.mem_image] at h
--     exact h
--   have v_mem : v ∈ southeast_set τ a b := by
--     rcases y_mem with ⟨n, n_mem, y_eq⟩
--     subst v; rw [← y_eq]; simp [n_mem]
--   use v
--   have le_τv : ∀ n ∈ southeast_set τ a b, τ n ≤ τ v := by
--     intro n n_mem
--     subst v; simp
--     refine Finset.le_max' (Finset.image τ (τ.se a b)) (τ n) ?_
--     rw [Finset.mem_image]
--     use n
--     simpa [AspPerm.mem_se] using n_mem
--   · suffices τ.s a b = τ.s (τ v + 1) b by
--       have h : τ.s (τ.func v + 1) b = τ.s (τ.func v) b + 1
--         := (τ.a_step_one_iff' v b).mpr v_mem.1
--       rw [this, h]
--     unfold AspPerm.s
--     suffices (τ.se a b) = (τ.se (τ.func v + 1) b) by rw [this]
--     ext n; simp only [AspPerm.mem_se]
--     have τv_lt_a : τ v < a := v_mem.2
--     constructor <;> (intro ⟨n_ge_b, τn_lt⟩; use n_ge_b)
--     · have := le_τv n ⟨n_ge_b, τn_lt⟩
--       exact Int.le_iff_lt_add_one.mp this
--     · have := Int.le_iff_lt_add_one.mpr τn_lt
--       exact lt_of_le_of_lt this τv_lt_a

-- structure s'_witness (τ : AspPerm) (a b : ℤ) where
--   u : ℤ
--   s'_val : τ.s' b a = τ.s' b (τ u)
--   mem_nw : u ∈ northwest_set τ a b

-- noncomputable def find_s'_witness {τ : AspPerm} {a b : ℤ} (hab : τ.s' b a ≥ 1) :
--   s'_witness τ a b := by
--   have nw_nonempty : (τ.nw a b).Nonempty := by
--     dsimp [AspPerm.s'] at hab
--     have : (τ.nw a b).card ≠ 0 := by linarith
--     exact Finset.card_ne_zero.mp this
--   have img_nonempty : (Finset.image τ (τ.nw a b)).Nonempty := by simp [nw_nonempty]
--   let y := Finset.min' (Finset.image τ (τ.nw a b)) img_nonempty
--   let u := τ⁻¹ y
--   have y_mem : y ∈ τ '' northwest_set τ a b := by
--     have h : y ∈ Finset.image τ (τ.nw a b) :=
--       Finset.min'_mem (Finset.image τ (τ.nw a b)) img_nonempty
--     simp [Finset.mem_image] at h
--     exact h
--   have u_mem : u ∈ northwest_set τ a b := by
--     rcases y_mem with ⟨n, n_mem, y_eq⟩
--     subst u; rw [← y_eq]; simp [n_mem]
--   have ge_τu : ∀ n ∈ northwest_set τ a b, τ u ≤ τ n := by
--     intro n n_mem
--     subst u; simp
--     apply Finset.min'_le
--     rw [Finset.mem_image]
--     use n
--     simpa [AspPerm.mem_nw] using n_mem
--   use u
--   · -- s'_val : τ.s' b a = τ.s' b (τ u)
--     unfold AspPerm.s'
--     suffices τ.nw a b = τ.nw (τ.func u) b by rw [this]
--     ext n; simp only [AspPerm.mem_nw]
--     constructor
--     · intro ⟨n_lt_b, τn_ge_a⟩
--       exact ⟨n_lt_b, ge_τu n ⟨n_lt_b, τn_ge_a⟩⟩
--     · intro ⟨n_lt_b, τn_ge_τu⟩
--       exact ⟨n_lt_b, le_trans u_mem.2 τn_ge_τu⟩

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
        have := tfree_of_321a τ h_321a u n v
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
    have := tfree_of_321a τ h_321a u v x
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
  (τ (τ.v b m_pos) ≥ τ⁻¹.u a m'_pos) ∧ (τ.v b m_pos ≥ τ⁻¹ (τ⁻¹.u a m'_pos)) := by
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
  rw [criterion_321a τ τ.bijective] at h_321a
  rw [criterion_321a β β.bijective]
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
lemma set_321a_of_func (avset : set_321a) (χ : ℤ) : set_321a_prop (inv_set (avset.recon χ)) := by
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


-- This is roughly a repeat of the proof above. Can it be unified with it somehow?
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

-- Almost identical to the above, but with β.u and β.v instead of τ.u and τ.v.
-- Can these be unified compactly?
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

    have h : (τ v, τ u) ∈ inv_set α⁻¹.func ↔ (τ⁻¹.s u a + 1, τ.s a v) ∈ α⁻¹.ramp a := by
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

lemma union_sufficient (a b : ℤ) (h_union : inv_set τ ⊆ ((τ.sr α) '' (inv_set α)) ∪ inv_set β) :
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
  -- [TODO] consider packaging all the above into a structure for use elsewhere

  have : ⟨u, v⟩ ∈ inv_set β ↔ ⟨m, n⟩ ∈ β.ramp b :=
    lel_ramp h_321a h_L b m_ge_1 n_ge_1
  rw [← this]

  let u' := τ⁻¹.u a m'_ge_1
  let v' := τ⁻¹.v a n'_ge_1

  -- [TODO] bubble this out as a separate helper, and also the one below
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
  suffices ⟨u, v⟩ ∈ (τ.sr α) '' (inv_set α) ∨ ⟨u, v⟩ ∈ inv_set β  by
    rwa [← lamp_equiv, ← u'_eq, ← v'_eq, ← τ.sr_crit α u v, Or.comm]

  have uv_inv : ⟨u, v⟩ ∈ inv_set τ := ⟨lt_of_lt_of_le u_lt_b v_ge_b, lt_of_lt_of_le τv_lt_a τu_ge_a⟩
  exact h_union uv_inv

lemma excess_of_not_isolated {u v₁ v₂ : ℤ} (v₁_lt_v₂ : v₁ < v₂)
  (uv₁_inv : ⟨u, v₁⟩ ∈ (τ.sr α) '' (inv_set α)) (uv₂_inv : ⟨u, v₂⟩ ∈ inv_set β) :
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
      have := tfree_of_321a τ h_321a u v₁ x
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

  -- Can probably remove this after getting the rest hashed out
  let n' := N + 1 - n
  change ⟨1, n⟩ ∈ β.ramp b ∨ ⟨1, n'⟩ ∈ α.lamp a

  have u_lt_v₁ : u < v₁ := by linarith [uv₁_inv_τ.1]
  have v₁_le_v₂ : v₁ ≤ v₂ := by linarith
  -- have τv₂_ge_a : τ v₂ ≥ a := by sorry
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
  ∃ (I J : (ℤ × ℤ)), {I, J} ⊆ (τ.sr α ''  (inv_set α)) ∩ (inv_set β) ∧ I ≼ J ∧ I ≠ J
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
  have duality : is_snk τ⁻¹ v' → is_snk τ⁻¹ (τ u) → (τ⁻¹ v' ≥ u) ∧ (v' ≥ τ u) := by
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
  ∃ (I J : (ℤ × ℤ)), {I, J} ⊆ (τ.sr α ''  (inv_set α)) ∩ (inv_set β) ∧ I ≼ J ∧ I ≠ J
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
    -- [TODO] Consider extracting this as a general ramp ⊆ ramp lemma for ≤L.
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
      convert (τ.mem_ramp_iff_s_geq b M N).mp mem_ramp_τ
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
        rw [τ.χ_dual]
        linarith [hMN, h_χ]
      simpa [hba] using (τ⁻¹.mem_ramp_iff_s_geq a N M).mp mem_ramp_τi
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
    ⟨M+1-m, N+1-n⟩ ∈ α.lamp a
    ∧ ((⟨m-1, n⟩ ∈ β.ramp b ∧ m ≥ 2) ∨ (⟨m, n-1⟩ ∈ β.ramp b ∧ n ≥ 2)) := by
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
      rw [τ.χ_dual, α.χ_dual, β.χ_dual]
      linarith [h_χ]
    have hβi : ⟨n, m-1⟩ ∈ β⁻¹.lamp b := (β.ramp_lamp_dual b (m-1) n).mp hβ
    have hαi : ⟨N+1-n, M+1-m⟩ ∈ α⁻¹.ramp a := by
      simpa [α⁻¹.ramp_lamp_dual a]
    have := not_isolated_of_domino (inv_is_321a h_321a) h_R leR b a  (N+1-n) n (M+1-m) (m-1)
      (by linarith [n_Icc.2]) n_Icc.1
      (by linarith [m_Icc.2]) (by linarith [m_ge_2]) (by linarith) (by simp; linarith) hβi hαi
    rcases this with ⟨⟨u₁, v₁⟩, ⟨u₂, v₂⟩, ⟨h_mem, h_nest⟩⟩
    have h1_mem : ⟨u₁, v₁⟩ ∈ ((τ⁻¹.sr β⁻¹) '' (inv_set β⁻¹.func)) ∩ (inv_set α⁻¹.func) :=
      h_mem (by simp : (u₁, v₁) ∈ ({(u₁, v₁), (u₂, v₂)} : Set (ℤ × ℤ)))
    have h2_mem : ⟨u₂, v₂⟩ ∈ ((τ⁻¹.sr β⁻¹) '' (inv_set β⁻¹.func)) ∩ (inv_set α⁻¹.func) :=
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

--- Main result

theorem dprod_ge_iff_union : τ ≤ α ⋆ β ↔ inv_set τ ⊆ (τ.sr α) '' (inv_set α) ∪ inv_set β := by
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
      repeat rw [AspPerm.χ_dual]
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
  -- rw [τ.eq_star_iff]
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
variable {τ : AspPerm}

structure Link (τ : AspPerm) where
  A : Set (ℤ × ℤ)
  B : Set (ℤ × ℤ)
  χa : ℤ
  χb : ℤ
  union_eq : A ∪ B = inv_set τ
  sep : ∀ p ∈ A, ∀ q ∈ B, p ≼ q → p = q
  shift : τ.χ = χa + χb

lemma Link.B_subset (L : Link τ) : L.B ⊆ inv_set τ := by
  rw [← L.union_eq]
  apply Set.subset_union_right

lemma Link.A_subset (L : Link τ) : L.A ⊆ inv_set τ := by
  rw [← L.union_eq]
  apply Set.subset_union_left

lemma Link.mem_A_of_mem_inv_not_mem_B (L : Link τ) {p : ℤ × ℤ}
  (hpτ : p ∈ inv_set τ) (hpB : p ∉ L.B) : p ∈ L.A := by
  rw [← L.union_eq] at hpτ
  rcases hpτ with (hpA | hpB')
  · exact hpA
  · exact (hpB hpB').elim

theorem Link.ext {L₁ L₂ : Link τ}
  (hA : L₁.A = L₂.A) (hB : L₁.B = L₂.B) (hχ : L₁.χa = L₂.χa) : L₁ = L₂ := by
  -- Note: I only include a χa hypothesis here, for convenience,
  -- but this is asymmetrical as a result.
  cases L₁
  cases L₂
  cases hA
  cases hB
  cases hχ
  simp
  omega

variable (h_321a : is_321a τ)
include h_321a

noncomputable def Link_of_dprod {α β : AspPerm}
  (dprod : α ⋆ β = τ) : Link τ where
  A := (τ.sr α) '' inv_set α
  B := inv_set β
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
  shift := by
    rw [← dprod]
    exact AspPerm.chi_star α β

lemma B_AspSet_prop_of_Link (L : Link τ) :
  AspSet_prop L.B where
  directed := by
    intro u v huv
    exact (L.B_subset huv).1
  closed := by
    intro u v w huv hvw
    exfalso
    apply L.B_subset at huv
    apply L.B_subset at hvw
    have := h_321a u v w huv.1 hvw.1
    absurd this; push_neg
    exact ⟨le_of_lt huv.2, le_of_lt hvw.2⟩
  coclosed := by
    intro u v w u_lt_v v_lt_w huv hvw
    by_contra! huw

    have := (AspSet.of_AspPerm τ).coclosed u v w u_lt_v v_lt_w
    have h : ⟨u, v⟩ ∈ inv_set τ ∨ ⟨v, w⟩ ∈ inv_set τ := by
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
    exact ((AspSet.of_AspPerm τ).finite_outdegree u).subset (by
      intro v hv
      exact L.B_subset hv)
  finite_indegree := by
    intro v
    exact ((AspSet.of_AspPerm τ).finite_indegree v).subset (by
      intro u hu
      exact L.B_subset hu)

def reverse_link (L : Link τ) : Link τ⁻¹ where
  A := τ.rev_map '' L.B
  B := τ.rev_map '' L.A
  χa := - L.χb
  χb := - L.χa
  union_eq := by
    ext ⟨u, v⟩
    constructor
    · intro h
      rcases h with (hB | hA)
      · rcases hB with ⟨⟨u', v'⟩, hu'v', hEq⟩
        simp [AspPerm.rev_map] at hEq
        rcases hEq with ⟨rfl, rfl⟩
        exact (τ.inv_set_inverse u' v').mp (L.B_subset hu'v')
      · rcases hA with ⟨⟨u', v'⟩, hu'v', hEq⟩
        simp [AspPerm.rev_map] at hEq
        rcases hEq with ⟨rfl, rfl⟩
        exact (τ.inv_set_inverse u' v').mp (L.A_subset hu'v')
    · intro h
      have h' : ⟨τ⁻¹ v, τ⁻¹ u⟩ ∈ inv_set τ := by
        have hτi : ⟨τ (τ⁻¹ u), τ (τ⁻¹ v)⟩ ∈ inv_set τ⁻¹.func := by
          simpa using h
        have := (τ.inv_set_inverse (τ⁻¹ v) (τ⁻¹ u)).mpr hτi
        simpa using this
      rw [← L.union_eq] at h'
      rcases h' with (hA | hB)
      · right
        refine ⟨⟨τ⁻¹ v, τ⁻¹ u⟩, hA, ?_⟩
        simp [AspPerm.rev_map]
      · left
        refine ⟨⟨τ⁻¹ v, τ⁻¹ u⟩, hB, ?_⟩
        simp [AspPerm.rev_map]
  sep := by
    intro p hp q hq hpq
    rcases hp with ⟨⟨u, v⟩, huv, rfl⟩
    rcases hq with ⟨⟨u', v'⟩, hu'v', rfl⟩
    simp [AspPerm.rev_map] at hpq
    have hpτi : ⟨τ v, τ u⟩ ∈ inv_set τ⁻¹.func := by
      exact (τ.inv_set_inverse u v).mp (L.B_subset huv)
    have hqτi : ⟨τ v', τ u'⟩ ∈ inv_set τ⁻¹.func := by
      exact (τ.inv_set_inverse u' v').mp (L.A_subset hu'v')
    have hqup : u ≤ u' := by
      have hu_snk : is_snk (τ⁻¹) (τ u) := snk_of_inv hpτi
      simpa using snk_le (inv_is_321a h_321a) hu_snk hpq.2
    have hvpv : v' ≤ v := by
      have hv_src : is_src (τ⁻¹) (τ v) := src_of_inv hpτi
      simpa using src_ge (inv_is_321a h_321a) hv_src hpq.1
    have hqp : ⟨u', v'⟩ ≼ ⟨u, v⟩ := by
      exact ⟨hqup, hvpv⟩
    have hEq : (u', v') = (u, v) := L.sep (u', v') hu'v' (u, v) huv hqp
    simpa [AspPerm.rev_map] using congrArg τ.rev_map hEq.symm
  shift := by
    rw [τ.χ_dual, L.shift]
    omega


lemma A_AspSet_prop_of_Link (L : Link τ) :
  AspSet_prop (τ.rev_map '' L.A) := by
  let L' := reverse_link h_321a L
  have h' := B_AspSet_prop_of_Link (inv_is_321a h_321a) L'
  convert h'

def A_AspSet_of_link (L : Link τ) : AspSet where
  I := τ.rev_map '' L.A
  prop := A_AspSet_prop_of_Link h_321a L

def B_AspSet_of_link (L : Link τ) : AspSet where
  I := L.B
  prop := B_AspSet_prop_of_Link h_321a L

@[simp] lemma invSet_B_AspSet_of_link (L : Link τ) :
  inv_set ((B_AspSet_of_link h_321a L).toAspPerm L.χb).func = L.B :=
  (B_AspSet_of_link h_321a L).invSet_of_toAspPerm L.χb

lemma A_eq_sr_of_A_AspSet_of_link (L : Link τ) :
  let α := ((A_AspSet_of_link h_321a L).toAspPerm (-L.χa))⁻¹
  L.A = τ.sr α '' inv_set α.func := by
  let α := ((A_AspSet_of_link h_321a L).toAspPerm (-L.χa))⁻¹
  have hAinv : inv_set α⁻¹.func = τ.rev_map '' L.A := by
    simpa [α] using (A_AspSet_of_link h_321a L).invSet_of_toAspPerm (-L.χa)
  ext ⟨u, v⟩
  constructor
  · intro huv
    apply (τ.sr_crit α u v).mpr
    rw [hAinv]
    exact ⟨⟨u, v⟩, huv, by simp [AspPerm.rev_map]⟩
  · intro huv
    have hrev : ⟨τ v, τ u⟩ ∈ τ.rev_map '' L.A := by
      rw [← hAinv]
      exact (τ.sr_crit α u v).mp huv
    rcases hrev with ⟨⟨u', v'⟩, hu'v', hEq⟩
    simp [AspPerm.rev_map] at hEq
    rcases hEq with ⟨hv, hu⟩
    apply τ.injective at hv
    apply τ.injective at hu
    simpa [hu, hv] using hu'v'

lemma rev_A_eq_inv_inv_of_Link_of_dprod {α β : AspPerm} (dprod : α ⋆ β = τ) :
  τ.rev_map '' (Link_of_dprod h_321a dprod).A = inv_set α⁻¹.func := by
  ext ⟨u, v⟩
  change ⟨u, v⟩ ∈ τ.rev_map '' (τ.sr α '' inv_set α.func) ↔ ⟨u, v⟩ ∈ inv_set α⁻¹.func
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

noncomputable def dprod_of_link (L : Link τ) : AspPerm × AspPerm :=
   ⟨((A_AspSet_of_link h_321a L).toAspPerm (-L.χa))⁻¹,
  (B_AspSet_of_link h_321a L).toAspPerm L.χb⟩


lemma dprod_of_link_spec (L : Link τ) :
  let α := (dprod_of_link h_321a L).1
  let β := (dprod_of_link h_321a L).2
  α ⋆ β = τ ∧ α.χ = L.χa ∧ β.χ = L.χb
  := by
  intro α β

  have h_χa : α.χ = L.χa := by
    have := (A_AspSet_of_link h_321a L).chi_of_toAspPerm (-L.χa)
    subst α
    unfold dprod_of_link
    rw [AspPerm.χ_dual]
    omega
  have h_χb : β.χ = L.χb := (B_AspSet_of_link h_321a L).chi_of_toAspPerm L.χb
  apply And.intro _ ⟨h_χa, h_χb⟩
  change α ⋆ β = τ
  apply Eq.symm
  apply (dprod_eq_iff (τ := τ) (α := α) (β := β) h_321a).mpr
  constructor
  · rw [h_χa, h_χb, ← L.shift]
  have hLB : L.B = inv_set β.func := by
    simp [β, dprod_of_link]
  have hLA : L.A = τ.sr α '' inv_set α.func := by
    simpa [α] using A_eq_sr_of_A_AspSet_of_link h_321a L
  constructor
  · rw [← L.union_eq]
    congr
  · intro p hp q hq hpq
    rw [← hLB] at hq
    rw [← hLA] at hp
    exact L.sep p hp.1 q hq.2 hpq

noncomputable def dprod_to_link :
  {⟨α, β⟩ : AspPerm × AspPerm | α ⋆ β = τ } → Link τ :=
  fun x => Link_of_dprod h_321a x.property

noncomputable def link_to_dprod :
  Link τ → { ⟨α, β⟩ : AspPerm × AspPerm |  α ⋆ β = τ } :=
  fun L => ⟨dprod_of_link h_321a L, (dprod_of_link_spec h_321a L).1⟩


theorem dprod_to_link_link_to_dprod :
  Function.LeftInverse (dprod_to_link h_321a) (link_to_dprod h_321a) := by
  intro L
  let α := ((A_AspSet_of_link h_321a L).toAspPerm (-L.χa))⁻¹
  let β := (B_AspSet_of_link h_321a L).toAspPerm L.χb
  have hLB : L.B = inv_set β.func := by
    simp [β]
  have hLA : L.A = τ.sr α '' inv_set α.func := by
    simpa [α] using A_eq_sr_of_A_AspSet_of_link h_321a L
  refine Link.ext ?_ ?_ ?_
  · unfold dprod_to_link link_to_dprod
    simpa [dprod_of_link, α, β] using hLA.symm
  · unfold dprod_to_link link_to_dprod
    change inv_set ((B_AspSet_of_link h_321a L).toAspPerm L.χb).func = L.B
    exact hLB.symm
  · dsimp [dprod_to_link, Link_of_dprod, link_to_dprod]
    exact (dprod_of_link_spec h_321a L).2.1

theorem link_to_dprod_dprod_to_link :
  Function.RightInverse (dprod_to_link h_321a) (link_to_dprod h_321a) := by
  intro x
  let α := x.1.1
  let β := x.1.2
  have h_dprod : α ⋆ β = τ := x.2
  let L := dprod_to_link h_321a ⟨⟨α, β⟩, h_dprod⟩
  apply Subtype.ext
  suffices (link_to_dprod h_321a L).1 = ⟨α, β⟩ by
    simpa using this
  dsimp [link_to_dprod]
  apply Prod.ext
  · dsimp [dprod_of_link]
    let asps := (A_AspSet_of_link h_321a L)
    suffices asps.toAspPerm (-L.χa) = α⁻¹ by
      rw [this]
      simp
    apply AspPerm.unique_from_inv_and_χ
    · rw [AspSet.invSet_of_toAspPerm]
      subst asps
      dsimp [A_AspSet_of_link]
      subst L
      simpa [dprod_to_link] using
        rev_A_eq_inv_inv_of_Link_of_dprod (τ := τ) h_321a h_dprod
    · rw [AspSet.chi_of_toAspPerm]
      subst asps L
      dsimp [dprod_to_link, Link_of_dprod]
      rw [α.χ_dual]
  · dsimp [dprod_of_link]
    let asps := (B_AspSet_of_link h_321a L)
    suffices asps.toAspPerm L.χb = β by
      rw [this]
    apply AspPerm.unique_from_inv_and_χ
    · rw [AspSet.invSet_of_toAspPerm]
      subst asps
      dsimp [B_AspSet_of_link]
      suffices L.B = inv_set β.func by
        simpa using this
      subst L
      dsimp [dprod_to_link, Link_of_dprod]
    · rw [AspSet.chi_of_toAspPerm]
      subst asps L
      dsimp [dprod_to_link, Link_of_dprod]

theorem bijective_dprod_to_link :
  Function.Bijective (dprod_to_link h_321a) := by
  constructor
  · intro x y hxy
    have := congrArg (link_to_dprod h_321a ) hxy
    simpa [link_to_dprod_dprod_to_link h_321a x,
      link_to_dprod_dprod_to_link h_321a y] using this
  · intro L
    exact ⟨link_to_dprod h_321a L, dprod_to_link_link_to_dprod h_321a L⟩

theorem bijective_link_to_dprod :
  Function.Bijective (link_to_dprod h_321a) := by
  constructor
  · intro x y hxy
    have := congrArg (dprod_to_link h_321a) hxy
    simpa [dprod_to_link_link_to_dprod h_321a x,
      dprod_to_link_link_to_dprod h_321a y] using this
  · intro x
    exact ⟨dprod_to_link h_321a x, link_to_dprod_dprod_to_link h_321a x⟩


end Link

section Tableaux
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
  | ⟨A,χa⟩ :: Q =>
    ∃ τ : AspPerm, ∃ L : Link τ,
      L.A = A ∧ L.χa = χa
      ∧ L.B = boxUnion Q ∧ L.χb = chiSum Q
      ∧ isChain Q

def Chain (τ : AspPerm) : Type :=
  {C : List (Set (ℤ × ℤ) × ℤ) // isChain C ∧ boxUnion C = inv_set τ ∧ chiSum C = τ.χ}

def IsLayering : List (Set (ℤ × ℤ) × ℤ) → Prop
  | [] => True
  | head :: tail =>
      IsLayering tail ∧
      ∀ p ∈ head.1, ∀ q ∈ boxUnion tail, p ≼ q → p = q

def Layering : Type :=
  {A : List (Set (ℤ × ℤ) × ℤ) // IsLayering A}

def SVT_Layering (τ : AspPerm) : Type :=
  {L : List (Set (ℤ × ℤ) × ℤ) // IsLayering L ∧ boxUnion L = inv_set τ ∧ chiSum L = τ.χ}

noncomputable def LSet_of_LPerm : List AspPerm → List (Set (ℤ × ℤ) × ℤ)
  | [] => []
  | α :: L =>
    ((DProd (α :: L)).sr α '' (inv_set α), α.χ) :: LSet_of_LPerm L

include h_321a

lemma LSet_helper
  (A : HeckeFactorization τ) :
  IsLayering (LSet_of_LPerm A.val)
  ∧ boxUnion (LSet_of_LPerm A.val) = inv_set τ
  ∧ chiSum (LSet_of_LPerm A.val) = τ.χ
  := by
  rcases A with ⟨AL, dprodA⟩
  induction AL generalizing τ with
  | nil =>
    constructor
    · constructor
    · have : τ = AspPerm.id := by
        rw [← dprodA]
        simp
      dsimp [LSet_of_LPerm, boxUnion, chiSum]
      constructor
      · apply Eq.symm
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro ⟨u,v⟩ huv
        rw [this] at huv
        obtain ⟨u_lt_v, iduv⟩ := huv
        dsimp [AspPerm.id] at iduv
        omega
      · rw [this]
        simp
  | cons α L ih =>
    let β := DProd L
    have h_L : β ≤L τ := by
      rw [← dprodA, DProd_cons]
      exact Submodular.lel_of_dprod α β
    have h_321a_β : is_321a β := is_321a_of_lel h_321a h_L
    specialize ih h_321a_β (by rfl)
    obtain ⟨ih_layering, ih_union⟩ := ih
    have τ_eq : α ⋆ β = τ := by
      rw [← dprodA, ← DProd_cons]
    constructor
    · constructor
      · exact ih_layering
      · intro p hp q hq hpq
        rw [ih_union.1] at hq
        rw [dprodA] at hp
        exact (Link_of_dprod h_321a τ_eq).sep p hp q hq hpq
    · dsimp [boxUnion, LSet_of_LPerm]
      constructor
      · rw [ih_union.1, τ_eq]
        simpa [β] using (Link_of_dprod h_321a τ_eq).union_eq
      · dsimp [chiSum]
        rw [ih_union.2]
        rw [← τ_eq]
        exact (AspPerm.chi_star α β).symm

/-- `LSet_of_LPerm` applied to a Hecke factorization satisfies `isChain`.
This is the chain analogue of `LSet_helper`. Contributed by Codex -/
lemma chain_of_HF_helper (A : HeckeFactorization τ) :
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
      have h_321a_β : is_321a β := is_321a_of_lel h_321a h_L
      have ih' := ih h_321a_β (by rfl)
      have τ_eq : α ⋆ β = τ := by
        rw [← dprodA, ← DProd_cons]
      have h_tail_union : boxUnion (LSet_of_LPerm L) = inv_set β :=
        (LSet_helper h_321a_β ⟨L, rfl⟩).2.1
      have h_tail_chi : chiSum (LSet_of_LPerm L) = β.χ :=
        (LSet_helper h_321a_β ⟨L, rfl⟩).2.2
      -- The chain witness for the head layer is exactly the `Link` extracted
      -- from the Demazure product decomposition `α ⋆ β = τ`.
      refine ⟨τ, Link_of_dprod h_321a τ_eq, ?_, rfl, ?_, ?_, ih'⟩
      · have hτ : τ = α ⋆ DProd L := by
          rw [← dprodA, DProd_cons]
        simpa [β] using congrArg (fun σ => σ.sr α '' inv_set α) hτ
      · simpa [β] using h_tail_union.symm
      · simpa [β] using h_tail_chi.symm

/-- Convert a Hecke factorization to a chain by applying `LSet_of_LPerm` and
packaging the chain/union/shift facts. Contributed by Codex -/
noncomputable def Chain_of_HF (A : HeckeFactorization τ) : Chain τ :=
  ⟨LSet_of_LPerm A.val, ⟨chain_of_HF_helper h_321a A,
    (LSet_helper h_321a A).2.1, (LSet_helper h_321a A).2.2⟩⟩

/-- Extract the head `Link τ` encoded by a nonempty chain. The ambient
equalities in `Chain τ` retarget the witness in `isChain` from its local
permutation to the ambient `τ`. Contributed by Codex -/
noncomputable def Link_of_Chain {C : Chain τ} (hC : C.val ≠ []) :
  Link τ where
  A := (C.val.head hC).1
  B := boxUnion C.val.tail
  χa := (C.val.head hC).2
  χb := chiSum C.val.tail
  union_eq := by
    rcases C with ⟨c, ⟨h_chain, h_union, h_chi⟩⟩
    cases c with
    | nil =>
        exfalso
        exact hC rfl
    | cons AT Q =>
        rcases h_chain with ⟨σ, L, hA, hχa, hB, hχb, h_chain'⟩
        -- `isChain` only tells us that the witness link unions to `inv_set σ`;
        -- the outer `Chain τ` hypothesis upgrades that to `inv_set τ`.
        simpa [boxUnion, hA, hB] using h_union
  sep := by
    rcases C with ⟨c, ⟨h_chain, h_union, h_chi⟩⟩
    cases c with
    | nil =>
        exfalso
        exact hC rfl
    | cons AT Q =>
        rcases h_chain with ⟨σ, L, hA, hχa, hB, hχb, h_chain'⟩
        intro p hp q hq hpq
        apply L.sep p ?_ q ?_ hpq
        · simpa [hA] using hp
        · simpa [hB] using hq
  shift := by
    rcases C with ⟨c, ⟨h_chain, h_union, h_chi⟩⟩
    cases c with
    | nil =>
        exfalso
        exact hC rfl
    | cons AT Q =>
        rcases h_chain with ⟨σ, L, hA, hχa, hB, hχb, h_chain'⟩
        simpa [chiSum, hχa, hχb] using h_chi.symm

noncomputable def SVTL_of_HF
  (A : HeckeFactorization τ) : SVT_Layering τ :=
  ⟨LSet_of_LPerm A.val, LSet_helper h_321a A⟩

/-- Extract the head `Link τ` from a nonempty `SVT_Layering τ`. Contributed by Codex -/
noncomputable def Link_of_SVTL {L : SVT_Layering τ} (hL : L.val ≠ []) :
  Link τ where
  A := (L.val.head hL).1
  B := boxUnion L.val.tail
  χa := (L.val.head hL).2
  χb := chiSum L.val.tail
  union_eq := by
    rcases L with ⟨l, hprop⟩
    cases l with
    | nil =>
        exfalso
        exact hL rfl
    | cons head tail =>
        simpa [boxUnion] using hprop.2.1
  sep := by
    rcases L with ⟨l, hprop⟩
    cases l with
    | nil =>
        exfalso
        exact hL rfl
    | cons head tail =>
        simpa [IsLayering] using hprop.1.2
  shift := by
    rcases L with ⟨l, hprop⟩
    cases l with
    | nil =>
        exfalso
        exact hL rfl
    | cons head tail =>
        simpa [chiSum] using hprop.2.2.symm


omit h_321a in
/-- Legacy inverse from `SVT_Layering` to Hecke factorizations. It is kept for
comparison with the cleaner list-based helper below. Contributed by Codex -/
noncomputable def HF_of_SVTL_old {τ : AspPerm} (h_321a : is_321a τ) :
  SVT_Layering τ →  HeckeFactorization τ
  | ⟨[], hL⟩ => by
    use []
    dsimp [DProd]
    dsimp [chiSum] at hL
    rcases hL with ⟨_, ⟨h_union,h_chi⟩⟩
    have h_inv : inv_set τ = ∅ := by
      dsimp [boxUnion] at h_union
      exact h_union.symm
    exact (AspPerm.eq_id τ h_inv h_chi.symm).symm
  | ⟨AT :: L', hL⟩ => by
    obtain ⟨A, χa⟩ := AT
    dsimp [boxUnion, chiSum] at hL
    rcases hL with ⟨h_layering, h_union, h_chi⟩
    let B := boxUnion L'
    have : IsLayering L' ∧ ∀ p ∈ A, ∀ q ∈ B, p ≼ q → p = q := by
      simpa [IsLayering] using h_layering
    obtain ⟨h_layering', h_sep⟩ := this
    have hAB : A ∪ B = inv_set τ := by
      simpa using h_union
    let Lnk : Link τ := Link.mk A B χa (chiSum L') hAB h_sep h_chi.symm
    have hLnk : dprod_to_link h_321a (link_to_dprod h_321a Lnk) = Lnk :=
      (dprod_to_link_link_to_dprod (τ := τ) h_321a) Lnk
    let fac := link_to_dprod h_321a Lnk
    let α : AspPerm := fac.1.1
    let β : AspPerm := fac.1.2
    have h_spec := dprod_of_link_spec h_321a Lnk
    have h_dprod : α ⋆ β = τ := fac.2
    have h_χa : α.χ = χa := by
      simpa [fac, α, β, link_to_dprod] using h_spec.2.1
    have h_χb : β.χ = chiSum L' := by
      simpa [fac, α, β, link_to_dprod] using h_spec.2.2
    have h_L : β ≤L τ := by
      rw [← h_dprod]
      exact Submodular.lel_of_dprod α β
    have h_321a_β : is_321a β := is_321a_of_lel h_321a h_L
    have h_unionβ : boxUnion L' = inv_set β := by
      have := congrArg Link.B hLnk
      simpa [Lnk, fac, α, β, link_to_dprod, dprod_to_link, Link_of_dprod, B] using this.symm
    let Lβ : HeckeFactorization β := HF_of_SVTL_old h_321a_β
      ⟨L', ⟨h_layering', ⟨h_unionβ, h_χb.symm⟩⟩⟩
    use α :: Lβ.val
    rw [DProd_cons, ← h_dprod]
    congr
    exact Lβ.property
termination_by L => L.1.length
decreasing_by
  simp_wf

omit h_321a in
/-- Recursively recover the factor list encoded by a chain. The head factor is
obtained from `Link_of_Chain`, and the tail recursion runs on the second factor
of the associated Demazure-product decomposition. Contributed by Codex -/
noncomputable def HFList_of_Chain {τ : AspPerm} (h_321a : is_321a τ) :
  (L : List (Set (ℤ × ℤ) × ℤ)) →
  isChain L → boxUnion L = inv_set τ → chiSum L = τ.χ → List AspPerm
  | [], _, _, _ => []
  | AT :: L', h_chain, h_union, h_chi => by
    let C : Chain τ := ⟨AT :: L', ⟨h_chain, h_union, h_chi⟩⟩
    have hC : C.val ≠ [] := by
      simp [C]
    have h_chain' : isChain L' := by
      rcases h_chain with ⟨σ, L, hA, hχa, hB, hχb, h_chain'⟩
      exact h_chain'
    let Lnk : Link τ := Link_of_Chain (τ := τ) (C := C) hC
    let fac := link_to_dprod h_321a Lnk
    let α : AspPerm := fac.1.1
    let β : AspPerm := fac.1.2
    have h_spec := dprod_of_link_spec h_321a Lnk
    -- The recursive call moves from `τ` to the tail factor `β`, whose
    -- inversion set and shift are read off from the same link.
    have h_L : β ≤L τ := by
      rw [← fac.2]
      exact Submodular.lel_of_dprod α β
    have h_321a_β : is_321a β := is_321a_of_lel h_321a h_L
    have hLnk : dprod_to_link h_321a fac = Lnk := by
      exact (dprod_to_link_link_to_dprod (τ := τ) h_321a) Lnk
    have h_unionβ : boxUnion L' = inv_set β := by
      have := congrArg Link.B hLnk
      simpa [C, Lnk, fac, α, β, dprod_to_link, Link_of_dprod] using this.symm
    have h_χβ : chiSum L' = β.χ := by
      simpa [fac, α, β, link_to_dprod] using h_spec.2.2.symm
    exact α :: HFList_of_Chain h_321a_β L' h_chain' h_unionβ h_χβ
termination_by L => L.length
decreasing_by
  simp_wf

omit h_321a in
/-- One-step unfold rule for the nonempty branch of `HFList_of_Chain`.
This is the stable computation lemma used in later proofs. Contributed by Codex -/
lemma HFList_of_Chain_cons_unfold {τ : AspPerm} (h_321a : is_321a τ)
    (AT : Set (ℤ × ℤ) × ℤ) (L' : List (Set (ℤ × ℤ) × ℤ))
    (h_chain : isChain (AT :: L'))
    (h_union : boxUnion (AT :: L') = inv_set τ)
    (h_chi : chiSum (AT :: L') = τ.χ) :
    let C : Chain τ := ⟨AT :: L', ⟨h_chain, h_union, h_chi⟩⟩
    let hC : C.val ≠ [] := by
      simp [C]
    have h_chain' : isChain L' := by
      rcases h_chain with ⟨σ, L, hA, hχa, hB, hχb, h_chain'⟩
      exact h_chain'
    let Lnk : Link τ := Link_of_Chain (τ := τ) (C := C) hC
    let fac := link_to_dprod h_321a Lnk
    let α : AspPerm := fac.1.1
    let β : AspPerm := fac.1.2
    have h_spec := dprod_of_link_spec h_321a Lnk
    have h_L : β ≤L τ := by
      rw [← fac.2]
      exact Submodular.lel_of_dprod α β
    have h_321a_β : is_321a β := is_321a_of_lel h_321a h_L
    have hLnk : dprod_to_link h_321a fac = Lnk := by
      exact (dprod_to_link_link_to_dprod (τ := τ) h_321a) Lnk
    have h_unionβ : boxUnion L' = inv_set β := by
      have := congrArg Link.B hLnk
      simpa [C, Lnk, fac, α, β, dprod_to_link, Link_of_dprod] using this.symm
    have h_χβ : chiSum L' = β.χ := by
      simpa [fac, α, β, link_to_dprod] using h_spec.2.2.symm
    HFList_of_Chain h_321a (AT :: L') h_chain h_union h_chi =
      α :: HFList_of_Chain h_321a_β L' h_chain' h_unionβ h_χβ := by
  set_option maxRecDepth 4096 in
    simp [HFList_of_Chain]

omit h_321a in
/-- The list produced by `HFList_of_Chain` has Demazure product `τ`.
Contributed by Codex -/
lemma HFList_of_Chain_spec {τ : AspPerm} (h_321a : is_321a τ) :
  ∀ (L : List (Set (ℤ × ℤ) × ℤ)) (h_chain : isChain L)
    (h_union : boxUnion L = inv_set τ) (h_chi : chiSum L = τ.χ),
    DProd (HFList_of_Chain h_321a L h_chain h_union h_chi) = τ
  | [], _, h_union, h_chi => by
    have h_inv : inv_set τ = ∅ := by
      simpa [boxUnion] using h_union.symm
    have hτ : τ = AspPerm.id := AspPerm.eq_id τ h_inv h_chi.symm
    simp [HFList_of_Chain, DProd, hτ]
  | AT :: L', h_chain, h_union, h_chi => by
    let C : Chain τ := ⟨AT :: L', ⟨h_chain, h_union, h_chi⟩⟩
    have hC : C.val ≠ [] := by
      simp [C]
    have h_chain' : isChain L' := by
      rcases h_chain with ⟨σ, L, hA, hχa, hB, hχb, h_chain'⟩
      exact h_chain'
    let Lnk : Link τ := Link_of_Chain (τ := τ) (C := C) hC
    let fac := link_to_dprod h_321a Lnk
    let α : AspPerm := fac.1.1
    let β : AspPerm := fac.1.2
    have h_spec := dprod_of_link_spec h_321a Lnk
    have h_L : β ≤L τ := by
      rw [← fac.2]
      exact Submodular.lel_of_dprod α β
    have h_321a_β : is_321a β := is_321a_of_lel h_321a h_L
    have hLnk : dprod_to_link h_321a fac = Lnk := by
      exact (dprod_to_link_link_to_dprod (τ := τ) h_321a) Lnk
    have h_unionβ : boxUnion L' = inv_set β := by
      have := congrArg Link.B hLnk
      simpa [C, Lnk, fac, α, β, dprod_to_link, Link_of_dprod] using this.symm
    have h_χβ : chiSum L' = β.χ := by
      simpa [fac, α, β, link_to_dprod] using h_spec.2.2.symm
    have ih := HFList_of_Chain_spec h_321a_β L' h_chain' h_unionβ h_χβ
    have hstep :
        HFList_of_Chain h_321a (AT :: L') h_chain h_union h_chi =
          α :: HFList_of_Chain h_321a_β L' h_chain' h_unionβ h_χβ :=
      HFList_of_Chain_cons_unfold h_321a AT L' h_chain h_union h_chi
    rw [hstep, DProd_cons, ih]
    simpa [fac, α, β, link_to_dprod] using h_spec.1

omit h_321a in
/-- Package `HFList_of_Chain` as a `HeckeFactorization`. This is the recursive
inverse candidate to `Chain_of_HF`. Contributed by Codex -/
noncomputable def HF_of_Chain {τ : AspPerm} (h_321a : is_321a τ) :
  Chain τ → HeckeFactorization τ
  | ⟨L, ⟨h_chain, h_union, h_chi⟩⟩ =>
      ⟨HFList_of_Chain h_321a L h_chain h_union h_chi,
        HFList_of_Chain_spec h_321a L h_chain h_union h_chi⟩

omit h_321a in
/-- For a nonempty factorization `α :: L`, the head link extracted from
`Chain_of_HF` is exactly the `Link_of_dprod` from the Link section. This is the
chain analogue of `Link_of_SVTL_of_SVTL_of_HF_cons`. Contributed by Codex -/
lemma Link_of_Chain_of_Chain_of_HF_cons {τ α : AspPerm} {L : List AspPerm}
    (h_321a : is_321a τ) (hP : DProd (α :: L) = τ) :
    let C : Chain τ := Chain_of_HF h_321a ⟨α :: L, hP⟩
    let hC : C.val ≠ [] := by
      simp [C, Chain_of_HF, LSet_of_LPerm]
    Link_of_Chain (τ := τ) (C := C) hC = Link_of_dprod h_321a (by
      let β := DProd L
      have : α ⋆ β = τ := by
        rw [← hP, DProd_cons]
      exact this) := by
  let β := DProd L
  have h_L : β ≤L τ := by
    rw [← hP, DProd_cons]
    exact Submodular.lel_of_dprod α β
  have h_321a_β : is_321a β := is_321a_of_lel h_321a h_L
  have τ_eq : α ⋆ β = τ := by
    rw [← hP, DProd_cons]
  let C : Chain τ := Chain_of_HF h_321a ⟨α :: L, hP⟩
  have hC : C.val ≠ [] := by
    simp [C, Chain_of_HF, LSet_of_LPerm]
  apply Link.ext
  · have hA : (Link_of_Chain (τ := τ) (C := C) hC).A = τ.sr α '' inv_set α := by
      ext p
      simp [C, Link_of_Chain, Chain_of_HF, LSet_of_LPerm, τ_eq, β]
    rw [hA]
    rfl
  · change boxUnion (LSet_of_LPerm L) = inv_set β
    exact (LSet_helper h_321a_β ⟨L, rfl⟩).2.1
  · change α.χ = α.χ
    rfl

omit h_321a in
/-- Applying `LSet_of_LPerm` to the factorization recovered from a chain returns
the original chain list. This is the core right-inverse statement on raw lists.
Contributed by Codex -/
lemma LSet_of_HFList_of_Chain {τ : AspPerm} (h_321a : is_321a τ) :
  ∀ (L : List (Set (ℤ × ℤ) × ℤ)) (h_chain : isChain L)
    (h_union : boxUnion L = inv_set τ) (h_chi : chiSum L = τ.χ),
    LSet_of_LPerm (HFList_of_Chain h_321a L h_chain h_union h_chi) = L
  | [], _, h_union, h_chi => by
      have h_inv : inv_set τ = ∅ := by
        simpa [boxUnion] using h_union.symm
      have hτ : τ = AspPerm.id := AspPerm.eq_id τ h_inv h_chi.symm
      simp [HFList_of_Chain, LSet_of_LPerm, hτ]
  | AT :: L', h_chain, h_union, h_chi => by
      let C : Chain τ := ⟨AT :: L', ⟨h_chain, h_union, h_chi⟩⟩
      have hC : C.val ≠ [] := by
        simp [C]
      have h_chain' : isChain L' := by
        rcases h_chain with ⟨σ, L, hA, hχa, hB, hχb, h_chain'⟩
        exact h_chain'
      let Lnk : Link τ := Link_of_Chain (τ := τ) (C := C) hC
      let fac := link_to_dprod h_321a Lnk
      let α : AspPerm := fac.1.1
      let β : AspPerm := fac.1.2
      have h_spec := dprod_of_link_spec h_321a Lnk
      have h_dprod : α ⋆ β = τ := by
        simpa [fac, α, β, link_to_dprod] using h_spec.1
      have h_L : β ≤L τ := by
        rw [← h_dprod]
        exact Submodular.lel_of_dprod α β
      have h_321a_β : is_321a β := is_321a_of_lel h_321a h_L
      have hLnk : dprod_to_link h_321a fac = Lnk := by
        exact (dprod_to_link_link_to_dprod (τ := τ) h_321a) Lnk
      have h_unionβ : boxUnion L' = inv_set β := by
        have := congrArg Link.B hLnk
        simpa [C, Lnk, fac, α, β, dprod_to_link, Link_of_dprod, Link_of_Chain] using this.symm
      have h_χβ : chiSum L' = β.χ := by
        simpa [C, Lnk, fac, α, β, link_to_dprod, Link_of_Chain] using (congrArg Link.χb hLnk).symm
      have ih := LSet_of_HFList_of_Chain (τ := β) h_321a_β L' h_chain' h_unionβ h_χβ
      have hstep :
          HFList_of_Chain h_321a (AT :: L') h_chain h_union h_chi =
            α :: HFList_of_Chain h_321a_β L' h_chain' h_unionβ h_χβ := by
        simpa [C, Lnk, fac, α, β] using
          (HFList_of_Chain_cons_unfold h_321a AT L' h_chain h_union h_chi)
      -- The link round-trip identifies the recovered head layer with the
      -- original tableau layer `AT`.
      have hA1 : τ.sr α '' inv_set α = AT.1 := by
        have := congrArg Link.A hLnk
        simpa [C, Lnk, fac, α, β, dprod_to_link, Link_of_dprod, Link_of_Chain] using this
      have hA2 : α.χ = AT.2 := by
        have := congrArg Link.χa hLnk
        simpa [C, Lnk, fac, α, β, dprod_to_link, Link_of_dprod, Link_of_Chain] using this
      rw [hstep]
      simp [LSet_of_LPerm, HFList_of_Chain_spec, ih, hA1, hA2, h_dprod]

omit h_321a in
/-- `Chain_of_HF` after `HF_of_Chain` is the identity on `Chain τ`.
Contributed by Codex -/
lemma Chain_of_HF_HF_of_Chain {τ : AspPerm} (h_321a : is_321a τ) (C : Chain τ) :
  Chain_of_HF h_321a (HF_of_Chain h_321a C) = C := by
  rcases C with ⟨L, ⟨h_chain, h_union, h_chi⟩⟩
  apply Subtype.ext
  simpa [Chain_of_HF, HF_of_Chain] using
    (LSet_of_HFList_of_Chain h_321a L h_chain h_union h_chi)

omit h_321a in
/-- Injectivity of `LSet_of_LPerm` on Hecke factorizations of a fixed `τ`.
The head step uses the bijection between Demazure-product decompositions and
links from the Link section; the tail then follows by induction. Contributed by Codex -/
lemma LSet_of_LPerm_injective {τ : AspPerm} (h_321a : is_321a τ) :
    ∀ {L₁ : List AspPerm} (_h₁ : DProd L₁ = τ) {L₂ : List AspPerm} (_h₂ : DProd L₂ = τ),
      LSet_of_LPerm L₁ = LSet_of_LPerm L₂ -> L₁ = L₂
  | [], _, [], _, _ => rfl
  | [], _, _ :: _, _, hEq => by
      simp [LSet_of_LPerm] at hEq
  | _ :: _, _, [], _, hEq => by
      simp [LSet_of_LPerm] at hEq
  | α₁ :: T₁, h₁, α₂ :: T₂, h₂, hEq => by
      have hHeadTail :
          ((DProd (α₁ :: T₁)).sr α₁ '' inv_set α₁, α₁.χ) =
            ((DProd (α₂ :: T₂)).sr α₂ '' inv_set α₂, α₂.χ)
          ∧ LSet_of_LPerm T₁ = LSet_of_LPerm T₂ := by
        simpa [LSet_of_LPerm] using hEq
      rcases hHeadTail with ⟨hHead, hTail⟩
      let β₁ := DProd T₁
      let β₂ := DProd T₂
      have h_L₁ : β₁ ≤L τ := by
        rw [← h₁, DProd_cons]
        exact Submodular.lel_of_dprod α₁ β₁
      have h_L₂ : β₂ ≤L τ := by
        rw [← h₂, DProd_cons]
        exact Submodular.lel_of_dprod α₂ β₂
      have h_321a_β₁ : is_321a β₁ := is_321a_of_lel h_321a h_L₁
      have h_321a_β₂ : is_321a β₂ := is_321a_of_lel h_321a h_L₂
      have τ_eq₁ : α₁ ⋆ β₁ = τ := by rw [← h₁, DProd_cons]
      have τ_eq₂ : α₂ ⋆ β₂ = τ := by rw [← h₂, DProd_cons]
      -- Equal head layers determine equal links, and the Link-section
      -- bijection then recovers equal head/tail factors.
      have hLink : Link_of_dprod h_321a τ_eq₁ = Link_of_dprod h_321a τ_eq₂ := by
        apply Link.ext
        · simpa [h₁, h₂] using congrArg Prod.fst hHead
        · calc
            (Link_of_dprod h_321a τ_eq₁).B = inv_set β₁ := rfl
            _ = boxUnion (LSet_of_LPerm T₁) := (LSet_helper h_321a_β₁ ⟨T₁, rfl⟩).2.1.symm
            _ = boxUnion (LSet_of_LPerm T₂) := by simp [hTail]
            _ = inv_set β₂ := (LSet_helper h_321a_β₂ ⟨T₂, rfl⟩).2.1
            _ = (Link_of_dprod h_321a τ_eq₂).B := rfl
        · exact congrArg Prod.snd hHead
      have hx := congrArg (link_to_dprod h_321a) hLink
      have hx₁ : link_to_dprod h_321a (Link_of_dprod h_321a τ_eq₁) = ⟨⟨α₁, β₁⟩, τ_eq₁⟩ := by
        simpa [dprod_to_link] using
          (link_to_dprod_dprod_to_link (τ := τ) h_321a ⟨⟨α₁, β₁⟩, τ_eq₁⟩)
      have hx₂ : link_to_dprod h_321a (Link_of_dprod h_321a τ_eq₂) = ⟨⟨α₂, β₂⟩, τ_eq₂⟩ := by
        simpa [dprod_to_link] using
          (link_to_dprod_dprod_to_link (τ := τ) h_321a ⟨⟨α₂, β₂⟩, τ_eq₂⟩)
      have hpair : (α₁, β₁) = (α₂, β₂) := by
        calc
          (α₁, β₁) = (link_to_dprod h_321a (Link_of_dprod h_321a τ_eq₁)).1 := by
            simpa using congrArg Subtype.val hx₁.symm
          _ = (link_to_dprod h_321a (Link_of_dprod h_321a τ_eq₂)).1 := by
            exact congrArg Subtype.val hx
          _ = (α₂, β₂) := by
            simpa using congrArg Subtype.val hx₂
      rcases Prod.ext_iff.mp hpair with ⟨hα, hβ⟩
      have h₂' : DProd T₂ = β₁ := by simpa [β₂] using hβ.symm
      have hT : T₁ = T₂ := LSet_of_LPerm_injective (τ := β₁) h_321a_β₁ rfl h₂' hTail
      cases hα
      simp [hT]

omit h_321a in
/-- `Chain_of_HF` is injective. Contributed by Codex -/
theorem Chain_of_HF_injective {τ : AspPerm} (h_321a : is_321a τ) :
  Function.Injective (Chain_of_HF h_321a) := by
  intro A₁ A₂ hEq
  apply Subtype.ext
  exact LSet_of_LPerm_injective h_321a A₁.property A₂.property (congrArg Subtype.val hEq)

omit h_321a in
/-- `HF_of_Chain` after `Chain_of_HF` is the identity on
`HeckeFactorization τ`, obtained from injectivity of `Chain_of_HF` and the
already-proved right inverse. Contributed by Codex -/
lemma HF_of_Chain_Chain_of_HF {τ : AspPerm} (h_321a : is_321a τ) (A : HeckeFactorization τ) :
  HF_of_Chain h_321a (Chain_of_HF h_321a A) = A := by
  apply Chain_of_HF_injective h_321a
  exact Chain_of_HF_HF_of_Chain h_321a (Chain_of_HF h_321a A)

omit h_321a in
/-- The conversion from Hecke factorizations to chains is a bijection, with
inverse `HF_of_Chain`. Contributed by Codex -/
theorem bijective_Chain_of_HF {τ : AspPerm} (h_321a : is_321a τ) :
  Function.Bijective (Chain_of_HF h_321a) := by
  constructor
  · exact Chain_of_HF_injective h_321a
  · intro C
    exact ⟨HF_of_Chain h_321a C, Chain_of_HF_HF_of_Chain h_321a C⟩

omit h_321a in
/-- Recursively recover the factor list encoded by an `SVT_Layering`.
Contributed by Codex -/
noncomputable def HFList_of_SVTL {τ : AspPerm} (h_321a : is_321a τ) :
  (L : List (Set (ℤ × ℤ) × ℤ)) →
  IsLayering L → boxUnion L = inv_set τ → chiSum L = τ.χ → List AspPerm
  | [], _, _, _ => []
  | AT :: L', h_layering, h_union, h_chi => by
    let S : SVT_Layering τ := ⟨AT :: L', ⟨h_layering, h_union, h_chi⟩⟩
    have hS : S.val ≠ [] := by
      simp [S]
    have hs : IsLayering L' ∧ ∀ p ∈ AT.1, ∀ q ∈ boxUnion L', p ≼ q → p = q := by
      simpa [IsLayering] using h_layering
    let Lnk : Link τ := Link_of_SVTL (τ := τ) (L := S) hS
    let fac := link_to_dprod h_321a Lnk
    let α : AspPerm := fac.1.1
    let β : AspPerm := fac.1.2
    have h_spec := dprod_of_link_spec h_321a Lnk
    have h_L : β ≤L τ := by
      rw [← fac.2]
      exact Submodular.lel_of_dprod α β
    have h_321a_β : is_321a β := is_321a_of_lel h_321a h_L
    have hLnk : dprod_to_link h_321a fac = Lnk := by
      exact (dprod_to_link_link_to_dprod (τ := τ) h_321a) Lnk
    have h_layering' : IsLayering L' := hs.1
    have h_unionβ : boxUnion L' = inv_set β := by
      have := congrArg Link.B hLnk
      simpa [S, Lnk, fac, α, β, dprod_to_link, Link_of_dprod] using this.symm
    have h_χβ : chiSum L' = β.χ := by
      simpa [fac, α, β, link_to_dprod] using h_spec.2.2.symm
    exact α :: HFList_of_SVTL h_321a_β L' h_layering' h_unionβ h_χβ
termination_by L => L.length
decreasing_by
  simp_wf

omit h_321a in
/-- One-step unfold rule for the nonempty branch of `HFList_of_SVTL`.
Contributed by Codex -/
lemma HFList_of_SVTL_cons_unfold {τ : AspPerm} (h_321a : is_321a τ)
    (AT : Set (ℤ × ℤ) × ℤ) (L' : List (Set (ℤ × ℤ) × ℤ))
    (h_layering : IsLayering (AT :: L'))
    (h_union : boxUnion (AT :: L') = inv_set τ)
    (h_chi : chiSum (AT :: L') = τ.χ) :
    let S : SVT_Layering τ := ⟨AT :: L', ⟨h_layering, h_union, h_chi⟩⟩
    let hS : S.val ≠ [] := by
      simp [S]
    let hs : IsLayering L' ∧ ∀ p ∈ AT.1, ∀ q ∈ boxUnion L', p ≼ q → p = q := by
      simpa [IsLayering] using h_layering
    let Lnk : Link τ := Link_of_SVTL (τ := τ) (L := S) hS
    let fac := link_to_dprod h_321a Lnk
    let α : AspPerm := fac.1.1
    let β : AspPerm := fac.1.2
    have h_spec := dprod_of_link_spec h_321a Lnk
    have h_L : β ≤L τ := by
      rw [← fac.2]
      exact Submodular.lel_of_dprod α β
    have h_321a_β : is_321a β := is_321a_of_lel h_321a h_L
    have hLnk : dprod_to_link h_321a fac = Lnk := by
      exact (dprod_to_link_link_to_dprod (τ := τ) h_321a) Lnk
    have h_layering' : IsLayering L' := hs.1
    have h_unionβ : boxUnion L' = inv_set β := by
      have := congrArg Link.B hLnk
      simpa [S, Lnk, fac, α, β, dprod_to_link, Link_of_dprod] using this.symm
    have h_χβ : chiSum L' = β.χ := by
      simpa [fac, α, β, link_to_dprod] using h_spec.2.2.symm
    HFList_of_SVTL h_321a (AT :: L') h_layering h_union h_chi =
      α :: HFList_of_SVTL h_321a_β L' h_layering' h_unionβ h_χβ := by
  set_option maxRecDepth 4096 in
    simp [HFList_of_SVTL]

omit h_321a in
/-- The factor list recovered from an `SVT_Layering` has Demazure product `τ`.
Contributed by Codex -/
lemma HFList_of_SVTL_spec {τ : AspPerm} (h_321a : is_321a τ) :
  ∀ (L : List (Set (ℤ × ℤ) × ℤ)) (h_layering : IsLayering L)
    (h_union : boxUnion L = inv_set τ) (h_chi : chiSum L = τ.χ),
    DProd (HFList_of_SVTL h_321a L h_layering h_union h_chi) = τ
  | [], _, h_union, h_chi => by
    have h_inv : inv_set τ = ∅ := by
      simpa [boxUnion] using h_union.symm
    have hτ : τ = AspPerm.id := AspPerm.eq_id τ h_inv h_chi.symm
    simp [HFList_of_SVTL, DProd, hτ]
  | AT :: L', h_layering, h_union, h_chi => by
    let S : SVT_Layering τ := ⟨AT :: L', ⟨h_layering, h_union, h_chi⟩⟩
    have hS : S.val ≠ [] := by
      simp [S]
    have hs : IsLayering L' ∧ ∀ p ∈ AT.1, ∀ q ∈ boxUnion L', p ≼ q → p = q := by
      simpa [IsLayering] using h_layering
    let Lnk : Link τ := Link_of_SVTL (τ := τ) (L := S) hS
    let fac := link_to_dprod h_321a Lnk
    let α : AspPerm := fac.1.1
    let β : AspPerm := fac.1.2
    have h_spec := dprod_of_link_spec h_321a Lnk
    have h_L : β ≤L τ := by
      rw [← fac.2]
      exact Submodular.lel_of_dprod α β
    have h_321a_β : is_321a β := is_321a_of_lel h_321a h_L
    have hLnk : dprod_to_link h_321a fac = Lnk := by
      exact (dprod_to_link_link_to_dprod (τ := τ) h_321a) Lnk
    have h_layering' : IsLayering L' := hs.1
    have h_unionβ : boxUnion L' = inv_set β := by
      have := congrArg Link.B hLnk
      simpa [S, Lnk, fac, α, β, dprod_to_link, Link_of_dprod] using this.symm
    have h_χβ : chiSum L' = β.χ := by
      simpa [fac, α, β, link_to_dprod] using h_spec.2.2.symm
    have ih := HFList_of_SVTL_spec h_321a_β L' h_layering' h_unionβ h_χβ
    have hstep :
        HFList_of_SVTL h_321a (AT :: L') h_layering h_union h_chi =
          α :: HFList_of_SVTL h_321a_β L' h_layering' h_unionβ h_χβ :=
      HFList_of_SVTL_cons_unfold h_321a AT L' h_layering h_union h_chi
    rw [hstep, DProd_cons, ih]
    simpa [fac, α, β, link_to_dprod] using h_spec.1

omit h_321a in
/-- Package `HFList_of_SVTL` as a `HeckeFactorization`. Contributed by Codex -/
noncomputable def HF_of_SVTL {τ : AspPerm} (h_321a : is_321a τ) :
  SVT_Layering τ → HeckeFactorization τ
  | ⟨L, ⟨h_layering, h_union, h_chi⟩⟩ =>
      ⟨HFList_of_SVTL h_321a L h_layering h_union h_chi,
        HFList_of_SVTL_spec h_321a L h_layering h_union h_chi⟩

omit h_321a in
/-- Compare the head link extracted from `SVTL_of_HF` with the corresponding
`Link_of_dprod`. Contributed by Codex -/
lemma Link_of_SVTL_of_SVTL_of_HF_cons {τ α : AspPerm} {L : List AspPerm}
    (h_321a : is_321a τ) (hP : DProd (α :: L) = τ) :
    let S : SVT_Layering τ := SVTL_of_HF h_321a ⟨α :: L, hP⟩
    let hS : S.val ≠ [] := by
      simp [S, SVTL_of_HF, LSet_of_LPerm]
    Link_of_SVTL (τ := τ) (L := S) hS = Link_of_dprod h_321a (by
      let β := DProd L
      have : α ⋆ β = τ := by
        rw [← hP, DProd_cons]
      exact this) := by
  let β := DProd L
  have h_L : β ≤L τ := by
    rw [← hP, DProd_cons]
    exact Submodular.lel_of_dprod α β
  have h_321a_β : is_321a β := is_321a_of_lel h_321a h_L
  have τ_eq : α ⋆ β = τ := by
    rw [← hP, DProd_cons]
  let S : SVT_Layering τ := SVTL_of_HF h_321a ⟨α :: L, hP⟩
  have hS : S.val ≠ [] := by
    simp [S, SVTL_of_HF, LSet_of_LPerm]
  apply Link.ext
  · have hA : (Link_of_SVTL (τ := τ) (L := S) hS).A = τ.sr α '' inv_set α := by
      ext p
      simp [S, Link_of_SVTL, SVTL_of_HF, LSet_of_LPerm, τ_eq, β]
    rw [hA]
    rfl
  · change boxUnion (LSet_of_LPerm L) = inv_set β
    exact (LSet_helper h_321a_β ⟨L, rfl⟩).2.1
  · change α.χ = α.χ
    rfl
end Tableaux

section SetValuedTableaux
-- This section written by Codex, using GPT-5.4.

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
