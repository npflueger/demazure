import Demazure.InvSet

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

theorem inv_321a_char (I : Set (ℤ × ℤ)) :
  set_321a_prop I
  ↔ (∃ τ : (ℤ → ℤ), (is_321a τ ∧ Function.Bijective τ ∧ inv_set τ = I)) := by
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

def is_src (τ : AspPerm) (u : ℤ) : Prop :=
  ∃ v : ℤ, ⟨u, v⟩ ∈ inv_set τ

def src_of_inv {τ : AspPerm} {u v : ℤ} (uv_inv : ⟨u, v⟩ ∈ inv_set τ) :
  is_src τ u := by use v

def is_snk (τ : AspPerm) (v : ℤ) : Prop :=
  ∃ u : ℤ, (u, v) ∈ inv_set τ

def snk_of_inv {τ : AspPerm} {u v : ℤ} (uv_inv : ⟨u, v⟩ ∈ inv_set τ) :
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
      have := not_src_and_snk (h_321a := h_321a) x
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
      have := not_src_and_snk (h_321a := h_321a) x
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
  unfold AspPerm.s
  have : τ.se a b = τ.se a v ∪ τ.se (τ v) b := by
    ext n
    simp only [Finset.mem_union, τ.mem_se]
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
        have un_inv : ⟨u, n⟩ ∈ inv_set τ := by
          have u_lt_n : u < n := lt_of_lt_of_le u_lt_b n_ge_b
          have τu_gt_τn : τ u > τ n := lt_of_lt_of_le τn_lt_a τu_ge_a
          exact ⟨u_lt_n, τu_gt_τn⟩
        have := tfree_of_321a τ h_321a u n v
        rcases this <;> contradiction
    · rintro (⟨n_ge_v, τn_lt_a⟩ | ⟨n_ge_b, τn_lt_τv⟩)
      · exact ⟨le_trans b_le_v n_ge_v, τn_lt_a⟩
      · exact ⟨n_ge_b, lt_trans τn_lt_τv τv_lt_a⟩

  rw [this, Finset.card_union]
  suffices τ.se a v ∩ τ.se (τ v) b = ∅ by
    rw [Finset.card_eq_zero.mpr this]
    simp

  simp only [Finset.eq_empty_iff_forall_notMem, Finset.mem_inter]
  intro x x_mem
  simp only [τ.mem_se] at x_mem
  obtain ⟨⟨x_ge_v, τx_lt_a⟩, ⟨x_ge_b,τx_lt_τv⟩⟩ := x_mem
  have vx_inv : ⟨v, x⟩ ∈ inv_set τ := (τ.inv_iff_lt x_ge_v).mpr τx_lt_τv
  have := tfree_of_321a τ h_321a u v x
  rcases this <;> contradiction

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
  let A := τ.se (τ v) b
  let B := τ.se a (τ⁻¹ w)
  let S := τ.se a b
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
    have : A.card = m - 1 := by exact τ.s_τv_b b m_pos
    rw [this]
    have : B.card = m' := by
      have := τ⁻¹.s'_b_τu a m'_pos
      simpa [τ⁻¹.dual_inverse] using this
    rw [this]
    have : S.card + 1 = τ.s a b + 1:= by rfl
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
  let S := τ.se a b
  let A := τ.se a (τ⁻¹ w)
  let B := τ.se (τ v) b
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
      rw [← τ⁻¹.s'_b_τu a m'_pos]
      simp [τ⁻¹.dual_inverse]
      congr
    rw [this]
    have : B.card = m - 1 := by
      rw [← τ.s_τv_b b m_pos]
      congr
    rw [this]
    have : S.card = τ.s a b := by rfl
    rw [this]
    linarith [h_sum]

  have := Finset.card_le_card (Finset.union_subset A_subset B_subset)
  linarith [this, ineq]

lemma split_s' {u v : ℤ} {a b : ℤ}
  (u_lt_b : u < b) (b_le_v : b ≤ v) (τv_lt_a : τ v < a) (τu_ge_a : τ u ≥ a) :
  τ⁻¹.s b (τ u) + τ⁻¹.s u a = τ⁻¹.s b a := by
  let u' := τ v
  let v' := τ u
  have := split_s (τ := τ⁻¹) (h_321a := inv_is_321a (τ := τ) (h_321a := h_321a))
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
  have bp := between_inv (τ := τ) (h_321a := h_321a) (h_L uv_inv) u_le_x x_le_v
  have bpβ := between_inv (τ := β) (h_321a := is_321a_of_lel (τ := τ) (β := β)
    (h_321a := h_321a) (h_L := h_L)) uv_inv u_le_x x_le_v
  by_cases h_src : is_src β x
  · have h_ux : ⟨u, x⟩ ∉ inv_set τ := bp.src_iff_left_ninv.mp
      (src_of_src (h_L := h_L) h_src)
    have h_xv : ⟨x, v⟩ ∈ inv_set β := bpβ.src_iff_right_inv.mp h_src
    have h_ux_β : ⟨u, x⟩ ∉ inv_set β := by
      contrapose! h_ux
      exact h_L h_ux
    have x_src : is_src β x := src_of_inv h_xv
    have x_snk : ¬ is_snk τ x := not_imp_not.mpr bp.snk_iff_left_inv.mp h_ux
    have x_snk_β : ¬ is_snk β x := not_imp_not.mpr
      (snk_of_snk (h_L := h_L)) x_snk
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
        exact src_of_src (h_L := h_L) h_src
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
      (snk_of_snk (h_L := h_L) h_snk)
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
        exact snk_of_snk (h_L := h_L) h_snk
      · intro _
        exact x_snk

def interval_sub (i₁ i₂ : (ℤ × ℤ)) : Prop :=
  i₂.1 ≤ i₁.1 ∧ i₁.2 ≤ i₂.2
infix:50 " ≼ " => interval_sub

lemma inv_of_lel_iff
  {u v u' v' : ℤ} (uv_inv : ⟨u, v⟩ ∈ inv_set β) (nested : ⟨u', v'⟩ ≼ ⟨u, v⟩) :
  ⟨u', v'⟩ ∈ inv_set β ↔ ⟨u', v'⟩ ∈ inv_set τ := by
  have h_321a_β := is_321a_of_lel (h_321a := h_321a) (h_L := h_L)
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
    between_inv_lel (h_321a := h_321a) (h_L := h_L)
    uv_inv nested.1 (le_trans (le_of_lt u'v'_inv.1) nested.2)
  have u'_src : is_src β u' := bpu'.src_iff.mpr u'_src_τ
  have u'v_inv : ⟨u', v⟩ ∈ inv_set β := bpu'.propβ.src_iff_right_inv.mp u'_src

  have v'_snk_τ : is_snk τ v' := snk_of_inv u'v'_inv
  have bpv' : between_inv_lel_prop β τ u' v' v :=
    between_inv_lel (h_321a := h_321a) (h_L := h_L)
    u'v_inv (le_of_lt u'v'_inv.1) nested.2
  have v'_snk : is_snk β v' := bpv'.snk_iff.mpr v'_snk_τ
  have u'v'_inv : ⟨u', v'⟩ ∈ inv_set β := bpv'.propβ.snk_iff_left_inv.mp v'_snk

  exact u'v'_inv

omit h_321a h_L in
lemma set_321a_of_func (avset : set_321a) : set_321a_prop (inv_set avset.to_func) := by
  constructor
  · show AspSet_prop (inv_set avset.to_func)
    rw [avset.invSet_func]
    refine avset.prop
  · simp [avset.prop_321a.tfree, avset.invSet_func]

theorem eq_s_of_lel
  {u b v : ℤ} (uv_inv : ⟨u, v⟩ ∈ inv_set β) (u_lt_b : u < b) :
  β.s (β v) b = τ.s (τ v) b := by
  unfold AspPerm.s
  suffices β.se (β v) b = τ.se (τ v) b by
    rw [this]
  ext x
  suffices x ≥ b → (β x < β v ↔ τ x < τ v) by
    simpa [AspPerm.se, southeast_set, this]
  intro x_ge_b
  have u_lt_x : u < x := lt_of_lt_of_le u_lt_b x_ge_b

  wlog x_le_v : x ≤ v
  · have v_lt_x : v < x := by linarith
    have v_snk : is_snk β v := snk_of_inv uv_inv
    have β_lt: β v < β x := snk_lt (is_321a_of_lel (h_321a := h_321a) (h_L := h_L))
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
  exact inv_of_lel_iff (h_321a := h_321a) (h_L := h_L) uv_inv nested


-- This is roughly a repeat of the proof above. Can it be unified with it somehow?
lemma eq_s'_of_lel
  {u b v : ℤ} (uv_inv : ⟨u, v⟩ ∈ inv_set β) (b_le_v : b ≤ v) :
  β.s' b (β u) = τ.s' b (τ u) := by
  unfold AspPerm.s'
  suffices β.nw (β u) b = τ.nw (τ u) b by
    rw [this]
  ext x
  suffices x < b → (β x ≥ β u ↔ τ x ≥ τ u) by
    simpa [AspPerm.nw, northwest_set, this]
  intro x_lt_b

  wlog u_le_x : u ≤ x
  · have x_lt_u : x < u := by linarith
    have u_src : is_src β u := src_of_inv uv_inv
    have β_gt: β x < β u := src_gt (is_321a_of_lel (h_321a := h_321a) (h_L := h_L))
      u_src x_lt_u
    have τ_gt : τ x < τ u := src_gt h_321a (src_of_inv <| h_L uv_inv) x_lt_u
    constructor <;> (intro h; linarith)

  suffices ⟨u, x⟩ ∈ inv_set β ↔ ⟨u, x⟩ ∈ inv_set τ by
    rw [β.inv_iff_lt u_le_x, τ.inv_iff_lt u_le_x] at this
    constructor <;> (intro h; contrapose! h; rwa [this] at *)
  have nested : ⟨u, x⟩ ≼ ⟨u, v⟩ := by constructor <;> linarith
  exact inv_of_lel_iff (h_321a := h_321a) (h_L := h_L) uv_inv nested

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
  have u_lt_b : u < b := ((τ.u_crit b n_pos u).mp (by rfl)).2
  have v_crit := (τ.v_crit b m_pos v).mp (by rfl)
  have s_eq : τ.s (τ v) b = m - 1 := v_crit.1
  have b_le_v : b ≤ v := v_crit.2

  have m_eq : β.s (β v) b = m-1 := by
    rw [eq_s_of_lel (h_321a := h_321a) (h_L := h_L) uv_inv u_lt_b, s_eq]
  have n_eq : β.s' b (β u) = n := by
    rw [eq_s'_of_lel (h_321a := h_321a) (h_L := h_L) uv_inv b_le_v, s'_eq]

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
  have u_lt_b : u < b := ((β.u_crit b n_pos u).mp (by rfl)).2
  have v_crit := (β.v_crit b m_pos v).mp (by rfl)
  have s_eq : β.s (β v) b = m - 1 := v_crit.1
  have b_le_v : b ≤ v := v_crit.2

  have m_eq : τ.s (τ v) b = m-1 := by
    rw [← eq_s_of_lel (h_321a := h_321a) (h_L := h_L) uv_inv u_lt_b, s_eq]
  have n_eq : τ.s' b (τ u) = n := by
    rw [← eq_s'_of_lel (h_321a := h_321a) (h_L := h_L) uv_inv b_le_v, s'_eq]

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
    have uv_eq := uv_eq_of_lel (h_321a := h_321a) (h_L := h_L)
      b m_pos n_pos uv_inv
    rwa [← uv_eq.1, ← uv_eq.2]
  · intro uv_inv
    have uv_eq := uv_eq_of_lel' (h_321a := h_321a) (h_L := h_L)
      b m_pos n_pos uv_inv
    rwa [← uv_eq.1, ← uv_eq.2]

omit h_L in
theorem lel_lamp {α : AspPerm} (h_R : α ≤R τ)
  (a : ℤ) {m n : ℤ} (m_pos : m > 0) (n_pos : n > 0) :
  ⟨τ⁻¹.u a m_pos, τ⁻¹.v a n_pos⟩ ∈ inv_set α⁻¹.func
  ↔ ⟨m, n⟩ ∈ α.lamp a
  := by
  have := lel_ramp (τ := τ⁻¹) (β := α⁻¹)
    (h_321a := inv_is_321a (τ := τ) (h_321a := h_321a)) (h_L := h_R) a n_pos m_pos
  rw [this]
  simp [α⁻¹.ramp_lamp_dual a]

-- lemma s_inc_on_snks {τ : AspPerm} (h_321a : is_321a τ) {b m n : ℤ}
--   (m_snk : is_snk τ m) (b_le_m : b ≤ m) (n_snk : is_snk τ n) (b_le_n : b ≤ n) :
--     m ≤ n ↔ τ.s (τ m) b ≤ τ.s (τ n) b
--   := by
--   constructor
--   · intro m_le_n
--     refine (τ.s_nondec ?_ b).1
--     wlog m_lt_n : m < n
--     · have : m = n := eq_of_le_of_not_lt m_le_n m_lt_n
--       rw [this]
--     exact le_of_lt <| snk_lt h_321a m_snk m_lt_n
--   · intro h
--     contrapose! h with n_lt_m
--     have τ_n_lt_m : τ n < τ m := snk_lt h_321a n_snk n_lt_m
--     have h := (τ.s_nondec (le_of_lt τ_n_lt_m) b)
--     suffices τ.s (τ n) b ≠ τ.s (τ m) b by
--       exact lt_of_le_of_ne h.1 this
--     intro heq
--     have n_lt_b : n < b := h.2.mp heq n (le_refl _) τ_n_lt_m
--     exact lt_iff_not_ge.mp n_lt_b b_le_n

-- lemma s'_dec_on_srcs {τ : AspPerm} (h_321a : is_321a τ) {b m n : ℤ}
--   (m_src : is_src τ m) (m_lt_b : m < b) (n_src : is_src τ n) (n_lt_b : n < b) :
--     m ≤ n ↔ τ.s' b (τ m) ≥ τ.s' b (τ n)
--   := by
--   rw [τ.dual_inverse]
--   constructor
--   · intro m_le_n
--     refine (τ⁻¹.s_noninc b ?_).1
--     wlog m_lt_n : m < n
--     · have : m = n := eq_of_le_of_not_lt m_le_n m_lt_n
--       rw [this]
--     exact le_of_lt <| src_gt h_321a n_src m_lt_n
--   · intro h
--     contrapose! h with n_lt_m
--     have τ_m_lt_n : τ n < τ m := src_gt h_321a m_src n_lt_m
--     have h := (τ⁻¹.s_noninc b (le_of_lt τ_m_lt_n))
--     suffices τ⁻¹.s b (τ m) ≠ τ⁻¹.s b (τ n) by
--       exact lt_of_le_of_ne h.1 this
--     intro heq
--     have n_ge_b : n ≥ b := by
--       have := h.2.mp (Eq.symm heq) (τ n) (le_refl _) τ_m_lt_n
--       rwa [τ.inv_mul_cancel_eval n] at this
--     exact lt_iff_not_ge.mp n_lt_b n_ge_b

theorem inv_of_lel_iff_ramp
  {u b v : ℤ} (u_lt_b : u < b) (b_le_v : b ≤ v) :
  let m := τ.s (τ v) b + 1
  let n := τ.s' b (τ u)
  ⟨u, v⟩ ∈ inv_set β ↔ ⟨m, n⟩ ∈ β.ramp b
  := by
  intro m n
  have m_pos : m > 0 := by linarith [τ.s_nonneg (τ v) b]
  have n_pos : n > 0 := by
    simp only [n, τ.dual_inverse]
    have : τ⁻¹.s b (τ u) = τ⁻¹.s b (τ u + 1) + 1 := by
      linarith [(τ⁻¹.b_step_one_iff b (τ u)).mpr (by simp [u_lt_b])]
    linarith [this, τ⁻¹.s_nonneg b (τ u + 1)]

  rw [← lel_ramp (h_321a := h_321a) (h_L := h_L) b m_pos n_pos]
  have u_eq: u = τ.u b n_pos := by
    rw [τ.u_crit b n_pos u]
    exact ⟨rfl, u_lt_b⟩
  have v_eq: v = τ.v b m_pos := by
    rw [τ.v_crit b m_pos v]
    exact ⟨by linarith, b_le_v⟩
  rw [u_eq, v_eq]


-- theorem inv_of_lel_iff_ramp_old {β : AspPerm} (h_321a : is_321a τ) (h_L : β ≤L τ)
--   {u b v : ℤ} (uv_inv : ⟨u, v⟩ ∈ inv_set τ) (u_lt_b : u < b) (b_le_v : b ≤ v) :
--     ⟨u, v⟩ ∈ inv_set β
--     ↔ ⟨τ.s (τ v) b + 1, τ.s' b (τ u)⟩ ∈ β.ramp b
--   := by
--   have h_321a_β := is_321a_of_lel (τ := τ) h_321a h_L
--   constructor
--   · intro uv_inv_β
--     let l₁ := β u
--     let l₂ := β v + 1
--     have l₂_le_l₁ : l₂ ≤ l₁ := uv_inv_β.2
--     use l₁
--     constructor
--     · suffices β.s l₂ b ≥ τ.s (τ.func v) b + 1 by
--         apply le_trans this
--         exact (β.s_nondec l₂_le_l₁ b).1
--       simp only [l₂]
--       have : β.s (β.func v + 1) b = β.s (β.func v) b + 1 := by
--         rw [β.a_step (β v) b, β.inv_mul_cancel_eval]
--         simp [b_le_v]
--       rw [this]
--       rw [eq_s_of_lel (τ := τ) h_321a h_L uv_inv_β u_lt_b]
--     · rw [eq_s'_of_lel (τ := τ) h_321a h_L uv_inv_β b_le_v]
--   · intro mem_ramp
--     rcases mem_ramp with ⟨l, ⟨hm,hn⟩⟩

--     have : β.s' b l ≥ 1 := by
--       suffices τ.s' b (τ u) > 0 by linarith
--       suffices (τ.nw (τ u) b).Nonempty by
--         unfold AspPerm.s'
--         simp [this]
--       use u; simp [u_lt_b]
--     have nw_wit : s'_witness β l b := find_s'_witness this
--     let u' := nw_wit.u

--     have : β.s l b ≥ 1 := by
--       have : τ.s (τ.func v) b ≥ 0 := τ.s_nonneg (τ.func v) b
--       linarith [hm, this]
--     have se_wit : s_witness β l b := find_s_witness this
--     let v' := se_wit.v

--     have u'v'_inv : ⟨u', v'⟩ ∈ inv_set β := inv_of_quadrants nw_wit.mem_nw se_wit.mem_se

--     have : τ.s (τ v) b ≤ τ.s (τ v') b := by
--       suffices τ.s (τ v) b + 1 ≤ τ.s (τ v') b + 1 by linarith
--       calc
--         τ.s (τ v) b + 1 ≤ β.s l b := hm
--         _ = β.s (β v') b + 1 := by
--           exact se_wit.s_val
--         _ = τ.s (τ v') b + 1 := by
--           have := eq_s_of_lel (τ := τ) h_321a h_L u'v'_inv nw_wit.mem_nw.1
--           linarith

--     have v_le_v' : v ≤ v' := by exact (s_inc_on_snks h_321a
--       (snk_of_inv uv_inv) b_le_v (snk_of_inv <| h_L u'v'_inv) se_wit.mem_se.1).mpr this

--     have : τ.s' b (τ u) ≤ τ.s' b (τ u') := by
--       calc
--         τ.s' b (τ u) ≤ β.s' b l := hn
--         _ = β.s' b (β u') := by exact nw_wit.s'_val
--         _ = τ.s' b (τ u') := by
--           exact eq_s'_of_lel (τ := τ) h_321a h_L u'v'_inv se_wit.mem_se.1

--     have u'_le_u : u' ≤ u := by exact (s'_dec_on_srcs h_321a
--       (src_of_inv <| h_L u'v'_inv) nw_wit.mem_nw.1 (src_of_inv uv_inv) u_lt_b).mpr this
--     have nest : ⟨u, v⟩ ≼ ⟨u', v'⟩ := by
--       constructor <;> assumption
--     exact (inv_of_lel_iff (τ := τ) h_321a h_L u'v'_inv nest).mpr uv_inv



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
    · dsimp [n]
      have : τ⁻¹.s b (τ u) = τ⁻¹.s b (τ u + 1) + 1 := by
        have := (τ⁻¹.b_step_one_iff b (τ u)).mpr
        rw [τ.inv_mul_cancel_eval] at this
        linarith [this u_lt_b]
      linarith [this, τ⁻¹.s_nonneg b (τ u + 1)]
    · dsimp [n, N]
      exact (τ⁻¹.s_noninc b τu_ge_a).1

  have habMN : a - b + α.χ + β.χ = M - N := by
    linarith [τ.duality a b, h_χ]

  have legos := (α.ramp_dprod_legos β a b M N habMN).mp dprod m m_icc n n_icc
  rcases legos with (hβ | hα)
  · right
    apply (inv_of_lel_iff_ramp (h_321a := h_321a) (h_L := h_L)
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
        (h_321a := inv_is_321a (τ := τ) (h_321a := h_321a)) (h_L := h_R) τv_lt_a τu_ge_a
      rw [τ⁻¹.dual_inverse, inv_inv] at this
      simpa using this

    have : τ⁻¹.s u a + 1 = N + 1 - n ∧ τ.s a v = M + 1 - m := by
      constructor
      · have : τ⁻¹ (τ u) < b ∧ τ⁻¹ (τ v) ≥ b := by
          constructor <;> (simp; assumption)
        have := split_s (τ := τ⁻¹) (h_321a := inv_is_321a (τ := τ) (h_321a := h_321a))
          τv_lt_a τu_ge_a this.1 this.2
        simp [τ.inv_mul_cancel_eval] at this
        linarith [this]
      · linarith [split_s (τ := τ) (h_321a := h_321a) u_lt_b b_le_v τv_lt_a τu_ge_a]

    rw [this.1, this.2] at h
    apply h.mpr at hα

    exact (τ.sr_crit α u v).mpr hα

lemma union_sufficient (a b : ℤ) (h_union : inv_set τ ⊆ inv_set β ∪ (τ.sr α) '' (inv_set α)) :
   α.dprod_val_ge β a b (τ.s a b)
  := by
  let M := τ.s a b
  let N := τ.s' b a
  have habMN : a - b + α.χ + β.χ = M - N := by
    have : N = τ⁻¹.s b a := by rw [← τ.dual_inverse]
    linarith [τ.duality a b, h_χ]
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
  -- [TODO] consider packaginga all the above into a structure for use elsewhere

  have : ⟨u, v⟩ ∈ inv_set β ↔ ⟨m, n⟩ ∈ β.ramp b :=
    lel_ramp (h_321a := h_321a) (h_L := h_L) b m_ge_1 n_ge_1
  rw [← this]

  let u' := τ⁻¹.u a m'_ge_1
  let v' := τ⁻¹.v a n'_ge_1

  -- [TODO] bubble this out as a separate helper, and also the one below
  have u'_eq : τ v = u' := by
    apply (τ⁻¹.u_crit a m'_ge_1 (τ v)).mpr
    simp only [τ⁻¹.dual_inverse, inv_inv, τ.inv_mul_cancel_eval]
    constructor
    · suffices m + τ.s a v = M + 1 by linarith
      have := split_s (h_321a := h_321a) (τ.u_lt b n_ge_1) (τ.v_ge b m_ge_1)
        (τ.τv_lt b m_ge_1 m_le_M) (τ.τu_ge b n_ge_1 n_le_N)
      rw [τ.s_τv_b b m_ge_1] at this
      linarith [this]
    · exact  τ.τv_lt b m_ge_1 m_le_M

  have v'_eq : τ u = v' := by
    apply (τ⁻¹.v_crit a n'_ge_1 (τ u)).mpr
    simp only [τ.inv_mul_cancel_eval]
    constructor
    · suffices n + τ⁻¹.s u a = N by (unfold n'; linarith)
      have split := split_s' (h_321a := h_321a) (τ.u_lt b n_ge_1) (τ.v_ge b m_ge_1)
        (τ.τv_lt b m_ge_1 m_le_M) (τ.τu_ge b n_ge_1 n_le_N)
      have := τ.s'_b_τu b n_ge_1; rw [τ.dual_inverse] at this
      rw [this] at split
      convert split using 1; rw [← τ.dual_inverse]
    · exact τ.τu_ge b n_ge_1 n_le_N

  have lamp_equiv : ⟨u', v'⟩ ∈ inv_set α⁻¹.func
    ↔ ⟨m', n'⟩ ∈ α.lamp a := lel_lamp h_321a h_R a m'_ge_1 n'_ge_1
  suffices ⟨u, v⟩ ∈ inv_set β ∨ ⟨u, v⟩ ∈ (τ.sr α) '' (inv_set α) by
    rwa [← lamp_equiv, ← u'_eq, ← v'_eq, ← τ.sr_crit α u v]

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
    unfold AspPerm.s
    suffices τ.se a b = ∅ by simpa
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x x_mem; simp at x_mem
    have v₁x_inv : ⟨v₁, x⟩ ∈ inv_set τ := by
      refine (τ.inv_iff_le ?_).mpr ?_
      linarith [x_mem.1]
      linarith [x_mem.2]
    have := tfree_of_321a τ h_321a u v₁ x
    rcases this <;> contradiction
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
  have := uv_eq_of_lel' (h_321a := inv_is_321a h_321a) (h_L := h_R) a n'_pos m'_pos invα
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
    apply  (inv_of_lel_iff (τ := τ⁻¹) (β := α⁻¹) (h_321a := inv_is_321a h_321a) lel invα prec).mpr
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

def min_helper {m n : ℤ} (m_pos : m ≥ 1) (n_pos : n ≥ 1)
    {S : Set (ℤ × ℤ)} (mem : ⟨m, n⟩ ∈ S) (nmem : ⟨1, 1⟩ ∉ S) :
  ∃ m' n', m' ≥ 1 ∧ n' ≥ 1 ∧ ⟨m', n'⟩ ∈ S
  ∧ ( ⟨m'-1,n'⟩ ∉ S ∧ m' ≥ 2 ∨ ⟨m', n'-1⟩ ∉ S ∧ n' ≥ 2)
  := by
  by_cases h : ⟨m-1, n⟩ ∉ S ∧ m ≥ 2 ∨ ⟨m, n-1⟩ ∉ S ∧ n ≥ 2
  · use m, n
  push_neg at h
  by_cases m_ge_2 : m ≥ 2
  · have mem_m_dec : ⟨m-1, n⟩ ∈ S := by
      by_contra! h1
      linarith [h.1 h1]
    exact min_helper (m := m-1) (m_pos := by linarith) n_pos mem_m_dec nmem
  have m_one : m = 1 := le_antisymm (by linarith) m_pos
  subst m_one
  let h := h.2
  by_cases n_ge_2 : n ≥ 2
  · have mem_n_dec : ⟨1, n-1⟩ ∈ S:= by
      by_contra! h1
      linarith [h h1]
    exact min_helper m_pos (n := n-1) (n_pos := by linarith) mem_n_dec nmem
  have n_one : n = 1 := le_antisymm (by linarith) n_pos
  subst n_one
  exfalso; exact nmem mem
termination_by (m+n).toNat
decreasing_by
  all_goals
    simp_wf
    omega

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
    have uv_eq := uv_eq_of_lel' (h_321a := h_321a) (h_L := h_L) b M_pos N_pos uv_inv_β
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
      (h_321a := inv_is_321a h_321a) (h_L := h_R) a N_pos M_pos uv_inv_αi
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
      min_helper (m_pos := M_pos) (n_pos := N_pos) hMN_S h11_nS
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
      src_of_src (τ := τ⁻¹) (β := α⁻¹) (h_L := h_R) (src_of_inv h1_mem.2)
    have u2_src : is_src (τ⁻¹) u₂ :=
      src_of_src (τ := τ⁻¹) (β := α⁻¹) (h_L := h_R) (src_of_inv h2_mem.2)
    have v1_snk : is_snk (τ⁻¹) v₁ :=
      snk_of_snk (τ := τ⁻¹) (β := α⁻¹) (h_L := h_R) (snk_of_inv h1_mem.2)
    have v2_snk : is_snk (τ⁻¹) v₂ :=
      snk_of_snk (τ := τ⁻¹) (β := α⁻¹) (h_L := h_R) (snk_of_inv h2_mem.2)

    have hu_inv : τ⁻¹ u₂ ≤ τ⁻¹ u₁ := by
      rcases lt_or_eq_of_le hu with (hu_lt | rfl)
      · exact le_of_lt (src_gt (h_321a := inv_is_321a h_321a) u1_src hu_lt)
      · exact le_rfl
    have hv_inv : τ⁻¹ v₁ ≤ τ⁻¹ v₂ := by
      rcases lt_or_eq_of_le hv with (hv_lt | rfl)
      · exact le_of_lt (snk_lt (h_321a := inv_is_321a h_321a) v1_snk hv_lt)
      · exact le_rfl

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


end factorization
end fixed_321a_and_lel
end fixed_321a
end ASP321a
