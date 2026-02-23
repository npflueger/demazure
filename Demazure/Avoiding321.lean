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

lemma inv_is_321a (h_321a : is_321a τ) : is_321a τ⁻¹.func := by
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

lemma not_src_and_snk (h_321a : is_321a τ) (n : ℤ) :
  ¬ (is_src τ n) ∨ ¬(is_snk τ) n := by
  by_contra!
  obtain ⟨h_src, h_snk⟩ := this
  rcases h_snk with ⟨u, hu⟩
  rcases h_src with ⟨v, hv⟩
  have := tfree_of_321a τ h_321a u n v
  rcases this <;> contradiction

structure between_inv_prop (u x v : ℤ) where
  src_or_snk : is_src τ x ∨ is_snk τ x
  src_iff_right_inv : is_src τ x ↔ ⟨x, v⟩ ∈ inv_set τ
  src_iff_left_ninv : is_src τ x ↔ ⟨u, x⟩ ∉ inv_set τ
  snk_iff_left_inv : is_snk τ x ↔ ⟨u, x⟩ ∈ inv_set τ
  snk_iff_right_ninv : is_snk τ x ↔ ⟨x, v⟩ ∉ inv_set τ

lemma between_inv {u x v : ℤ} (h_321a : is_321a τ)
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
      have := not_src_and_snk (τ := τ) h_321a x
      rcases this <;> contradiction
    constructor <;> simp [x_src, x_nsnk, h_ux, h_xv]

structure s_witness (τ : AspPerm) (a b : ℤ) where
  v : ℤ
  s_val : τ.s a b = τ.s (τ v) b + 1
  mem_se : v ∈ southeast_set τ a b


noncomputable def find_s_witness {τ : AspPerm} {a b : ℤ} (hab : τ.s a b ≥ 1) : s_witness τ a b := by
  have se_nonempty : (τ.se a b).Nonempty := by
    dsimp [AspPerm.s] at hab
    have : (τ.se a b).card ≠ 0 := by linarith
    exact Finset.card_ne_zero.mp this
  let S := Finset.image τ (τ.se a b)
  have : (Finset.image τ (τ.se a b)).Nonempty := by
    simp [se_nonempty]
  let y := Finset.max' (Finset.image τ (τ.se a b)) this
  let v := τ⁻¹ y
  have y_mem : y ∈ τ '' southeast_set τ a b := by
    -- Start with the Finset version
    have h : y ∈ Finset.image τ (τ.se a b) := Finset.max'_mem (Finset.image τ (τ.se a b)) this
    simp [Finset.mem_image] at h
    exact h
  have v_mem : v ∈ southeast_set τ a b := by
    rcases y_mem with ⟨n, n_mem, y_eq⟩
    subst v; rw [← y_eq]; simp [n_mem]
  use v
  have le_τv : ∀ n ∈ southeast_set τ a b, τ n ≤ τ v := by
    intro n n_mem
    subst v; simp
    refine Finset.le_max' (Finset.image τ (τ.se a b)) (τ n) ?_
    rw [Finset.mem_image]
    use n
    simpa [AspPerm.mem_se] using n_mem
  · suffices τ.s a b = τ.s (τ v + 1) b by
      have h : τ.s (τ.func v + 1) b = τ.s (τ.func v) b + 1
        := (τ.a_step_one_iff' v b).mpr v_mem.1
      rw [this, h]
    unfold AspPerm.s
    suffices (τ.se a b) = (τ.se (τ.func v + 1) b) by rw [this]
    ext n; simp only [AspPerm.mem_se]
    have τv_lt_a : τ v < a := v_mem.2
    constructor <;> (intro ⟨n_ge_b, τn_lt⟩; use n_ge_b)
    · have := le_τv n ⟨n_ge_b, τn_lt⟩
      exact Int.le_iff_lt_add_one.mp this
    · have := Int.le_iff_lt_add_one.mpr τn_lt
      exact lt_of_le_of_lt this τv_lt_a

structure s'_witness (τ : AspPerm) (a b : ℤ) where
  u : ℤ
  s'_val : τ.s' b a = τ.s' b (τ u)
  mem_nw : u ∈ northwest_set τ a b

noncomputable def find_s'_witness {τ : AspPerm} {a b : ℤ} (hab : τ.s' b a ≥ 1) :
  s'_witness τ a b := by
  have nw_nonempty : (τ.nw a b).Nonempty := by
    dsimp [AspPerm.s'] at hab
    have : (τ.nw a b).card ≠ 0 := by linarith
    exact Finset.card_ne_zero.mp this
  have img_nonempty : (Finset.image τ (τ.nw a b)).Nonempty := by simp [nw_nonempty]
  let y := Finset.min' (Finset.image τ (τ.nw a b)) img_nonempty
  let u := τ⁻¹ y
  have y_mem : y ∈ τ '' northwest_set τ a b := by
    have h : y ∈ Finset.image τ (τ.nw a b) :=
      Finset.min'_mem (Finset.image τ (τ.nw a b)) img_nonempty
    simp [Finset.mem_image] at h
    exact h
  have u_mem : u ∈ northwest_set τ a b := by
    rcases y_mem with ⟨n, n_mem, y_eq⟩
    subst u; rw [← y_eq]; simp [n_mem]
  have ge_τu : ∀ n ∈ northwest_set τ a b, τ u ≤ τ n := by
    intro n n_mem
    subst u; simp
    apply Finset.min'_le
    rw [Finset.mem_image]
    use n
    simpa [AspPerm.mem_nw] using n_mem
  use u
  · -- s'_val : τ.s' b a = τ.s' b (τ u)
    unfold AspPerm.s'
    suffices τ.nw a b = τ.nw (τ.func u) b by rw [this]
    ext n; simp only [AspPerm.mem_nw]
    constructor
    · intro ⟨n_lt_b, τn_ge_a⟩
      exact ⟨n_lt_b, ge_τu n ⟨n_lt_b, τn_ge_a⟩⟩
    · intro ⟨n_lt_b, τn_ge_τu⟩
      exact ⟨n_lt_b, le_trans u_mem.2 τn_ge_τu⟩

lemma inv_of_quadrants {τ : AspPerm} {a b u v : ℤ}
  (hu : u ∈ northwest_set τ a b) (hv : v ∈ southeast_set τ a b) :
  ⟨u, v⟩ ∈ inv_set τ := by
  have u_lt_v : u < v := lt_of_lt_of_le hu.1 hv.1
  have τ_u_gt_v : τ v < τ u := lt_of_lt_of_le hv.2 hu.2
  exact ⟨u_lt_v, τ_u_gt_v⟩

section fixed_321a_and_lel
variable {β : AspPerm} (h_L : β ≤L τ)

lemma src_of_src {n : ℤ} (h_L : β ≤L τ) (h_src : is_src β n) : is_src τ n := by
  rcases h_src with ⟨v, h_inv⟩
  exact src_of_inv (h_L h_inv)

lemma snk_of_snk {n : ℤ} (h_L : β ≤L τ) (h_snk : is_snk β n) : is_snk τ n := by
  rcases h_snk with ⟨u, h_inv⟩
  exact snk_of_inv (h_L h_inv)

lemma is_321a_of_lel {β : AspPerm} (h_321a : is_321a τ)
  (h_L : β ≤L τ) : is_321a β := by
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

lemma between_inv_lel {β : AspPerm} (h_321a : is_321a τ) (h_L : β ≤L τ)
  {u x v : ℤ} (uv_inv : ⟨u, v⟩ ∈ inv_set β) (u_le_x : u ≤ x) (x_le_v : x ≤ v)
  : between_inv_lel_prop β τ u x v  := by
  have bp := between_inv h_321a (h_L uv_inv) u_le_x x_le_v
  have bpβ := between_inv (is_321a_of_lel h_321a h_L) uv_inv u_le_x x_le_v
  by_cases h_src : is_src β x
  · have h_ux : ⟨u, x⟩ ∉ inv_set τ := bp.src_iff_left_ninv.mp (src_of_src h_L h_src)
    have h_xv : ⟨x, v⟩ ∈ inv_set β := bpβ.src_iff_right_inv.mp h_src
    have h_ux_β : ⟨u, x⟩ ∉ inv_set β := by
      contrapose! h_ux
      exact h_L h_ux
    have x_src : is_src β x := src_of_inv h_xv
    have x_snk : ¬ is_snk τ x := not_imp_not.mpr bp.snk_iff_left_inv.mp h_ux
    have x_snk_β : ¬ is_snk β x := not_imp_not.mpr (snk_of_snk h_L) x_snk
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
    have h_xv : ⟨x, v⟩ ∉ inv_set τ := bp.snk_iff_right_ninv.mp (snk_of_snk h_L h_snk)
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

lemma inv_of_lel_iff {β : AspPerm} (h_321a : is_321a τ) (h_L : β ≤L τ)
  {u v u' v' : ℤ} (uv_inv : ⟨u, v⟩ ∈ inv_set β) (nested : ⟨u', v'⟩ ≼ ⟨u, v⟩) :
  ⟨u', v'⟩ ∈ inv_set β ↔ ⟨u', v'⟩ ∈ inv_set τ := by
  have h_321a_β := is_321a_of_lel (τ := τ) h_321a h_L
  wlog u'_lt_v' : u' < v'
  · constructor <;> (intro u'v'_inv; have := u'v'_inv.1; contradiction)
  -- Do the easy direction first
  constructor
  · intro h
    exact h_L h
  -- Now focus on the converse
  intro u'v'_inv

  have u'_src_τ : is_src τ u' := src_of_inv u'v'_inv
  have bpu' : between_inv_lel_prop β τ u u' v := between_inv_lel h_321a h_L
    uv_inv nested.1 (le_trans (le_of_lt u'v'_inv.1) nested.2)
  have u'_src : is_src β u' := bpu'.src_iff.mpr u'_src_τ
  have u'v_inv : ⟨u', v⟩ ∈ inv_set β := bpu'.propβ.src_iff_right_inv.mp u'_src

  have v'_snk_τ : is_snk τ v' := snk_of_inv u'v'_inv
  have bpv' : between_inv_lel_prop β τ u' v' v := between_inv_lel h_321a h_L
    u'v_inv (le_of_lt u'v'_inv.1) nested.2
  have v'_snk : is_snk β v' := bpv'.snk_iff.mpr v'_snk_τ
  have u'v'_inv : ⟨u', v'⟩ ∈ inv_set β := bpv'.propβ.snk_iff_left_inv.mp v'_snk

  exact u'v'_inv

lemma set_321a_of_func (avset : set_321a) : set_321a_prop (inv_set avset.to_func) := by
  constructor
  · show AspSet_prop (inv_set avset.to_func)
    rw [avset.invSet_func]
    refine avset.prop
  · simp [avset.prop_321a.tfree, avset.invSet_func]



lemma snk_lt {τ : AspPerm} (h_321a : is_321a τ)
  {v x : ℤ} (v_snk : is_snk τ v) (v_lt_x : v < x) :
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

lemma src_gt {τ : AspPerm} (h_321a : is_321a τ)
  {u x : ℤ} (u_src : is_src τ u) (x_lt_u : x < u) :
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

theorem eq_s_of_lel {β : AspPerm} (h_321a : is_321a τ) (h_L : β ≤L τ)
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
    have β_lt: β v < β x := snk_lt (is_321a_of_lel h_321a h_L) v_snk v_lt_x
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
lemma eq_s'_of_lel {β : AspPerm} (h_321a : is_321a τ) (h_L : β ≤L τ)
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
    have β_gt: β x < β u := src_gt (is_321a_of_lel h_321a h_L) u_src x_lt_u
    have τ_gt : τ x < τ u := src_gt h_321a (src_of_inv <| h_L uv_inv) x_lt_u
    constructor <;> (intro h; linarith)

  suffices ⟨u, x⟩ ∈ inv_set β ↔ ⟨u, x⟩ ∈ inv_set τ by
    rw [β.inv_iff_lt u_le_x, τ.inv_iff_lt u_le_x] at this
    constructor <;> (intro h; contrapose! h; rwa [this] at *)
  have nested : ⟨u, x⟩ ≼ ⟨u, v⟩ := by constructor <;> linarith
  exact inv_of_lel_iff h_321a h_L uv_inv nested

lemma uv_eq_of_lel (h_321a : is_321a τ) (h_L : β ≤L τ)
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
    rw [eq_s_of_lel h_321a h_L uv_inv u_lt_b, s_eq]
  have n_eq : β.s' b (β u) = n := by
    rw [eq_s'_of_lel h_321a h_L uv_inv b_le_v, s'_eq]

  exact ⟨ (β.u_crit b n_pos u).mpr ⟨n_eq, u_lt_b⟩,
    (β.v_crit b m_pos v).mpr ⟨m_eq, b_le_v⟩ ⟩

-- Almost identical to the above, but with β.u and β.v instead of τ.u and τ.v.
-- Can these be unified compactly?
lemma uv_eq_of_lel' (h_321a : is_321a τ) (h_L : β ≤L τ)
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
    rw [← eq_s_of_lel h_321a h_L uv_inv u_lt_b, s_eq]
  have n_eq : τ.s' b (τ u) = n := by
    rw [← eq_s'_of_lel h_321a h_L uv_inv b_le_v, s'_eq]

  exact ⟨ (τ.u_crit b n_pos u).mpr ⟨n_eq, u_lt_b⟩,
    (τ.v_crit b m_pos v).mpr ⟨m_eq, b_le_v⟩ ⟩

theorem lel_ramp (h_321a : is_321a τ) (h_L : β ≤L τ)
  (b : ℤ) {m n : ℤ} (m_pos : m > 0) (n_pos : n > 0) :
  ⟨τ.u b n_pos, τ.v b m_pos⟩ ∈ inv_set β
  ↔ ⟨m, n⟩ ∈ β.ramp b
  := by
  rw [β.inv_ramp_correspondence b m_pos n_pos]
  constructor
  · intro uv_inv
    have uv_eq := uv_eq_of_lel h_321a h_L b m_pos n_pos uv_inv
    rwa [← uv_eq.1, ← uv_eq.2]
  · intro uv_inv
    have uv_eq := uv_eq_of_lel' h_321a h_L b m_pos n_pos uv_inv
    rwa [← uv_eq.1, ← uv_eq.2]

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

theorem inv_of_lel_iff_ramp {β : AspPerm} (h_321a : is_321a τ) (h_L : β ≤L τ)
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

  rw [← lel_ramp h_321a h_L b m_pos n_pos]
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

end fixed_321a_and_lel

section factorization
variable (τ α β : AspPerm) (h_R : α ≤R τ) (h_L : β ≤L τ) (h_χ : τ.χ = α.χ + β.χ)

-- "Slide right" inversions from α to inversions of τ
noncomputable def sr : (ℤ × ℤ) → (ℤ × ℤ) := fun x => ⟨ τ⁻¹ (α x.1), τ⁻¹ (α x.2) ⟩

lemma sr_crit : ∀ (u v : ℤ),  ⟨u, v⟩ ∈ (sr τ α) '' inv_set α ↔ ⟨τ v, τ u⟩ ∈ inv_set α⁻¹.func := by
  intro u v
  constructor
  · intro h
    rcases h with ⟨⟨u, v⟩, uv_inv, xy_inv, rfl⟩
    simp only [τ.mul_inv_cancel_eval]
    exact (α.inv_set_inverse u v).mp uv_inv
  · intro h
    use ⟨α⁻¹ (τ u), α⁻¹ (τ v)⟩
    constructor
    · have := (α⁻¹.inv_set_inverse (τ v) (τ u)).mp h
      simpa
    · unfold sr
      simp

lemma split_s {τ : AspPerm} (h_321a : is_321a τ) {u v : ℤ} {a b : ℤ}
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

lemma inversion_in_union (h_321a : is_321a τ) (h_R : α ≤R τ) (h_L : β ≤L τ)
  (a b u v : ℤ) (h_χ : τ.χ = α.χ + β.χ)
  (dprod : α.dprod_geq β a b (τ.s a b)) :
  u < b → b ≤ v → τ u ≥ a → τ v < a
  → ⟨u, v⟩ ∈ (sr τ α) '' (inv_set α) ∪ inv_set β := by
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
    apply (inv_of_lel_iff_ramp h_321a h_L u_lt_b b_le_v).mpr
    rw [τ.dual_inverse]
    convert hβ
    rw [m_eq]
  · left
    have := α⁻¹.ramp_lamp_dual a (N+1-n) (M+1-m)
    rw [inv_inv] at this
    rw [← this] at hα

    have h : (τ v, τ u) ∈ inv_set α⁻¹.func ↔ (τ⁻¹.s u a + 1, τ.s a v) ∈ α⁻¹.ramp a := by
      have := inv_of_lel_iff_ramp (inv_is_321a h_321a) h_R τv_lt_a τu_ge_a
      rw [τ⁻¹.dual_inverse, inv_inv] at this
      simpa using this

    have : τ⁻¹.s u a + 1 = N + 1 - n ∧ τ.s a v = M + 1 - m := by
      constructor
      · have : τ⁻¹ (τ u) < b ∧ τ⁻¹ (τ v) ≥ b := by
          constructor <;> (simp; assumption)
        have := split_s (inv_is_321a h_321a) τv_lt_a τu_ge_a this.1 this.2
        simp [τ.inv_mul_cancel_eval] at this
        linarith [this]
      · linarith [split_s h_321a u_lt_b b_le_v τv_lt_a τu_ge_a]

    rw [this.1, this.2] at h
    apply h.mpr at hα

    exact (sr_crit τ α u v).mpr hα


end factorization

end fixed_321a
end ASP321a
