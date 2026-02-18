import Mathlib
import Demazure.AspPerm
import Demazure.InvSet
import Demazure.Utils

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

lemma inv_between {τ : AspPerm} (h_321a : is_321a τ) {u x v : ℤ}
  (u_le_x : u ≤ x) (x_le_v : x ≤ v) (uv_inv : ⟨u, v⟩ ∈ inv_set τ) :
  ⟨u, x⟩ ∈ inv_set τ ↔ ⟨x, v⟩ ∉ inv_set τ := by
  have h : ⟨u, x⟩ ∈ inv_set τ ∨ ⟨x, v⟩ ∈ inv_set τ  := by
    by_contra! not_inv
    obtain ⟨ux_ninv, xv_ninv⟩ := not_inv
    have x_lt_v : x < v := by
      by_contra! h
      have : x = v := le_antisymm x_le_v h
      rw [this] at ux_ninv
      contradiction
    have u_lt_x : u < x := by
      by_contra! h
      have : u = x := le_antisymm u_le_x h
      rw [← this] at xv_ninv
      contradiction
    absurd uv_inv
    apply (AspSet.of_AspPerm τ).prop.coclosed u x v <;> assumption
  rcases h with (ux_inv | xv_inv)
  · suffices ⟨x, v⟩ ∉ inv_set τ by simp [this, ux_inv]
    intro xv_inv
    have := tfree_of_321a τ h_321a u x v
    rcases this <;> contradiction
  · suffices ⟨u, x⟩ ∉ inv_set τ by simp [this, xv_inv]
    have := tfree_of_321a τ h_321a u x v
    intro vu_inv
    rcases this <;> contradiction

def is_src (τ : AspPerm) (u : ℤ) : Prop :=
  ∃ v : ℤ, ⟨u, v⟩ ∈ inv_set τ

def src_of_inv {τ : AspPerm} {u v : ℤ} (uv_inv : ⟨u, v⟩ ∈ inv_set τ) :
  is_src τ u := by use v

def is_snk (τ : AspPerm) (v : ℤ) : Prop :=
  ∃ u : ℤ, (u, v) ∈ inv_set τ

def snk_of_inv {τ : AspPerm} {u v : ℤ} (uv_inv : ⟨u, v⟩ ∈ inv_set τ) :
  is_snk τ v := by use u

lemma not_src_and_snk {τ : AspPerm} (h_321a : is_321a τ) (n : ℤ) :
  ¬ (is_src τ n) ∨ ¬(is_snk τ) n := by
  by_contra!
  obtain ⟨h_src, h_snk⟩ := this
  rcases h_snk with ⟨u, hu⟩
  rcases h_src with ⟨v, hv⟩
  have := tfree_of_321a τ h_321a u n v
  rcases this <;> contradiction

lemma is_321a_of_lel {β τ : AspPerm} (h_321a : is_321a τ)
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

lemma inv_lel_between {β τ : AspPerm} (h_321a : is_321a τ) (h_L : β ≤L τ)
  {u x v : ℤ} (uv_inv : ⟨u, v⟩ ∈ inv_set β) (u_le_x : u ≤ x) (x_le_v : x ≤ v) :
  (is_src τ x → ⟨x, v⟩ ∈ inv_set β) ∧ (is_snk τ x → ⟨u, x⟩ ∈ inv_set β) := by
  have h_321a_β : is_321a β := is_321a_of_lel h_321a h_L
  have hiff := inv_between h_321a_β u_le_x x_le_v uv_inv
  have not_both : is_src τ x → ¬ (is_snk τ x) := by
    intro hsrc hsnk
    have := not_src_and_snk h_321a x
    rcases this <;> contradiction
  constructor
  · intro h_src
    apply not_both at h_src
    contrapose! h_src with h_ninv
    exact snk_of_inv <| h_L <| hiff.mpr h_ninv
  · intro h_snk
    apply hiff.mpr
    intro h_inv
    exact not_both (src_of_inv <| h_L h_inv) h_snk

lemma set_321a_of_func (avset : set_321a) : set_321a_prop (inv_set avset.to_func) := by
  constructor
  · show AspSet_prop (inv_set avset.to_func)
    rw [avset.invSet_func]
    refine avset.prop
  · simp [avset.prop_321a.tfree, avset.invSet_func]

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

lemma sink_lt {τ : AspPerm} (h_321a : is_321a τ)
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

lemma source_gt {τ : AspPerm} (h_321a : is_321a τ)
  {u v x : ℤ} (uv_inv : ⟨u, v⟩ ∈ inv_set τ) (x_lt_u : x < u) :
  τ x < τ u := by
  by_contra! h
  have : ⟨x, u⟩ ∈ inv_set τ := by
    use x_lt_u
    refine lt_of_le_of_ne h ?_
    intro heq
    apply τ.injective at heq
    rw [heq] at x_lt_u
    exact lt_irrefl x x_lt_u
  have := tfree_of_321a τ h_321a x u v
  rcases this <;> contradiction

lemma eq_s_of_lel {β τ : AspPerm} (h_321a : is_321a τ) (h_L : β ≤L τ)
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
    have := h_L uv_inv

    have h1 : β v ≤ β x := le_of_lt <|
      sink_lt (is_321a_of_lel h_321a h_L) (snk_of_inv uv_inv) v_lt_x
    have h2 : τ v ≤ τ x := le_of_lt <|
      sink_lt h_321a (snk_of_inv <| h_L uv_inv) v_lt_x
    constructor <;> (intro h; linarith)

  have hβ := inv_between (is_321a_of_lel h_321a h_L) (le_of_lt u_lt_x) x_le_v uv_inv
  have hτ := inv_between h_321a (le_of_lt u_lt_x) x_le_v (h_L uv_inv)

  constructor
  · intro β_x_lt_v
    have x_ne_v : x ≠ v := by
      intro heq
      rw [heq] at β_x_lt_v
      exact lt_irrefl (β v) β_x_lt_v
    have xv_ninv : ⟨x, v⟩ ∉ inv_set β := by
      intro h
      exact lt_irrefl (β v) <| lt_trans h.2 β_x_lt_v
    have := hτ.mp <| h_L <| hβ.mpr xv_ninv
    contrapose! this with τ_v_le_x
    exact (τ.inv_iff_le (lt_of_le_of_ne x_le_v x_ne_v)).mpr τ_v_le_x
  · intro τ_x_lt_v
    have x_lt_v : x < v := by
      by_contra! h
      have : x = v := le_antisymm x_le_v h
      rw [this] at τ_x_lt_v; exact lt_irrefl (τ v) τ_x_lt_v
    contrapose! τ_x_lt_v with β_v_le_x
    have xv_inv : ⟨x, v⟩ ∈ inv_set τ :=
      h_L <| (β.inv_iff_le x_lt_v).mpr β_v_le_x
    exact le_of_lt xv_inv.2

-- This is roughly a repeat of the proof above. Can it be unified with it somehow?
lemma eq_s'_of_lel {β τ : AspPerm} (h_321a : is_321a τ) (h_L : β ≤L τ)
  {u b v : ℤ} (uv_inv : ⟨u, v⟩ ∈ inv_set β) (b_le_v : b ≤ v) :
  β.s' b (β u) = τ.s' b (τ u) := by
  unfold AspPerm.s'
  suffices β.nw (β u) b = τ.nw (τ u) b by
    rw [this]
  ext x
  suffices x < b → (β x ≥ β u ↔ τ x ≥ τ u) by
    simpa [AspPerm.nw, northwest_set, this]
  intro x_lt_b
  wlog x_ne_u : x ≠ u
  · have heq : x = u := by
      contrapose! x_ne_u; assumption
    rw [heq]
    simp
  wlog x_gt_u : x > u
  · have x_lt_u : x < u := by
      push_neg at x_gt_u
      exact lt_of_le_of_ne x_gt_u x_ne_u
    have := h_L uv_inv
    have h1 : β x < β u := source_gt (is_321a_of_lel h_321a h_L) uv_inv x_lt_u
    have h2 : τ x < τ u := source_gt h_321a (h_L uv_inv) x_lt_u
    constructor <;> (intro h; linarith)

  have hβ : (u, x) ∈ inv_set β.func ↔ (x, v) ∉ inv_set β.func :=
    inv_between (is_321a_of_lel h_321a h_L) (le_of_lt x_gt_u)
      (le_of_lt <| lt_of_lt_of_le x_lt_b b_le_v) uv_inv
  have hτ : (u, x) ∈ inv_set τ.func ↔ (x, v) ∉ inv_set τ.func :=
    inv_between h_321a (le_of_lt x_gt_u)
      (le_of_lt <| lt_of_lt_of_le x_lt_b b_le_v) (h_L uv_inv)

  constructor
  · intro β_x_ge_u
    have xu_inv : ⟨u, x⟩ ∉ inv_set β := by
      intro h
      have := (β.inv_iff_lt (le_of_lt x_gt_u)).mp h
      linarith
    suffices ⟨u, x⟩ ∉ inv_set τ by
      have h := (τ.inv_iff_lt (le_of_lt x_gt_u)).mpr
      contrapose! this with τ_x_lt_u
      exact h τ_x_lt_u
    contrapose! xu_inv with ux_inv
    apply hβ.mpr
    intro xu_inv_β
    exact (hτ.mp ux_inv) (h_L xu_inv_β)
  · intro τ_x_ge_u
    have xu_inv : ⟨u, x⟩ ∉ inv_set τ := by
      contrapose! τ_x_ge_u with ux_inv
      exact (τ.inv_iff_lt (le_of_lt x_gt_u)).mp ux_inv
    contrapose! xu_inv with β_x_lt_u
    exact h_L <| (β.inv_iff_lt (le_of_lt x_gt_u)).mpr β_x_lt_u

theorem inv_of_lel_iff_ramp {β τ : AspPerm} (h_321a : is_321a τ) (h_L : β ≤L τ)
  {u b v : ℤ} (uv_inv : ⟨u, v⟩ ∈ inv_set τ) (u_lt_b : u < b) (b_le_v : b ≤ v) :
    ⟨u, v⟩ ∈ inv_set β
    ↔ ⟨τ.s (τ v) b + 1, τ.s' b (τ u)⟩ ∈ β.ramp b
  := by
  have h_321a_β := is_321a_of_lel h_321a h_L
  constructor
  · intro uv_inv_β
    let l₁ := β u
    let l₂ := β v + 1
    have l₂_le_l₁ : l₂ ≤ l₁ := uv_inv_β.2
    use l₁
    constructor
    · suffices β.s l₂ b ≥ τ.s (τ.func v) b + 1 by
        apply le_trans this
        exact (β.s_nondec l₂_le_l₁ b).1
      simp only [l₂]
      have : β.s (β.func v + 1) b = β.s (β.func v) b + 1 := by
        rw [β.a_step (β v) b, β.inv_mul_cancel_eval]
        simp [b_le_v]
      rw [this]
      rw [eq_s_of_lel h_321a h_L uv_inv_β u_lt_b]
    · rw [eq_s'_of_lel h_321a h_L uv_inv_β b_le_v]
  · intro mem_ramp
    rcases mem_ramp with ⟨l, ⟨hm,hn⟩⟩
    -- Define u' to be the first source that actually lies in the quadrant
    have : (β.nw l b).Nonempty := by
      suffices β.s' b l ≥ 1 by simpa [AspPerm.s', this]
      suffices τ.s' b (τ u) > 0 by linarith
      suffices (τ.nw (τ u) b).Nonempty by
        unfold AspPerm.s'
        simp [this]
      use u; simp [u_lt_b]
    let u' := (Finset.min' <| β.nw l b) this
    have : u' ∈ northwest_set β l b := by
      have : u' ∈ β.nw l b := (β.nw l b).min'_mem this
      simp at this ⊢; exact this
    obtain ⟨u'_lt_b, l_le_βu'⟩ := this

    -- Define v' to the be first sink that actually lies in the quadrant
    have : (β.se l b).Nonempty := by
      suffices β.s l b ≥ 1 by simpa [AspPerm.s, this]
      have : τ.s (τ v) b ≥ 0 := by simp [AspPerm.s]
      linarith
    let v' := (Finset.max' <| β.se l b) this
    have : v' ∈ southeast_set β l b := by
      have : v' ∈ β.se l b := (β.se l b).max'_mem this
      simp at this ⊢; exact this
    obtain ⟨b_le_v', βv'_lt_l⟩ := this

    have u'v'_inv : ⟨u', v'⟩ ∈ inv_set β :=
      ⟨lt_of_lt_of_le u'_lt_b b_le_v', lt_of_lt_of_le βv'_lt_l l_le_βu'⟩

    have : τ.s (τ v) b ≤ τ.s (τ v') b := by
      suffices τ.s (τ v) b + 1 ≤ τ.s (τ v') b + 1 by linarith
      calc
        τ.s (τ v) b + 1 ≤ β.s l b := hm
        _ = β.s (β v' + 1) b := by
          have : β v' + 1 ≤ l := by linarith
          apply Eq.symm
          apply (β.s_nondec this b).2.mpr
          intro x βv'_lt_βx βx_lt_l
          contrapose! βv'_lt_βx with x_ge_b
          obtain x_ge_b : x ≥ b := x_ge_b
          have x_mem : x ∈ β.se l b := by
            simp only [β.mem_se]
            exact ⟨x_ge_b, βx_lt_l⟩
          simp only [β.mem_se] at x_mem
          have x_le_v' : x ≤ v'  := by
            apply Finset.le_max' _ x
            simp only [β.mem_se]
            constructor <;> assumption
          by_contra! βv'_lt_βx

          have xv'_inv : ⟨x, v'⟩ ∈ inv_set β := by
            apply (β.inv_iff_lt x_le_v').mpr
            linarith
          suffices ⟨u',x⟩ ∈ inv_set β by
            have := tfree_of_321a β h_321a_β u' x v'
            rcases this <;> contradiction
          exact ⟨lt_of_lt_of_le u'_lt_b x_ge_b, lt_of_lt_of_le βx_lt_l l_le_βu'⟩
        _ = β.s (β v') b + 1 := by
          rw [β.a_step (β v') b, β.inv_mul_cancel_eval]
          simp [b_le_v']
        _ = τ.s (τ v') b + 1 := by
          have := eq_s_of_lel h_321a h_L u'v'_inv u'_lt_b
          linarith
    have v_le_v' : v ≤ v' := by
      by_contra! v'_lt_v
      have τ_v'_lt_v : τ v' < τ v := sink_lt h_321a (snk_of_inv <| h_L u'v'_inv) v'_lt_v
      have h := (τ.s_nondec (le_of_lt τ_v'_lt_v) b)
      have : τ.s (τ v') b = τ.s (τ v) b := le_antisymm h.1 this
      have : v' < b := h.2.mp this v' (le_refl _) τ_v'_lt_v
      exact lt_iff_not_ge.mp this b_le_v'

    -- Now do the whole dance again with u'! Woof.
    have : τ.s' b (τ u) ≤ τ.s' b (τ u') := by
      calc
        τ.s' b (τ u) ≤ β.s' b l := hn
        _ = β.s' b (β u') := by
          rw [AspPerm.dual_inverse, (β⁻¹.s_noninc b (l_le_βu')).2]
          intro y l_le_y y_lt_βu'
          let x := β⁻¹ y
          have y_eq : y = β x := by
            simp only [x]; rw [β.mul_inv_cancel_eval y]
          rw [y_eq] at l_le_y y_lt_βu' ⊢; simp only [β.inv_mul_cancel_eval]
          contrapose! y_lt_βu' with x_lt_b
          have x_nw : x ∈ β.nw l b := by
            simp only [β.mem_nw]
            exact ⟨x_lt_b, l_le_y⟩
          have u'_le_x : u' ≤ x := by
            dsimp [u']
            exact Finset.min'_le _ _ x_nw
          have : ⟨x, v'⟩ ∈ inv_set β := by
            use lt_of_lt_of_le x_lt_b b_le_v', lt_of_lt_of_le βv'_lt_l l_le_y
          contrapose! this with β_x_lt_u'
          have u'x_inv : ⟨u', x⟩ ∈ inv_set β := (β.inv_iff_lt u'_le_x).mpr β_x_lt_u'
          have := inv_between h_321a_β  u'_le_x (le_trans (le_of_lt x_lt_b) b_le_v') u'v'_inv
          exact this.mp u'x_inv
        _ = τ.s' b (τ u') := by
          exact eq_s'_of_lel h_321a h_L u'v'_inv b_le_v'

    have u'_le_u : u' ≤ u := by
      by_contra! u_lt_u'
      have τ_u'_lt_u : τ u < τ u' := by
        exact source_gt h_321a (h_L u'v'_inv) u_lt_u'
      have mono := (τ⁻¹.s_noninc b (le_of_lt τ_u'_lt_u))
      have : τ⁻¹.s b (τ u) = τ⁻¹.s b (τ u') := by
        rw [τ.dual_inverse] at this
        exact le_antisymm this mono.1
      have b_le_u : b ≤ u := by
        have := mono.2.mp this (τ u) (le_refl _) τ_u'_lt_u
        simpa [this]
      linarith

    have : ⟨u', v⟩ ∈ inv_set β := by
      have u'_le_v := le_trans (le_of_lt u'_lt_b) b_le_v
      have helper := inv_lel_between h_321a h_L u'v'_inv u'_le_v v_le_v'
      exact helper.2 (snk_of_inv uv_inv)

    have u_le_v : u ≤ v := le_trans (le_of_lt u_lt_b) b_le_v
    have helper := inv_lel_between h_321a h_L this u'_le_u u_le_v
    exact helper.1 (src_of_inv uv_inv)

end ASP321a
