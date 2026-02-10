import Mathlib
import Demazure.Basic
import Demazure.Utils

structure AspSet_prop (I : Set (ℤ × ℤ)) where
  directed :
    (∀ u v : ℤ, ⟨u, v⟩ ∈ I → u < v)
  closed:
    (∀ u v w : ℤ, (u, v) ∈ I → (v, w) ∈ I → ⟨u, w⟩ ∈ I)
  coclosed:
    (∀ u v w : ℤ, (u < v) → (v < w) → (u, v) ∉ I → (v, w) ∉ I → ⟨u, w⟩ ∉ I)
  finite_outdegree:
    (∀ u : ℤ, { v : ℤ | ⟨u, v⟩ ∈ I }.Finite)
  finite_indegree:
    (∀ v : ℤ, { u : ℤ | ⟨u, v⟩ ∈ I }.Finite)

structure AspSet where
  I : Set (ℤ × ℤ)
  prop : AspSet_prop I

namespace AspSet

abbrev directed (as : AspSet) := as.prop.directed
abbrev closed (as : AspSet) := as.prop.closed
abbrev coclosed (as : AspSet) := as.prop.coclosed
abbrev finite_outdegree (as : AspSet) := as.prop.finite_outdegree
abbrev finite_indegree (as : AspSet) := as.prop.finite_indegree


lemma AspSet_InvSet_of_AspPerm (τ : AspPerm) : AspSet_prop τ.inv := by
  constructor
  · intro u v uv_inv
    exact uv_inv.1
  · intro u v w uv_inv vw_inv
    have h1 := lt_trans uv_inv.1 vw_inv.1
    have h2 := lt_trans vw_inv.2 uv_inv.2
    exact ⟨h1, h2⟩
  · intro u v w u_lt_v v_lt_w uv_inv vw_inv
    have h1 : u < w := lt_trans u_lt_v v_lt_w
    have h2 : τ.func u ≤ τ.func v := by
      contrapose! uv_inv
      exact ⟨u_lt_v, uv_inv⟩
    have h3 : τ.func v ≤ τ.func w := by
      contrapose! vw_inv
      exact ⟨v_lt_w, vw_inv⟩
    have h4 := le_trans h2 h3
    contrapose! h4
    exact h4.2
  · show ∀ (u : ℤ), {v | (u, v) ∈ τ.inv}.Finite
    unfold AspPerm.inv inv_set; simp
    intro u
    suffices {v | u < v ∧ τ.func v < τ.func u} = southeast_set τ.func (τ.func u) (u+1) by
      rw [this]
      apply se_finite_of_asp τ.bijective.injective
      exact τ.asp
    unfold southeast_set
    tauto
  · show ∀ (v : ℤ), {u | (u, v) ∈ τ.inv}.Finite
    unfold AspPerm.inv inv_set; simp
    intro v
    suffices {u | u < v ∧ τ.func u > τ.func v} = northwest_set τ.func (τ.func v + 1) v by
      rw [this]
      apply nw_finite_of_asp τ.bijective.injective
      exact τ.asp
    unfold northwest_set
    tauto

def of_AspPerm (τ : AspPerm) : AspSet :=
  ⟨τ.inv, AspSet_InvSet_of_AspPerm τ⟩

noncomputable section
abbrev inset (as : AspSet) (n : ℤ) : Finset ℤ := (as.finite_indegree n).toFinset

abbrev outset (as : AspSet) (n : ℤ) : Finset ℤ := (as.finite_outdegree n).toFinset

@[simp] lemma mem_inset (as : AspSet) (n x : ℤ) : x ∈ as.inset n ↔ ⟨x, n⟩ ∈ as.I := by
  simp [inset]

@[simp] lemma mem_outset (as : AspSet) (n x : ℤ) : x ∈ as.outset n ↔ ⟨n, x⟩ ∈ as.I := by
  simp [outset]

def to_func (as : AspSet) : ℤ → ℤ :=
  fun n => n + (as.outset n).card - (as.inset n).card

section σ_diff
variable (as : AspSet) (m n : ℤ)
abbrev σ := as.to_func

abbrev lf_pos : Finset ℤ := as.inset m \ as.inset n
@[simp] lemma mem_lf_pos (x : ℤ) : x ∈ lf_pos as m n
    ↔ x < m ∧ ⟨x, m⟩ ∈ as.I ∧ ⟨x, n⟩ ∉ as.I := by
  simp [lf_pos]
  intro hm hn
  exact as.directed x m hm

abbrev md_pos : Finset ℤ := (Finset.Ico m n) \ (as.outset m ∪ as.inset n)
@[simp] lemma mem_md_pos (x : ℤ) : x ∈ md_pos as m n
    ↔ m ≤ x ∧ x < n ∧ ⟨m, x⟩ ∉ as.I ∧ ⟨x, n⟩ ∉ as.I := by
  simp [md_pos]
  constructor
  · intro h
    obtain ⟨x_ge_m, x_lt_n⟩ := h.1
    simp [x_ge_m, x_lt_n, h]
  · intro h
    obtain ⟨x_ge_m, x_lt_n, x_outm, x_inn⟩ := h
    simp [x_ge_m, x_lt_n, x_outm, x_inn]

abbrev rt_pos : Finset ℤ := as.outset n \ as.outset m
@[simp] lemma mem_rt_pos (x : ℤ) : x ∈ rt_pos as m n
    ↔ x ≥ n ∧ ⟨m,x⟩ ∉ as.I ∧ ⟨n,x⟩ ∈ as.I := by
  simp [rt_pos]
  constructor
  · intro h
    simp [h]
    exact le_of_lt (as.directed n x h.1)
  · intro h
    simp [h]

abbrev lf_neg : Finset ℤ := (as.inset n \ as.inset m).filter (· < m)
@[simp] lemma mem_lf_neg (x : ℤ) : x ∈ lf_neg as m n
    ↔ x < m ∧ ⟨x, m⟩ ∉ as.I ∧ ⟨x, n⟩ ∈ as.I := by
  simp [lf_neg]
  constructor <;> (intro h; simp [h])

abbrev md_neg : Finset ℤ := (Finset.Ico m n) ∩ (as.outset m ∩ as.inset n)
@[simp] lemma mem_md_neg (x : ℤ) : x ∈ md_neg as m n
    ↔ m ≤ x ∧ x < n ∧ ⟨m, x⟩ ∈ as.I ∧ ⟨x, n⟩ ∈ as.I := by
  simp [md_neg]
  constructor <;> (intro h; simp [h])

abbrev rt_neg : Finset ℤ := (as.outset m \ as.outset n).filter (· ≥  n)
@[simp] lemma mem_rt_neg (x : ℤ) : x ∈ rt_neg as m n
    ↔ x ≥ n ∧ ⟨m,x⟩ ∈ as.I ∧ ⟨n,x⟩ ∉ as.I := by
  simp [rt_neg]
  constructor <;> (intro h; simp [h])

lemma σ_diff (m_le_n : m ≤ n) : σ as n - σ as m =
  ((lf_pos as m n).card + (md_pos as m n).card + (rt_pos as m n).card)
  - ((lf_neg as m n).card + (md_neg as m n).card + (rt_neg as m n).card) := by

  have : σ as n - σ as m =
    (Finset.Ico m n).card
    + ( (as.outset n) \ (as.outset m)).card  - ( (as.outset m) \ (as.outset n)).card
    + ( (as.inset m) \ (as.inset n)).card - ( (as.inset n) \ (as.inset m)).card := by
    unfold σ to_func
    have h1 := Utils.sub_card_eq_sub_card_diff (as.outset n) (as.outset m)
    have h2 := Utils.sub_card_eq_sub_card_diff (as.inset m) (as.inset n)
    have h3 : (Finset.Ico m n).card = n-m := by
      simp [m_le_n]
    linarith [h1,h2,h2]
  rw [this]

  have rp : (as.outset n \ as.outset m) = rt_pos as m n := by simp
  have lp : (as.inset m \ as.inset n) = lf_pos as m n := by simp
  have rn :
    (as.outset m \ as.outset n).card
    = ( (Finset.Ico m n) ∩ (as.outset m) ).card + (rt_neg as m n).card := by
    let A := (Finset.Ico m n) ∩ (as.outset m)
    let B := rt_neg as m n
    have : Disjoint A B := by
      rw [Finset.disjoint_iff_ne]
      rintro a ha b hb
      unfold A at ha; simp at ha
      unfold B at hb; simp at hb
      linarith
    rw [← Finset.card_union_of_disjoint this]
    suffices (A ∪ B) = (as.outset m \ as.outset n) by
      rw [this]
    ext x
    unfold A B
    simp
    constructor
    · intro hx
      rcases hx with (hA | hB)
      · simp [hA]
        intro h
        have : n < x := as.directed n x h
        linarith
      · tauto
    · intro h
      simp [h, le_of_lt (as.directed m x h.1)]
      exact lt_or_ge x n
  have ln : (as.inset n \ as.inset m).card
    = ( (Finset.Ico m n) ∩ (as.inset n) ).card + (lf_neg as m n).card := by
    let A := (Finset.Ico m n) ∩ (as.inset n)
    let B := lf_neg as m n
    have : Disjoint A B := by
      rw [Finset.disjoint_iff_ne]
      rintro a ha b hb
      unfold A at ha; simp at ha
      unfold B at hb; simp at hb
      intro a_eq_b
      linarith
    have := Finset.card_union_of_disjoint this
    rw [← this]
    suffices (A ∪ B) = (as.inset n \ as.inset m) by
      rw [this]
    ext x
    unfold A B; simp
    constructor
    · intro hx
      rcases hx with (hA | hB)
      · suffices ⟨x, m⟩ ∉ as.I by tauto
        intro xm_I
        apply as.directed x m at xm_I
        linarith
      · tauto
    · intro h
      have x_lt_n : x < n := as.directed x n h.1
      simp [h, x_lt_n]
      exact le_or_gt m x
  suffices ((Finset.Ico m n).card : ℤ)
    - ↑(md_pos as m n).card
    = ( (Finset.Ico m n) ∩ (as.outset m) ).card
    + ( (Finset.Ico m n) ∩ (as.inset n) ).card
    - ↑(md_neg as m n).card
    by
    rw [rp, lp, rn, ln]
    simp only [Nat.cast_add]
    linarith [this]

  unfold md_pos md_neg
  let U := (Finset.Ico m n)
  let A := U ∩ as.outset m
  let B := U ∩ as.inset n
  have h_diff : (U \ (A ∪ B)) = (Finset.Ico m n \ (as.outset m ∪ as.inset n)) := by
    ext x
    unfold A B U
    simp; tauto
  have h_inter : (A ∩ B) = (Finset.Ico m n ∩ (as.outset m ∩ as.inset n)) := by
    ext x
    unfold A B U; simp; tauto
  suffices (U.card : ℤ) = (U \ (A ∪ B)).card + A.card + B.card - (A ∩ B).card by
    rw [h_diff, h_inter] at this
    unfold U A B at this
    linarith [this]

  have h_union : (A.card : ℤ) + (B.card : ℤ) - (A ∩ B).card = (A ∪ B).card := by
    simp only [Finset.card_union A B]
    suffices A.card + B.card ≥ (A ∩ B).card by
      simp [this]
    have : A ∩ B ⊆ A := by apply Finset.inter_subset_left
    have : (A ∩ B).card ≤ A.card := Finset.card_le_card this
    linarith [this]

  have h_diff : ((U \ (A ∪ B)).card : ℤ) = U.card - (A ∪ B).card := by
    have : A ∪ B ⊆ U := by
      unfold A B U
      intro x hx
      simp at hx ⊢; tauto
    simp only [Finset.card_sdiff_of_subset this]
    suffices A ∪ B ⊆ U by
      simp [Finset.card_le_card this]
    intro x hx
    unfold A B at hx
    simp at hx; tauto
  linarith [h_diff, h_union]

lemma σ_diff_pos (m_lt_n : m < n) (mn_I : ⟨m, n⟩ ∉ as.I) :
  σ as n - σ as m = ↑(as.lf_pos m n).card + ↑(as.md_pos m n).card + ↑(as.rt_pos m n).card := by
  have diff := σ_diff as m n (le_of_lt m_lt_n)
  have h_lf : as.lf_neg m n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    simp at hx
    have := as.coclosed x m n
    tauto
  have h_md : as.md_neg m n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    simp at hx
    have := as.closed m x n
    tauto
  have h_rt : as.rt_neg m n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    simp at hx
    have : n ≠ x := by
      intro h_eq
      rw [← h_eq] at hx
      exact mn_I hx.1.1
    have := as.coclosed m n x m_lt_n (lt_of_le_of_ne hx.2 this)
    tauto
  rw [h_lf, h_md, h_rt] at diff
  simp at diff
  exact diff

lemma σ_inc (m_lt_n : m < n) (mn_nI : ⟨m, n⟩ ∉ as.I) : σ as m < σ as n := by
  have diff := σ_diff_pos as m n m_lt_n mn_nI
  by_contra! h
  have h_empty : as.md_pos m n = ∅ := by
    rw [← Finset.card_eq_zero]
    linarith
  apply Finset.eq_empty_iff_forall_notMem.mp at h_empty
  specialize h_empty m
  have : ⟨m, m⟩ ∈ as.I := by
    simp [m_lt_n, mn_nI] at h_empty
    exact h_empty
  linarith [as.directed m m this]

lemma σ_dec (m_lt_n : m < n) (mn_I : ⟨m, n⟩ ∈ as.I) : σ as m > σ as n := by
  have diff := σ_diff as m n (le_of_lt m_lt_n)
  have h_lf : as.lf_pos m n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    simp at hx
    have := as.closed x m n
    tauto
  have h_md : as.md_pos m n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    simp at hx
    have : m ≠ x := by
      intro h_eq
      rw [← h_eq] at hx
      exact hx.2.2 mn_I
    have : m < x := lt_of_le_of_ne hx.1.1 this
    have := as.coclosed m x n
    tauto
  have h_rt : as.rt_pos m n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    simp at hx
    have := as.closed m n x
    tauto
  rw [h_lf, h_md, h_rt] at diff
  simp at diff
  by_contra! h
  have h_empty : as.rt_neg m n = ∅ := by
    rw [← Finset.card_eq_zero]
    linarith
  apply Finset.eq_empty_iff_forall_notMem.mp at h_empty
  specialize h_empty n
  have : ⟨n, n⟩ ∈ as.I := by
    simp [mn_I] at h_empty
    exact h_empty
  linarith [as.directed n n this]

lemma mem_iff_lt (m_le_n : m ≤ n) : ⟨m, n⟩ ∈ as.I ↔ as.σ n < as.σ m := by
  constructor
  · intro h
    have m_lt_n : m < n := as.directed m n h
    exact σ_dec as m n m_lt_n h
  · intro h
    contrapose! h
    wlog m_lt_n : m < n
    · have h_eq : m = n := by linarith
      rw [h_eq]
    apply le_of_lt
    exact σ_inc as m n m_lt_n h

theorem func_injective (as : AspSet) : Function.Injective (as.to_func) := by
  intro m n h
  wlog m_le_n : m ≤ n generalizing m n
  · specialize this (h.symm) (by linarith)
    rw [this]
  contrapose! h
  have m_lt_n : m < n := lt_of_le_of_ne m_le_n h
  by_cases mn_I : ⟨m, n⟩ ∈ as.I
  · have := σ_dec as m n m_lt_n mn_I
    linarith
  · have := σ_inc as m n m_lt_n mn_I
    linarith

lemma contiguity_helper (m_lt_n : m < n) (σ_m_lt_n : σ as m < σ as n) :
  (σ as) ⁻¹' (Set.Ico (σ as m) (σ as n))
  = (lf_pos as m n) ∪ (md_pos as m n) ∪ (rt_pos as m n) := by
  have mn_nI : ⟨m, n⟩ ∉ as.I := by
    intro h
    have := σ_dec as m n m_lt_n h
    linarith [σ_m_lt_n]
  ext k
  simp

  by_cases k_lt_m : k < m
  · have h0 : ¬ (m ≤ k) := by linarith
    have h1 : ⟨m, k⟩ ∉ as.I := by
      intro h
      have := as.directed m k h
      linarith
    have h2 : ⟨n, k⟩ ∉ as.I := by
      intro h
      have := as.directed n k h
      linarith
    have h3 : as.σ m ≤ as.σ k ↔ ⟨k,m⟩ ∈ as.I := by
      rw [mem_iff_lt as k m (le_of_lt k_lt_m)]
      constructor
      · intro h
        by_contra! h'
        have : m = k := func_injective as (le_antisymm h h')
        linarith
      · intro h; exact le_of_lt h
    have h4 : as.σ k < as.σ n ↔ ⟨k,n⟩ ∉ as.I := by
      rw [mem_iff_lt as k n (le_of_lt (lt_trans k_lt_m m_lt_n))]
      have : k ≠ n := by
        intro h_eq
        rw [h_eq] at k_lt_m
        linarith
      have : as.σ k ≠ as.σ n := by
        contrapose! this
        exact func_injective as this
      constructor
      · intro h
        push_neg
        linarith
      · intro h
        push_neg at h
        exact lt_of_le_of_ne h this
    simp [h0, h1, h2, h3, h4]
  have m_le_k : m ≤ k := by
    push_neg at k_lt_m; exact k_lt_m
  clear k_lt_m
  by_cases k_lt_n : k < n
  · simp [m_le_k, k_lt_n]
    have h1 : as.σ m ≤ as.σ k ↔ ⟨m,k⟩ ∉ as.I := by
      rw [mem_iff_lt as m k m_le_k]
      push_neg; rfl
    have h2 : as.σ k < as.σ n ↔ ⟨k,n⟩ ∉ as.I := by
      rw [mem_iff_lt as k n (le_of_lt k_lt_n)]
      push_neg; constructor
      · apply le_of_lt
      · intro h
        by_contra!
        have h_eq := le_antisymm h this
        have h_eq : k = n := func_injective as h_eq
        linarith
    rw [h1, h2]
    constructor
    · intro h
      obtain ⟨mk_I, kn_nI⟩ := h
      simp [mk_I, kn_nI]
    · intro h
      have km_nI : ⟨k, m⟩ ∉ as.I := by
        intro h
        have := as.directed k m h
        linarith
      have nk_nI : ⟨n, k⟩ ∉ as.I := by
        intro h
        have := as.directed n k h
        linarith
      simp [km_nI, nk_nI] at h
      exact h
  have n_le_k : n ≤ k := by push_neg at k_lt_n; exact k_lt_n
  clear k_lt_n
  have : ¬(k < n) := by linarith
  simp [m_le_k, this]
  have : as.σ m ≤ as.σ k ↔ ⟨m, k⟩ ∉ as.I := by
    simp [mem_iff_lt as m k m_le_k]
  rw [this]
  have : as.σ k < as.σ n ↔ ⟨n,k⟩ ∈ as.I := by
    simp [mem_iff_lt as n k n_le_k]
  rw [this]
  constructor
  · intro h
    tauto
  · intro h
    rcases h with (h | h)
    · absurd h.1
      intro h'
      have : k < m := as.directed k m h'
      linarith
    · tauto

lemma func_contiguous (m_lt_n : m < n) (σ_m_lt_n : σ as m < σ as n) :
  ∀ k : ℤ, as.to_func m ≤ k → k < as.to_func n
  → ∃ l : ℤ, k = as.to_func l := by
  let σ := as.to_func
  let I := Finset.Ico (σ m) (σ n)
  let J := as.lf_pos m n ∪ as.md_pos m n ∪ as.rt_pos m n
  let K := Finset.image σ J

  have inv_image : σ ⁻¹' I = ↑J:= by
    unfold I σ
    have := contiguity_helper as m n m_lt_n σ_m_lt_n
    rw [← this]
    simp
  have card_J : (J.card : ℤ) = (σ n - σ m) := by
    unfold J
    have : ⟨m, n⟩ ∉ as.I := by
      rw [mem_iff_lt as m n (le_of_lt m_lt_n)]
      linarith
    rw [σ_diff_pos as m n m_lt_n this]
    simp
    let L := as.lf_pos m n
    let M := as.md_pos m n
    let R := as.rt_pos m n
    suffices (L ∪ (M ∪ R)).card = L.card + M.card + R.card by
      unfold L M R at this
      linarith
    have : Disjoint L (M ∪ R) := by
      rw [Finset.disjoint_iff_ne]
      rintro a ha b hb
      have a_small : a < m := by
        unfold L at ha; simp at ha
        have : ⟨a, m⟩ ∈ as.I := by tauto
        exact as.directed a m this
      have b_large : b ≥ m := by
        unfold M R at hb; simp at hb
        rcases hb with (hb | hb)
        · tauto
        · have : ⟨n,b⟩ ∈ as.I := by tauto
          have := as.directed n b this
          linarith
      linarith
    rw [Finset.card_union_of_disjoint this]
    suffices (M ∪ R).card = M.card + R.card by linarith
    have : Disjoint M R := by
      rw [Finset.disjoint_iff_ne]; intro a ha b hb
      have a_small : a < n := by
        unfold M at ha; simp at ha; tauto
      have b_large : b ≥ n := by
        unfold R at hb; simp at hb
        have : ⟨n, b⟩ ∈ as.I := by tauto
        have := as.directed n b this
        linarith
      linarith
    rw [Finset.card_union_of_disjoint this]
  have card_K : (K.card : ℤ) = (σ n - σ m) := by
    rw [← card_J]
    have : Function.Injective σ := func_injective as
    have := Finset.card_image_of_injective J this
    rw [← this]
  have K_eq_I : K = I := by
    apply Finset.eq_of_subset_of_card_le
    · show K ⊆ I
      intro k hk
      unfold K at hk
      rw [Finset.mem_image] at hk
      rcases hk with ⟨j, j_in_J, rfl⟩
      have : j ∈ (J : Set ℤ) := by
        simp [j_in_J]
      rw [← inv_image] at this
      exact this
    suffices I.card = K.card by
      rw [this]
    suffices (I.card : ℤ) = (K.card : ℤ) by
      rw [Nat.cast_inj] at this
      exact this
    unfold I
    rw [card_K]
    suffices σ m ≤ σ n by simp [this]
    exact le_of_lt σ_m_lt_n
  intro k σm_le_k k_lt_σn
  have k_in_I : k ∈ I := by
    simp [I]
    exact ⟨σm_le_k, k_lt_σn⟩
  rw [← K_eq_I] at k_in_I
  unfold K at k_in_I
  rw [Finset.mem_image] at k_in_I
  rcases k_in_I with ⟨l, l_in_J, hl⟩
  use l
  rw [← hl]

end σ_diff

theorem invSet_func (as : AspSet) : inv_set (as.to_func) = as.I := by
  ext ⟨u, v⟩
  wlog u_lt_v : u < v
  · have h1 : ⟨u, v⟩ ∉ inv_set (as.to_func) := by
      unfold inv_set
      simp [u_lt_v]
    have h2 : ⟨u, v⟩ ∉ as.I := by
      intro h
      have := as.directed u v h
      contradiction
    tauto
  constructor
  · intro h
    contrapose! h
    have : as.to_func u < as.to_func v := σ_inc as u v u_lt_v h
    unfold inv_set; simp [u_lt_v]
    linarith
  · intro h
    unfold inv_set; simp [u_lt_v]
    exact σ_dec as u v u_lt_v h

lemma inset_eq_nw (as : AspSet) (n : ℤ) : (as.inset n).toSet
   = northwest_set as.σ ((as.σ n) + 1) n := by
  ext x; simp
  rw [← invSet_func as]
  unfold inv_set northwest_set; simp
  tauto

lemma outset_eq_se (as : AspSet) (n : ℤ) : (as.outset n).toSet
   = southeast_set as.σ (as.σ n) (n+1) := by
  ext x; simp
  rw [← invSet_func as]
  unfold inv_set southeast_set; simp
  tauto

-- This lemma is equivalent to the funtion being bounded above,
-- but it is stated in a strange way. This is just for convenience
-- in the proof of surjectivity.
lemma surj_helper_up (as : AspSet) (m : ℤ) (n : ℕ) :
  ∃ x : ℤ, x ≥ m ∧ as.to_func x ≥ as.to_func m + n := by
  induction n with
  | zero =>
    use m
    simp
  | succ n ih =>
  rcases ih with ⟨x, x_ge_m, fx_ge⟩
  have : ∃ y : ℤ, y > x ∧ y ∉ as.outset x := by
    by_contra! h
    have : {y : ℤ | y > x} = ↑ (as.outset x) := by
      ext y
      specialize h y
      constructor
      · intro h'; simp at h'
        apply h at h'
        exact h'
      · intro h'
        simp at h'
        exact as.directed x y h'
    have : {y | y > x}.Finite := by
      rw [this]
      apply Finset.finite_toSet
    have : {y | y > x}.Infinite := by
      refine Set.infinite_of_forall_exists_gt ?_
      intro a
      use (max a x) + 1
      simp
      constructor
      · have := le_max_right a x
        linarith
      · have := le_max_left a x
        linarith
    contradiction
  rcases this with ⟨y, y_gt_x, y_not_outset_x⟩
  use y
  constructor
  · linarith
  · simp at y_not_outset_x
    rw [mem_iff_lt as x y (le_of_lt y_gt_x)] at y_not_outset_x
    push_neg at y_not_outset_x
    have : as.to_func x ≠ as.to_func y := by
      intro h_eq
      have : x = y := (func_injective as) h_eq
      linarith
    have : as.to_func y > as.to_func x := by
      exact lt_of_le_of_ne y_not_outset_x this
    have := lt_of_le_of_lt fx_ge this
    simp [Nat.cast_add]
    linarith

-- This lemma follows the previous one line for line. Surely there is some nice way to unify them.
lemma surj_helper_down (as : AspSet) (m : ℤ) (n : ℕ) :
  ∃ x : ℤ, x ≤ m ∧ as.to_func x ≤ as.to_func m - n := by
  induction n with
  | zero =>
    use m
    simp
  | succ n ih =>
  rcases ih with ⟨x, x_le_m, fx_le⟩
  have : ∃ y : ℤ, y < x ∧ y ∉ as.inset x := by
    by_contra! h
    have : {y : ℤ | y < x} = ↑ (as.inset x) := by
      ext y
      specialize h y
      constructor
      · intro h'; simp at h'
        apply h at h'
        exact h'
      · intro h'
        simp at h'
        exact as.directed y x h'
    have : {y | y < x}.Finite := by
      rw [this]
      apply Finset.finite_toSet
    have : {y | y < x}.Infinite := by
      refine Set.infinite_of_forall_exists_lt ?_
      intro a
      use (min a x) - 1
      simp
      constructor
      · have := min_le_right a x
        linarith
      · have := min_le_left a x
        linarith
    contradiction
  rcases this with ⟨y, y_lt_x, y_not_inset_x⟩
  use y
  constructor
  · linarith
  · simp at y_not_inset_x
    rw [mem_iff_lt as y x (le_of_lt y_lt_x)] at y_not_inset_x
    push_neg at y_not_inset_x
    have : as.to_func y ≠ as.to_func x := by
      intro h_eq
      have : y = x := (func_injective as) h_eq
      linarith
    have : as.to_func y < as.to_func x := by
      exact lt_of_le_of_ne y_not_inset_x this
    have := lt_of_lt_of_le this fx_le
    simp [Nat.cast_add]
    linarith


theorem func_surjective (as : AspSet) : Function.Surjective (as.to_func) := by
  intro y
  have : ∃ m : ℤ, m ≤ 0 ∧ as.to_func m ≤ y := by
    by_cases h0 : as.to_func 0 ≤ y
    · use 0
    push_neg at h0
    rcases surj_helper_down as 0 (as.to_func 0 - y).toNat with
      ⟨m, m_le_0, fm_le⟩
    use m
    simp at fm_le
    simp [m_le_0]
    apply le_trans fm_le
    rw [max_eq_left (by linarith)]
    simp
  rcases this with ⟨m, m_le_0, fm_le_y⟩
  have : ∃ n : ℤ, n ≥ 1 ∧ as.to_func n ≥ y + 1 := by
    by_cases h1 : as.to_func 1 ≥ y + 1
    · use 1
    push_neg at h1
    rcases surj_helper_up as 1 (y + 1 - as.to_func 1).toNat with
      ⟨n, n_ge_1, fn_ge⟩
    use n
    simp at fn_ge
    rw [max_eq_left (by linarith)] at fn_ge
    simp [n_ge_1]
    linarith
  rcases this with ⟨n, n_ge_1, fn_ge_y1⟩
  have m_le_n : m ≤ n := by linarith
  have contig := func_contiguous as m n (by linarith) (lt_of_le_of_lt fm_le_y fn_ge_y1)
  specialize contig y fm_le_y fn_ge_y1
  rcases contig with ⟨l, hl⟩
  use l
  rw [hl]

theorem func_bijective (as : AspSet) : Function.Bijective (as.to_func) :=
  ⟨func_injective as, func_surjective as⟩

theorem func_asp (as : AspSet) : is_asp (as.to_func) := by
  let τ := as.to_func
  let se := southeast_set τ (τ 0) 1
  have se_fin : se.Finite := by
    suffices se = outset as 0 by
      rw [this]
      simp [as.finite_outdegree 0]
    rw [outset_eq_se as 0]
    congr
  let nw := northwest_set τ ((τ 0) + 1) 0
  have nw_fin : nw.Finite := by
    suffices nw = inset as 0 by
      rw [this]
      simp [as.finite_indegree 0]
    rw [inset_eq_nw as 0]
  apply asp_of_finite_quadrants (func_injective as) se_fin nw_fin

def toAspPerm (as : AspSet) : AspPerm :=
  ⟨as.to_func, func_bijective as, func_asp as⟩

lemma invSet_of_toAspPerm (as : AspSet) : (toAspPerm as).inv = as.I := invSet_func as

theorem invSets_of_AspPerms (I : Set (ℤ × ℤ)) :
  (∃ τ : AspPerm, τ.inv = I) ↔  (AspSet_prop I) := by
  constructor
  · intro h
    rcases h with ⟨τ, τ_inv_eq⟩
    rw [← τ_inv_eq]
    exact AspSet_InvSet_of_AspPerm τ
  · intro asp
    let as : AspSet := ⟨I, asp⟩
    use as.toAspPerm
    exact invSet_of_toAspPerm as

end
end AspSet
