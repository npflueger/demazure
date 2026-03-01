import Demazure.AspPerm
import Mathlib.Order.Interval.Set.Infinite

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

instance : SetLike AspSet (ℤ × ℤ) where
  coe := AspSet.I
  coe_injective' := by
    intro a b h
    cases a; cases b;
    congr

@[simp] lemma mem_AspSet (asps : AspSet) (u v : ℤ) : ⟨u, v⟩ ∈ asps ↔ ⟨u, v⟩ ∈ asps.I := Iff.rfl

namespace AspSet

abbrev directed (asps : AspSet) := asps.prop.directed
abbrev closed (asps : AspSet) := asps.prop.closed
abbrev coclosed (asps : AspSet) := asps.prop.coclosed
abbrev finite_outdegree (asps : AspSet) := asps.prop.finite_outdegree
abbrev finite_indegree (asps : AspSet) := asps.prop.finite_indegree


lemma AspSet_InvSet_of_AspPerm (τ : AspPerm) : AspSet_prop (inv_set τ) := by
  constructor
  · intro u v uv_inv
    exact uv_inv.1
  · intro u v w uv_inv vw_inv
    have h1 := lt_trans uv_inv.1 vw_inv.1
    have h2 := lt_trans vw_inv.2 uv_inv.2
    exact ⟨h1, h2⟩
  · intro u v w u_lt_v v_lt_w uv_inv vw_inv
    have h1 : u < w := lt_trans u_lt_v v_lt_w
    have h2 : τ u ≤ τ v := by
      contrapose! uv_inv
      exact ⟨u_lt_v, uv_inv⟩
    have h3 : τ v ≤ τ w := by
      contrapose! vw_inv
      exact ⟨v_lt_w, vw_inv⟩
    have h4 := le_trans h2 h3
    contrapose! h4
    exact h4.2
  · show ∀ (u : ℤ), {v | (u, v) ∈ inv_set τ}.Finite
    unfold inv_set; simp
    intro u
    suffices {v | u < v ∧ τ v < τ u} = southeast_set τ (τ u) (u+1) by
      rw [this]
      apply se_finite_of_asp τ.bijective.injective
      exact τ.asp
    ext v
    constructor
    · intro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    · intro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  · show ∀ (v : ℤ), {u | (u, v) ∈ inv_set τ}.Finite
    unfold inv_set; simp
    intro v
    suffices {u | u < v ∧ τ u > τ v} = northwest_set τ (τ v + 1) v by
      rw [this]
      apply nw_finite_of_asp τ.bijective.injective
      exact τ.asp
    ext u
    constructor
    · intro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
    · intro ⟨h1, h2⟩; exact ⟨h1, by omega⟩

def of_AspPerm (τ : AspPerm) : AspSet :=
  ⟨inv_set τ, AspSet_InvSet_of_AspPerm τ⟩

noncomputable abbrev inset (asps : AspSet) (n : ℤ) : Finset ℤ := (asps.finite_indegree n).toFinset

noncomputable abbrev outset (asps : AspSet) (n : ℤ) : Finset ℤ := (asps.finite_outdegree n).toFinset

@[simp] lemma mem_inset (asps : AspSet) (n x : ℤ) : x ∈ asps.inset n ↔ ⟨x, n⟩ ∈ asps := by
  simp [inset]

@[simp] lemma mem_outset (asps : AspSet) (n x : ℤ) : x ∈ asps.outset n ↔ ⟨n, x⟩ ∈ asps := by
  simp [outset]

noncomputable def to_func (asps : AspSet) : ℤ → ℤ :=
  fun n => n + (asps.outset n).card - (asps.inset n).card

section σ_diff
variable (asps : AspSet) (m n : ℤ)
noncomputable abbrev σ := asps.to_func

noncomputable abbrev lf_pos : Finset ℤ := asps.inset m \ asps.inset n
@[simp] lemma mem_lf_pos (x : ℤ) : x ∈ lf_pos asps m n
    ↔ x < m ∧ ⟨x, m⟩ ∈ asps ∧ ⟨x, n⟩ ∉ asps := by
  simp [lf_pos]
  intro hm hn
  exact asps.directed x m hm

noncomputable abbrev md_pos : Finset ℤ := (Finset.Ico m n) \ (asps.outset m ∪ asps.inset n)
@[simp] lemma mem_md_pos (x : ℤ) : x ∈ md_pos asps m n
    ↔ m ≤ x ∧ x < n ∧ ⟨m, x⟩ ∉ asps ∧ ⟨x, n⟩ ∉ asps := by
  simp [md_pos]
  constructor
  · intro h
    obtain ⟨x_ge_m, x_lt_n⟩ := h.1
    simp [x_ge_m, x_lt_n, h]
  · intro h
    obtain ⟨x_ge_m, x_lt_n, x_outm, x_inn⟩ := h
    simp [x_ge_m, x_lt_n, x_outm, x_inn]

noncomputable abbrev rt_pos : Finset ℤ := asps.outset n \ asps.outset m
@[simp] lemma mem_rt_pos (x : ℤ) : x ∈ rt_pos asps m n
    ↔ x ≥ n ∧ ⟨m,x⟩ ∉ asps ∧ ⟨n,x⟩ ∈ asps := by
  simp [rt_pos]
  constructor
  · intro h
    simp [h]
    exact le_of_lt (asps.directed n x h.1)
  · intro h
    simp [h]

noncomputable abbrev lf_neg : Finset ℤ := (asps.inset n \ asps.inset m).filter (· < m)
@[simp] lemma mem_lf_neg (x : ℤ) : x ∈ lf_neg asps m n
    ↔ x < m ∧ ⟨x, m⟩ ∉ asps ∧ ⟨x, n⟩ ∈ asps := by
  simp [lf_neg]
  constructor <;> (intro h; simp [h])

noncomputable abbrev md_neg : Finset ℤ := (Finset.Ico m n) ∩ (asps.outset m ∩ asps.inset n)
@[simp] lemma mem_md_neg (x : ℤ) : x ∈ md_neg asps m n
    ↔ m ≤ x ∧ x < n ∧ ⟨m, x⟩ ∈ asps ∧ ⟨x, n⟩ ∈ asps := by
  simp [md_neg]
  constructor <;> (intro h; simp [h])

noncomputable abbrev rt_neg : Finset ℤ := (asps.outset m \ asps.outset n).filter (· ≥  n)
@[simp] lemma mem_rt_neg (x : ℤ) : x ∈ rt_neg asps m n
    ↔ x ≥ n ∧ ⟨m,x⟩ ∈ asps ∧ ⟨n,x⟩ ∉ asps := by
  simp [rt_neg]
  constructor <;> (intro h; simp [h])

lemma σ_diff (m_le_n : m ≤ n) : asps.σ n - asps.σ m =
  ((lf_pos asps m n).card + (md_pos asps m n).card + (rt_pos asps m n).card)
  - ((lf_neg asps m n).card + (md_neg asps m n).card + (rt_neg asps m n).card) := by

  have : asps.σ n - asps.σ m =
    (Finset.Ico m n).card
    + ( (asps.outset n) \ (asps.outset m)).card  - ( (asps.outset m) \ (asps.outset n)).card
    + ( (asps.inset m) \ (asps.inset n)).card - ( (asps.inset n) \ (asps.inset m)).card := by
    unfold σ to_func
    have h1 := Utils.sub_card_eq_sub_card_diff (asps.outset n) (asps.outset m)
    have h2 := Utils.sub_card_eq_sub_card_diff (asps.inset m) (asps.inset n)
    have h3 : (Finset.Ico m n).card = n-m := by
      simp [m_le_n]
    linarith [h1,h2,h2]
  rw [this]

  have rp : (asps.outset n \ asps.outset m) = rt_pos asps m n := rfl
  have lp : (asps.inset m \ asps.inset n) = lf_pos asps m n := rfl
  have rn :
    (asps.outset m \ asps.outset n).card
    = ( (Finset.Ico m n) ∩ (asps.outset m) ).card + (rt_neg asps m n).card := by
    let A := (Finset.Ico m n) ∩ (asps.outset m)
    let B := rt_neg asps m n
    have : Disjoint A B := by
      rw [Finset.disjoint_iff_ne]
      rintro a ha b hb
      unfold A at ha; simp at ha
      unfold B at hb; simp at hb
      omega
    rw [← Finset.card_union_of_disjoint this]
    suffices (A ∪ B) = (asps.outset m \ asps.outset n) by
      rw [this]
    ext x
    unfold A B
    simp
    constructor
    · intro hx
      rcases hx with (hA | hB)
      · simp [hA]
        intro h
        have : n < x := asps.directed n x h
        omega
      · exact hB.1
    · intro h
      simp [h, le_of_lt (asps.directed m x h.1)]
      exact lt_or_ge x n
  have ln : (asps.inset n \ asps.inset m).card
    = ( (Finset.Ico m n) ∩ (asps.inset n) ).card + (lf_neg asps m n).card := by
    let A := (Finset.Ico m n) ∩ (asps.inset n)
    let B := lf_neg asps m n
    have : Disjoint A B := by
      rw [Finset.disjoint_iff_ne]
      rintro a ha b hb
      unfold A at ha; simp at ha
      unfold B at hb; simp at hb
      intro a_eq_b
      omega
    have := Finset.card_union_of_disjoint this
    rw [← this]
    suffices (A ∪ B) = (asps.inset n \ asps.inset m) by
      rw [this]
    ext x
    unfold A B; simp
    constructor
    · intro hx
      rcases hx with (hA | hB)
      · suffices ⟨x, m⟩ ∉ asps by tauto
        intro xm_I
        apply asps.directed x m at xm_I
        omega
      · exact hB.1
    · intro h
      have x_lt_n : x < n := asps.directed x n h.1
      simp [h, x_lt_n]
      exact le_or_gt m x
  suffices ((Finset.Ico m n).card : ℤ)
    - ↑(md_pos asps m n).card
    = ( (Finset.Ico m n) ∩ (asps.outset m) ).card
    + ( (Finset.Ico m n) ∩ (asps.inset n) ).card
    - ↑(md_neg asps m n).card
    by
    rw [rp, lp, rn, ln]
    simp only [Nat.cast_add]
    linarith [this]

  unfold md_pos md_neg
  let U := (Finset.Ico m n)
  let A := U ∩ asps.outset m
  let B := U ∩ asps.inset n
  have h_diff : (U \ (A ∪ B)) = (Finset.Ico m n \ (asps.outset m ∪ asps.inset n)) := by
    ext x
    unfold A B U
    simp; tauto
  have h_inter : (A ∩ B) = (Finset.Ico m n ∩ (asps.outset m ∩ asps.inset n)) := by
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
      simp at hx ⊢
      tauto
    simp only [Finset.card_sdiff_of_subset this]
    suffices A ∪ B ⊆ U by
      simp [Finset.card_le_card this]
    intro x hx
    unfold A B at hx
    simp at hx
    tauto
  linarith [h_diff, h_union]

lemma σ_diff_pos (m_lt_n : m < n) (mn_I : ⟨m, n⟩ ∉ asps) :
  asps.σ n - asps.σ m
  = ↑(asps.lf_pos m n).card + ↑(asps.md_pos m n).card + ↑(asps.rt_pos m n).card := by
  have diff := σ_diff asps m n (le_of_lt m_lt_n)
  have h_lf : asps.lf_neg m n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx; simp at hx
    exact (asps.coclosed x m n hx.2 m_lt_n hx.1.2 mn_I) hx.1.1
  have h_md : asps.md_neg m n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx; simp at hx
    exact mn_I (asps.closed m x n hx.2.1 hx.2.2)
  have h_rt : asps.rt_neg m n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx; simp at hx
    have n_ne_x : n ≠ x := by rintro rfl; exact mn_I hx.1.1
    exact (asps.coclosed m n x m_lt_n (lt_of_le_of_ne hx.2 n_ne_x) mn_I hx.1.2) hx.1.1
  rw [h_lf, h_md, h_rt] at diff
  simp at diff
  exact diff

lemma σ_inc (m_lt_n : m < n) (mn_nI : ⟨m, n⟩ ∉ asps) : asps.σ m < asps.σ n := by
  have diff := σ_diff_pos asps m n m_lt_n mn_nI
  by_contra! h
  have h_empty : asps.md_pos m n = ∅ := by
    rw [← Finset.card_eq_zero]
    omega
  apply Finset.eq_empty_iff_forall_notMem.mp at h_empty
  specialize h_empty m
  have : ⟨m, m⟩ ∈ asps := by
    simp [m_lt_n] at h_empty
    tauto
  linarith [asps.directed m m this]

lemma σ_dec (m_lt_n : m < n) (mn_I : ⟨m, n⟩ ∈ asps) : asps.σ m > asps.σ n := by
  have diff := σ_diff asps m n (le_of_lt m_lt_n)
  have h_lf : asps.lf_pos m n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx; simp at hx
    exact hx.2 (asps.closed x m n hx.1 mn_I)
  have h_md : asps.md_pos m n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx; simp at hx
    have m_ne_x : m ≠ x := fun h => hx.2.2 (h ▸ mn_I)
    exact (asps.coclosed m x n (lt_of_le_of_ne hx.1.1 m_ne_x) hx.1.2 hx.2.1 hx.2.2) mn_I
  have h_rt : asps.rt_pos m n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx; simp at hx
    exact hx.2 (asps.closed m n x mn_I hx.1)
  rw [h_lf, h_md, h_rt] at diff
  simp at diff
  by_contra! h
  have h_empty : asps.rt_neg m n = ∅ := by
    rw [← Finset.card_eq_zero]
    omega
  apply Finset.eq_empty_iff_forall_notMem.mp at h_empty
  specialize h_empty n
  have : ⟨n, n⟩ ∈ asps := by
    simp at h_empty
    exact h_empty mn_I
  linarith [asps.directed n n this]

lemma mem_iff_lt (m_le_n : m ≤ n) : ⟨m, n⟩ ∈ asps ↔ asps.σ n < asps.σ m := by
  constructor
  · intro h
    have m_lt_n : m < n := asps.directed m n h
    exact σ_dec asps m n m_lt_n h
  · intro h
    contrapose! h
    wlog m_lt_n : m < n
    · have h_eq : m = n := by omega
      rw [h_eq]
    apply le_of_lt
    exact σ_inc asps m n m_lt_n h

theorem func_injective (asps : AspSet) : Function.Injective (asps.to_func) := by
  intro m n h
  wlog m_le_n : m ≤ n generalizing m n
  · specialize this (h.symm) (by omega)
    rw [this]
  contrapose! h
  have m_lt_n : m < n := lt_of_le_of_ne m_le_n h
  by_cases mn_I : ⟨m, n⟩ ∈ asps
  · have := σ_dec asps m n m_lt_n mn_I
    linarith
  · have := σ_inc asps m n m_lt_n mn_I
    linarith

lemma contiguity_helper (m_lt_n : m < n) (σ_m_lt_n : asps.σ m < asps.σ n) :
  (asps.σ) ⁻¹' (Set.Ico (asps.σ m) (asps.σ n))
  = (lf_pos asps m n) ∪ (md_pos asps m n) ∪ (rt_pos asps m n) := by
  have mn_nI : ⟨m, n⟩ ∉ asps := by
    intro h
    have := σ_dec asps m n m_lt_n h
    linarith [σ_m_lt_n]
  ext k
  simp

  by_cases k_lt_m : k < m
  · have h0 : ¬ (m ≤ k) := not_le_of_gt k_lt_m
    have h1 : ⟨m, k⟩ ∉ asps := by
      intro h
      have := asps.directed m k h
      omega
    have h2 : ⟨n, k⟩ ∉ asps := by
      intro h
      have := asps.directed n k h
      omega
    have h3 : asps.σ m ≤ asps.σ k ↔ ⟨k,m⟩ ∈ asps := by
      rw [mem_iff_lt asps k m (le_of_lt k_lt_m)]
      constructor
      · intro h
        by_contra! h'
        have : m = k := func_injective asps (le_antisymm h h')
        omega
      · intro h; exact le_of_lt h
    have h4 : asps.σ k < asps.σ n ↔ ⟨k,n⟩ ∉ asps := by
      rw [mem_iff_lt asps k n (le_of_lt (lt_trans k_lt_m m_lt_n))]
      have : k ≠ n := by
        intro h_eq
        rw [h_eq] at k_lt_m
        omega
      have : asps.σ k ≠ asps.σ n := by
        contrapose! this
        exact func_injective asps this
      constructor
      · intro h
        push_neg
        omega
      · intro h
        push_neg at h
        exact lt_of_le_of_ne h this
    simp at h0 h1 h2 h3 h4
    simp [h0, h1, h2, h3, h4]
  have m_le_k : m ≤ k := le_of_not_gt k_lt_m
  clear k_lt_m
  by_cases k_lt_n : k < n
  · simp only [m_le_k, k_lt_n]
    have h1 : asps.σ m ≤ asps.σ k ↔ ⟨m,k⟩ ∉ asps := by
      rw [mem_iff_lt asps m k m_le_k]
      push_neg; rfl
    have h2 : asps.σ k < asps.σ n ↔ ⟨k,n⟩ ∉ asps := by
      rw [mem_iff_lt asps k n (le_of_lt k_lt_n)]
      push_neg; constructor
      · apply le_of_lt
      · intro h
        by_contra!
        have h_eq := le_antisymm h this
        have h_eq : k = n := func_injective asps h_eq
        omega
    rw [h1, h2]
    constructor
    · intro h
      obtain ⟨mk_I, kn_nI⟩ := h
      simp at mk_I kn_nI
      simp [mk_I, kn_nI]
    · intro h
      have km_nI : ⟨k, m⟩ ∉ asps := by
        intro h
        have := asps.directed k m h
        omega
      have nk_nI : ⟨n, k⟩ ∉ asps := by
        intro h
        have := asps.directed n k h
        omega
      simp at km_nI nk_nI
      simp [km_nI, nk_nI] at h
      simp [h]
  have n_le_k : n ≤ k := le_of_not_gt k_lt_n
  clear k_lt_n
  have : ¬(k < n) := not_lt_of_ge n_le_k
  simp [m_le_k, this]
  have : asps.σ m ≤ asps.σ k ↔ ⟨m, k⟩ ∉ asps := by
    simp [mem_iff_lt asps m k m_le_k]
  rw [this]
  have : asps.σ k < asps.σ n ↔ ⟨n,k⟩ ∈ asps := by
    simp [mem_iff_lt asps n k n_le_k]
  rw [this]
  constructor
  · intro h
    tauto
  · intro h
    rcases h with (h | h)
    · absurd h.1
      intro h'
      have : k < m := asps.directed k m h'
      omega
    · tauto

lemma func_contiguous (m_lt_n : m < n) (σ_m_lt_n : asps.σ m < asps.σ n) :
  ∀ k : ℤ, asps.to_func m ≤ k → k < asps.to_func n
  → ∃ l : ℤ, k = asps.to_func l := by
  let σ := asps.to_func
  let I := Finset.Ico (σ m) (σ n)
  let J := asps.lf_pos m n ∪ asps.md_pos m n ∪ asps.rt_pos m n
  let K := Finset.image σ J

  have inv_image : σ ⁻¹' I = ↑J:= by
    unfold I σ
    have := contiguity_helper asps m n m_lt_n σ_m_lt_n
    rw [← this]
    simp
  have card_J : (J.card : ℤ) = (σ n - σ m) := by
    unfold J
    have : ⟨m, n⟩ ∉ asps := by
      rw [mem_iff_lt asps m n (le_of_lt m_lt_n)]
      omega
    rw [σ_diff_pos asps m n m_lt_n this]
    simp
    let L := asps.lf_pos m n
    let M := asps.md_pos m n
    let R := asps.rt_pos m n
    suffices (L ∪ (M ∪ R)).card = L.card + M.card + R.card by
      unfold L M R at this
      omega
    have : Disjoint L (M ∪ R) := by
      rw [Finset.disjoint_iff_ne]
      rintro a ha b hb
      have a_small : a < m := by
        unfold L at ha; simp at ha
        have : ⟨a, m⟩ ∈ asps := by tauto
        exact asps.directed a m this
      have b_large : b ≥ m := by
        unfold M R at hb; simp at hb
        rcases hb with (hb | hb)
        · tauto
        · have : ⟨n,b⟩ ∈ asps := by tauto
          have := asps.directed n b this
          omega
      omega
    rw [Finset.card_union_of_disjoint this]
    suffices (M ∪ R).card = M.card + R.card by omega
    have : Disjoint M R := by
      rw [Finset.disjoint_iff_ne]; intro a ha b hb
      have a_small : a < n := by
        unfold M at ha; simp at ha; tauto
      have b_large : b ≥ n := by
        unfold R at hb; simp at hb
        have : ⟨n, b⟩ ∈ asps := by tauto
        have := asps.directed n b this
        omega
      omega
    rw [Finset.card_union_of_disjoint this]
  have card_K : (K.card : ℤ) = (σ n - σ m) := by
    rw [← card_J]
    have : Function.Injective σ := func_injective asps
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

section OfAspSet
variable (asps : AspSet)

theorem invSet_func : inv_set (asps.to_func) = asps := by
  ext ⟨u, v⟩
  wlog u_lt_v : u < v
  · have h1 : ⟨u, v⟩ ∉ inv_set (asps.to_func) := by
      intro huv
      exact u_lt_v huv.1
    have h2 : ⟨u, v⟩ ∉ asps := by
      intro h
      have := asps.directed u v h
      contradiction
    constructor
    · intro huv
      exact (h1 huv).elim
    · intro huv
      exact (h2 huv).elim
  constructor
  · intro h
    contrapose! h
    have : asps.to_func u < asps.to_func v := σ_inc asps u v u_lt_v h
    intro huv
    exact (lt_irrefl (asps.to_func u)) (lt_trans this huv.2)
  · intro h
    exact ⟨u_lt_v, σ_dec asps u v u_lt_v h⟩

lemma inset_eq_nw (n : ℤ) : (asps.inset n).toSet
   = northwest_set asps.σ ((asps.σ n) + 1) n := by
  ext x
  unfold northwest_set
  have := Set.ext_iff.mp <| invSet_func asps
  specialize this ⟨x, n⟩
  constructor
  · intro hx
    have hx' : ⟨x, n⟩ ∈ asps := by simpa using hx
    have h_inv : ⟨x, n⟩ ∈ inv_set asps.σ := by simpa [this] using hx'
    rcases h_inv with ⟨hxn, hσ⟩
    exact ⟨hxn, by omega⟩
  · intro hx
    rcases hx with ⟨hxn, hσ⟩
    have h_inv : ⟨x, n⟩ ∈ inv_set asps.σ := ⟨hxn, by omega⟩
    have hx' : ⟨x, n⟩ ∈ asps := by simpa [this] using h_inv
    simpa using hx'

lemma outset_eq_se (n : ℤ) : (asps.outset n).toSet
   = southeast_set asps.σ (asps.σ n) (n+1) := by
  ext x
  have := Set.ext_iff.mp <| invSet_func asps
  specialize this ⟨n, x⟩
  constructor
  · intro hx
    have hx' : ⟨n, x⟩ ∈ asps := by simpa using hx
    have h_inv : ⟨n, x⟩ ∈ inv_set asps.σ := by simpa [this] using hx'
    rcases h_inv with ⟨hnx, hσ⟩
    exact ⟨by omega, hσ⟩
  · intro hx
    rcases hx with ⟨hnx, hσ⟩
    have h_inv : ⟨n, x⟩ ∈ inv_set asps.σ := ⟨by omega, hσ⟩
    have hx' : ⟨n, x⟩ ∈ asps := by simpa [this] using h_inv
    simpa using hx'

-- This lemma is equivalent to the funtion being bounded above,
-- but it is stated in a strange way. This is just for convenience
-- in the proof of surjectivity.
lemma surj_helper_up (m : ℤ) (n : ℕ) :
  ∃ x : ℤ, x ≥ m ∧ asps.to_func x ≥ asps.to_func m + n := by
  induction n with
  | zero =>
    use m
    simp
  | succ n ih =>
  rcases ih with ⟨x, x_ge_m, fx_ge⟩
  obtain ⟨y, y_gt_x, y_not_outset_x⟩ : ∃ y : ℤ, y > x ∧ y ∉ asps.outset x := by
    by_contra! hall
    have heq : {y : ℤ | y > x} = ↑(asps.outset x) := by
      ext y; simp only [Set.mem_setOf_eq, Finset.mem_coe, mem_outset]
      exact ⟨fun hy => (mem_outset asps x y).mp (hall y hy),
             fun hy => by linarith [asps.directed x y hy]⟩
    have hfin : ({y : ℤ | y > x}).Finite := heq ▸ Finset.finite_toSet _
    exact Set.Ioi_infinite x hfin
  use y
  constructor
  · omega
  · simp at y_not_outset_x
    have h_ineq : asps.to_func x ≤ asps.to_func y := by
      rw [← not_lt, ← mem_iff_lt asps x y (le_of_lt y_gt_x)]
      exact y_not_outset_x
    have h_ne : asps.to_func x ≠ asps.to_func y :=
      fun h => absurd (func_injective asps h) (by omega)
    have hlt := lt_of_le_of_ne h_ineq h_ne
    simp [Nat.cast_add]; linarith [lt_of_le_of_lt fx_ge hlt]

lemma surj_helper_down (m : ℤ) (n : ℕ) :
  ∃ x : ℤ, x ≤ m ∧ asps.to_func x ≤ asps.to_func m - n := by
  induction n with
  | zero =>
    use m
    simp
  | succ n ih =>
  rcases ih with ⟨x, x_le_m, fx_le⟩
  obtain ⟨y, y_lt_x, y_not_inset_x⟩ : ∃ y : ℤ, y < x ∧ y ∉ asps.inset x := by
    by_contra! hall
    have heq : {y : ℤ | y < x} = ↑(asps.inset x) := by
      ext y; simp only [Set.mem_setOf_eq, Finset.mem_coe, mem_inset]
      exact ⟨fun hy => (mem_inset asps x y).mp (hall y hy),
             fun hy => by linarith [asps.directed y x hy]⟩
    have hfin : ({y : ℤ | y < x}).Finite := heq ▸ Finset.finite_toSet _
    exact Set.Iio_infinite x hfin
  use y
  constructor
  · omega
  · simp at y_not_inset_x
    have h_ineq : asps.to_func y ≤ asps.to_func x := by
      rw [← not_lt, ← mem_iff_lt asps y x (le_of_lt y_lt_x)]
      exact y_not_inset_x
    have h_ne : asps.to_func y ≠ asps.to_func x :=
      fun h => absurd (func_injective asps h) (by omega)
    have hlt := lt_of_le_of_ne h_ineq h_ne
    simp [Nat.cast_add]; linarith [lt_of_lt_of_le hlt fx_le]


theorem func_surjective : Function.Surjective (asps.to_func) := by
  intro y
  have : ∃ m : ℤ, m ≤ 0 ∧ asps.to_func m ≤ y := by
    by_cases h0 : asps.to_func 0 ≤ y
    · use 0
    push_neg at h0
    rcases surj_helper_down asps 0 (asps.to_func 0 - y).toNat with
      ⟨m, m_le_0, fm_le⟩
    use m
    simp at fm_le
    simp [m_le_0]
    apply le_trans fm_le
    rw [max_eq_left (by omega)]
    simp
  rcases this with ⟨m, m_le_0, fm_le_y⟩
  have : ∃ n : ℤ, n ≥ 1 ∧ asps.to_func n ≥ y + 1 := by
    by_cases h1 : asps.to_func 1 ≥ y + 1
    · use 1
    push_neg at h1
    rcases surj_helper_up asps 1 (y + 1 - asps.to_func 1).toNat with
      ⟨n, n_ge_1, fn_ge⟩
    use n
    simp at fn_ge
    rw [max_eq_left (by omega)] at fn_ge
    simp [n_ge_1]
    omega
  rcases this with ⟨n, n_ge_1, fn_ge_y1⟩
  have m_le_n : m ≤ n := by omega
  have contig := func_contiguous asps m n (by omega) (lt_of_le_of_lt fm_le_y fn_ge_y1)
  specialize contig y fm_le_y fn_ge_y1
  rcases contig with ⟨l, hl⟩
  use l
  rw [hl]

theorem func_bijective : Function.Bijective (asps.to_func) :=
  ⟨func_injective asps, func_surjective asps⟩

theorem func_asp : is_asp (asps.to_func) := by
  let τ := asps.to_func
  let se := southeast_set τ (τ 0) 1
  have se_fin : se.Finite := by
    suffices se = outset asps 0 by
      rw [this]
      simp [asps.finite_outdegree 0]
    rw [outset_eq_se asps 0]
    congr
  let nw := northwest_set τ ((τ 0) + 1) 0
  have nw_fin : nw.Finite := by
    suffices nw = inset asps 0 by
      rw [this]
      simp [asps.finite_indegree 0]
    rw [inset_eq_nw asps 0]
  apply asp_of_finite_quadrants (func_injective asps) se_fin nw_fin

noncomputable def toAspPerm : AspPerm :=
  ⟨asps.to_func, func_bijective asps, func_asp asps⟩

lemma invSet_of_toAspPerm : inv_set (toAspPerm asps)= asps := invSet_func asps

end OfAspSet

theorem invSets_of_AspPerms (I : Set (ℤ × ℤ)) :
  (∃ τ : AspPerm, inv_set τ = I) ↔  (AspSet_prop I) := by
  constructor
  · intro h
    rcases h with ⟨τ, τ_inv_eq⟩
    rw [← τ_inv_eq]
    exact AspSet_InvSet_of_AspPerm τ
  · intro asp
    let asps : AspSet := ⟨I, asp⟩
    use asps.toAspPerm
    exact invSet_of_toAspPerm asps

end AspSet
