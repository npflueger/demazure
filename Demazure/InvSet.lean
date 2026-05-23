import Demazure.AspPerm
import Mathlib.Order.Interval.Set.Infinite

/-- The axioms characterizing inversion sets of ASP permutations: directedness,
closure, coclosure, and finite in/out degree. -/
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

/-- An abstract ASP inversion set: a set of boxes equipped with the axioms of
`AspSet_prop`. -/
structure AspSet where
  I : Set (ℤ × ℤ)
  prop : AspSet_prop I

instance : SetLike AspSet (ℤ × ℤ) where
  coe := AspSet.I
  coe_injective' := by
    intro a b h
    cases a; cases b;
    congr

@[simp] lemma mem_AspSet (asps : AspSet) (u v : ℤ) :
    ⟨u, v⟩ ∈ asps ↔ ⟨u, v⟩ ∈ asps.I := Iff.rfl

namespace AspSet

/-- Two `AspSet`s are equal if their underlying sets of boxes are equal. -/
theorem ext {A B : AspSet} (hI : A.I = B.I) : A = B := by
  cases A
  cases B
  cases hI
  rfl

abbrev directed (asps : AspSet) := asps.prop.directed
abbrev closed (asps : AspSet) := asps.prop.closed
abbrev coclosed (asps : AspSet) := asps.prop.coclosed
abbrev finite_outdegree (asps : AspSet) := asps.prop.finite_outdegree
abbrev finite_indegree (asps : AspSet) := asps.prop.finite_indegree

lemma not_mem_of_ge (asps : AspSet) {m n : ℤ} (n_le_m : n ≤ m) : ⟨m, n⟩ ∉ asps := by
  intro h
  exact (not_lt_of_ge n_le_m) (asps.directed m n h)

@[simp] lemma not_mem_self (asps : AspSet) (n : ℤ) : ⟨n, n⟩ ∉ asps := by
  exact asps.not_mem_of_ge (le_refl n)

/-- The order on indices after the inversions in `asps` are applied. -/
def post_lt (asps : AspSet) (m n : ℤ) : Prop :=
  (m < n ∧ ⟨m, n⟩ ∉ asps) ∨ (n < m ∧ ⟨n, m⟩ ∈ asps)

@[simp] lemma not_post_lt_self (asps : AspSet) (n : ℤ) : ¬ asps.post_lt n n := by
  simp [post_lt]

lemma post_lt_iff_not_mem (asps : AspSet) {m n : ℤ} (m_lt_n : m < n) :
    asps.post_lt m n ↔ ⟨m, n⟩ ∉ asps := by
  simp [post_lt, m_lt_n, not_lt_of_gt m_lt_n]

lemma post_lt_swap_iff_mem (asps : AspSet) {m n : ℤ} (m_le_n : m ≤ n) :
    asps.post_lt n m ↔ ⟨m, n⟩ ∈ asps := by
  rcases lt_or_eq_of_le m_le_n with m_lt_n | rfl
  · simp [post_lt, m_lt_n, not_lt_of_gt m_lt_n]
  · exact iff_of_false (not_post_lt_self asps m) (not_mem_self asps m)

lemma post_lt_trans (asps : AspSet) {l m n : ℤ} (hlm : asps.post_lt l m) (hmn : asps.post_lt m n) :
  asps.post_lt l n := by
  rcases hlm with (⟨l_lt_m, lm_nI⟩ | ⟨m_lt_l, ml_I⟩)
  · rcases hmn with (⟨m_lt_n, mn_nI⟩ | ⟨n_lt_m, nm_I⟩)
    · left
      refine ⟨lt_trans l_lt_m m_lt_n, ?_⟩
      apply asps.coclosed l m n <;> assumption
    · by_cases hl : l < n
      · left
        refine ⟨hl, ?_⟩
        contrapose! lm_nI with hln
        apply asps.closed l n m <;> assumption
      · right
        have n_lt_l : n < l := by
          refine lt_of_le_of_ne (le_of_not_gt hl) ?_
          intro n_eq_l
          exact lm_nI (by simpa [n_eq_l] using nm_I)
        refine ⟨n_lt_l, ?_⟩
        contrapose! nm_I with nl_nI
        apply asps.coclosed n l m <;> assumption
  · rcases hmn with (⟨m_lt_n, mn_nI⟩ | ⟨n_lt_m, nm_I⟩)
    · by_cases hl : l < n
      · left
        refine ⟨hl, ?_⟩
        contrapose! mn_nI with ln_I
        apply asps.closed m l n <;> assumption
      · right
        have n_lt_l : n < l := by
          refine lt_of_le_of_ne (le_of_not_gt hl) ?_
          intro n_eq_l
          exact mn_nI (by simpa [n_eq_l] using ml_I)
        refine ⟨n_lt_l, ?_⟩
        contrapose! ml_I with nl_nI
        apply asps.coclosed m n l <;> assumption
    · right
      refine ⟨lt_trans n_lt_m m_lt_l, ?_⟩
      apply asps.closed n m l <;> assumption


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
  · exact τ.outset_finite
  · exact τ.inset_finite

def of_AspPerm (τ : AspPerm) : AspSet :=
  ⟨inv_set τ, AspSet_InvSet_of_AspPerm τ⟩

noncomputable abbrev inset (asps : AspSet) (n : ℤ) : Finset ℤ :=
  (asps.finite_indegree n).toFinset

noncomputable abbrev outset (asps : AspSet) (n : ℤ) : Finset ℤ :=
  (asps.finite_outdegree n).toFinset

@[simp] lemma mem_inset (asps : AspSet) (n x : ℤ) :
    x ∈ asps.inset n ↔ ⟨x, n⟩ ∈ asps := by
  simp [inset]

@[simp] lemma mem_outset (asps : AspSet) (n x : ℤ) :
    x ∈ asps.outset n ↔ ⟨n, x⟩ ∈ asps := by
  simp [outset]

/-- Reconstruct a function `ℤ → ℤ` from an abstract ASP inversion set and a
shift parameter `χ`. -/
noncomputable def recon (asps : AspSet) (χ : ℤ) : ℤ → ℤ :=
  fun n => n + (asps.outset n).card - (asps.inset n).card - χ

section σ_diff
variable (asps : AspSet) (m n χ : ℤ)
noncomputable abbrev σ := asps.recon χ

noncomputable abbrev lf_pos : Finset ℤ := asps.inset m \ asps.inset n
@[simp] lemma mem_lf_pos (x : ℤ) : x ∈ lf_pos asps m n
    ↔ x < m ∧ ⟨x, m⟩ ∈ asps ∧ ⟨x, n⟩ ∉ asps := by
  simp only [Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.mem_setOf_eq, mem_AspSet,
    iff_and_self, and_imp]
  intro hm hn
  exact asps.directed x m hm

noncomputable abbrev md_pos : Finset ℤ := (Finset.Ico m n) \ (asps.outset m ∪ asps.inset n)
@[simp] lemma mem_md_pos (x : ℤ) : x ∈ md_pos asps m n
    ↔ m ≤ x ∧ x < n ∧ ⟨m, x⟩ ∉ asps ∧ ⟨x, n⟩ ∉ asps := by
  simp only [Finset.mem_sdiff, Finset.mem_Ico, Finset.mem_union, Set.Finite.mem_toFinset,
    Set.mem_setOf_eq, not_or, mem_AspSet]
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
  simp only [Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.mem_setOf_eq, ge_iff_le,
    mem_AspSet]
  constructor
  · intro h
    simp only [h, not_false_eq_true, and_self, and_true]
    exact le_of_lt (asps.directed n x h.1)
  · intro h
    simp [h]

noncomputable abbrev lf_neg : Finset ℤ := (asps.inset n \ asps.inset m).filter (· < m)
@[simp] lemma mem_lf_neg (x : ℤ) : x ∈ lf_neg asps m n
    ↔ x < m ∧ ⟨x, m⟩ ∉ asps ∧ ⟨x, n⟩ ∈ asps := by
  simp only [Finset.mem_filter, Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
    mem_AspSet]
  constructor <;> (intro h; simp [h])

noncomputable abbrev md_neg : Finset ℤ := (Finset.Ico m n) ∩ (asps.outset m ∩ asps.inset n)
@[simp] lemma mem_md_neg (x : ℤ) : x ∈ md_neg asps m n
    ↔ m ≤ x ∧ x < n ∧ ⟨m, x⟩ ∈ asps ∧ ⟨x, n⟩ ∈ asps := by
  simp only [Finset.mem_inter, Finset.mem_Ico, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
    mem_AspSet]
  constructor <;> (intro h; simp [h])

noncomputable abbrev rt_neg : Finset ℤ := (asps.outset m \ asps.outset n).filter (· ≥  n)
@[simp] lemma mem_rt_neg (x : ℤ) : x ∈ rt_neg asps m n
    ↔ x ≥ n ∧ ⟨m,x⟩ ∈ asps ∧ ⟨n,x⟩ ∉ asps := by
  simp only [Finset.mem_filter, Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
    ge_iff_le, mem_AspSet]
  constructor <;> (intro h; simp [h])

lemma σ_diff (m_le_n : m ≤ n) : asps.σ χ n - asps.σ χ m =
  ((lf_pos asps m n).card + (md_pos asps m n).card + (rt_pos asps m n).card)
  - ((lf_neg asps m n).card + (md_neg asps m n).card + (rt_neg asps m n).card) := by
  have : asps.σ χ n - asps.σ χ m =
    (Finset.Ico m n).card
    + ( (asps.outset n) \ (asps.outset m)).card  - ( (asps.outset m) \ (asps.outset n)).card
    + ( (asps.inset m) \ (asps.inset n)).card - ( (asps.inset n) \ (asps.inset m)).card := by
    unfold σ recon
    have h1 := Utils.sub_card_eq_sub_card_diff (asps.outset n) (asps.outset m)
    have h2 := Utils.sub_card_eq_sub_card_diff (asps.inset m) (asps.inset n)
    have h3 : (Finset.Ico m n).card = n-m := by
      simp [m_le_n]
    linarith [h1,h2,h3]
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
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_Ico, Set.Finite.mem_toFinset,
      Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_sdiff, ge_iff_le]
    constructor
    · intro hx
      rcases hx with (hA | hB)
      · simp only [hA, true_and]
        intro h
        have : n < x := asps.directed n x h
        omega
      · exact hB.1
    · intro h
      simp only [le_of_lt (asps.directed m x h.1), true_and, h, and_true, not_false_eq_true,
        and_self]
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
    unfold A B
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_Ico, Set.Finite.mem_toFinset,
      Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_sdiff]
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
      simp only [x_lt_n, and_true, h, not_false_eq_true, and_self, true_and]
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
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_Ico, Set.Finite.mem_toFinset,
        Set.mem_setOf_eq] at hx ⊢
      tauto
    simp only [Finset.card_sdiff_of_subset this]
    suffices A ∪ B ⊆ U by
      simp [Finset.card_le_card this]
    intro x hx
    unfold A B at hx
    simp only [Finset.mem_union, Finset.mem_inter, Set.Finite.mem_toFinset,
      Set.mem_setOf_eq] at hx
    tauto
  linarith [h_diff, h_union]

lemma σ_diff_pos (m_lt_n : m < n) (mn_I : ⟨m, n⟩ ∉ asps) :
  asps.σ χ n - asps.σ χ m
  = ↑(asps.lf_pos m n).card + ↑(asps.md_pos m n).card + ↑(asps.rt_pos m n).card := by
  have diff := σ_diff asps m n χ (le_of_lt m_lt_n)
  have h_lf : asps.lf_neg m n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx
    exact (asps.coclosed x m n hx.2 m_lt_n hx.1.2 mn_I) hx.1.1
  have h_md : asps.md_neg m n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx; simp only [Finset.mem_inter, Finset.mem_Ico, Set.Finite.mem_toFinset,
      Set.mem_setOf_eq] at hx
    exact mn_I (asps.closed m x n hx.2.1 hx.2.2)
  have h_rt : asps.rt_neg m n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
      ge_iff_le] at hx
    have n_ne_x : n ≠ x := by rintro rfl; exact mn_I hx.1.1
    exact (asps.coclosed m n x m_lt_n (lt_of_le_of_ne hx.2 n_ne_x) mn_I hx.1.2) hx.1.1
  rw [h_lf, h_md, h_rt] at diff
  simp only [Finset.card_empty, Nat.cast_zero, add_zero, sub_zero] at diff
  exact diff

lemma σ_inc (m_lt_n : m < n) (mn_nI : ⟨m, n⟩ ∉ asps) : asps.σ χ m < asps.σ χ n := by
  have diff := σ_diff_pos asps m n χ m_lt_n mn_nI
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

lemma σ_dec (m_lt_n : m < n) (mn_I : ⟨m, n⟩ ∈ asps) : asps.σ χ m > asps.σ χ n := by
  have diff := σ_diff asps m n χ (le_of_lt m_lt_n)
  have h_lf : asps.lf_pos m n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    simp only [Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx
    exact hx.2 (asps.closed x m n hx.1 mn_I)
  have h_md : asps.md_pos m n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_Ico, Finset.mem_union, Set.Finite.mem_toFinset,
      Set.mem_setOf_eq, not_or] at hx
    have m_ne_x : m ≠ x := fun h => hx.2.2 (h ▸ mn_I)
    exact (asps.coclosed m x n (lt_of_le_of_ne hx.1.1 m_ne_x) hx.1.2 hx.2.1 hx.2.2) mn_I
  have h_rt : asps.rt_pos m n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    simp only [Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx
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
    simp only [Finset.mem_filter, Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
      ge_iff_le, le_refl, and_true, not_and, not_not] at h_empty
    exact h_empty mn_I
  linarith [asps.directed n n this]

lemma post_lt_iff_σ_lt : asps.post_lt m n ↔ asps.σ χ m < asps.σ χ n := by
  -- Proof written by Codex.
  constructor
  · rintro (⟨m_lt_n, mn_nI⟩ | ⟨n_lt_m, nm_I⟩)
    · exact σ_inc asps m n χ m_lt_n mn_nI
    · exact σ_dec asps n m χ n_lt_m nm_I
  · intro hσ
    rcases lt_trichotomy m n with m_lt_n | rfl | n_lt_m
    · left
      refine ⟨m_lt_n, ?_⟩
      intro mn_I
      have hdec := σ_dec asps m n χ m_lt_n mn_I
      omega
    · exact (lt_irrefl _ hσ).elim
    · right
      refine ⟨n_lt_m, ?_⟩
      by_contra nm_nI
      have hinc := σ_inc asps n m χ n_lt_m nm_nI
      omega

lemma not_post_lt_iff_σ_le :
    ¬ asps.post_lt m n ↔ asps.σ χ n ≤ asps.σ χ m := by
  rw [post_lt_iff_σ_lt]
  exact not_lt

lemma mem_iff_lt (m_le_n : m ≤ n) : ⟨m, n⟩ ∈ asps ↔ asps.σ χ n < asps.σ χ m := by
  rw [← post_lt_iff_σ_lt asps n m χ]
  exact (post_lt_swap_iff_mem asps m_le_n).symm

theorem post_lt_trichotomous (asps : AspSet) : Std.Trichotomous asps.post_lt := by
  -- Proof written by Codex.
  exact Std.trichotomous_of_rel_or_eq_or_rel_swap fun {m n} => by
    rcases lt_trichotomy m n with m_lt_n | rfl | n_lt_m
    · by_cases mn_I : ⟨m, n⟩ ∈ asps
      · exact Or.inr <| Or.inr <| (post_lt_swap_iff_mem asps (le_of_lt m_lt_n)).mpr mn_I
      · exact Or.inl <| (post_lt_iff_not_mem asps m_lt_n).mpr mn_I
    · exact Or.inr <| Or.inl rfl
    · by_cases nm_I : ⟨n, m⟩ ∈ asps
      · exact Or.inl <| (post_lt_swap_iff_mem asps (le_of_lt n_lt_m)).mpr nm_I
      · exact Or.inr <| Or.inr <| (post_lt_iff_not_mem asps n_lt_m).mpr nm_I

instance (asps : AspSet) : IsStrictTotalOrder ℤ asps.post_lt where
  toTrichotomous := post_lt_trichotomous asps
  irrefl := not_post_lt_self asps
  trans _ _ _ := post_lt_trans asps

theorem func_injective (asps : AspSet) : Function.Injective (asps.recon χ) := by
  -- Proof written by GPT 5.5.
  intro m n hσ
  rcases trichotomous_of asps.post_lt m n with hmn | rfl | hnm
  · have hlt := (post_lt_iff_σ_lt asps m n χ).mp hmn
    exact ((ne_of_lt hlt) hσ).elim
  · rfl
  · have hlt := (post_lt_iff_σ_lt asps n m χ).mp hnm
    exact ((ne_of_gt hlt) hσ).elim

lemma contiguity_helper (m_lt_n : m < n) :
  (asps.σ χ) ⁻¹' (Set.Ico (asps.σ χ m) (asps.σ χ n))
  = (lf_pos asps m n) ∪ (md_pos asps m n) ∪ (rt_pos asps m n) := by
  -- Proof written by Codex.
  ext k
  simp only [Set.mem_preimage, Set.mem_Ico, Finset.mem_coe]
  rw [← not_post_lt_iff_σ_le asps k m χ,
    ← post_lt_iff_σ_lt asps k n χ]
  rcases lt_or_ge k m with k_lt_m | m_le_k
  · have k_lt_n : k < n := lt_trans k_lt_m m_lt_n
    have mk_nI : ⟨m, k⟩ ∉ asps := asps.not_mem_of_ge (le_of_lt k_lt_m)
    have nk_nI : ⟨n, k⟩ ∉ asps := asps.not_mem_of_ge (le_of_lt k_lt_n)
    simp only [mem_AspSet] at mk_nI nk_nI
    rw [post_lt_iff_not_mem asps k_lt_m, post_lt_iff_not_mem asps k_lt_n]
    simp [not_le_of_gt k_lt_m, mk_nI, nk_nI]
  · rcases lt_or_ge k n with k_lt_n | n_le_k
    · have km_nI : ⟨k, m⟩ ∉ asps := asps.not_mem_of_ge m_le_k
      have nk_nI : ⟨n, k⟩ ∉ asps := asps.not_mem_of_ge (le_of_lt k_lt_n)
      simp only [mem_AspSet] at km_nI nk_nI
      rw [post_lt_swap_iff_mem asps m_le_k, post_lt_iff_not_mem asps k_lt_n]
      simp [m_le_k, k_lt_n, km_nI, nk_nI]
    · have km_nI : ⟨k, m⟩ ∉ asps := asps.not_mem_of_ge m_le_k
      simp only [mem_AspSet] at km_nI
      rw [post_lt_swap_iff_mem asps m_le_k, post_lt_swap_iff_mem asps n_le_k]
      simp [not_lt_of_ge n_le_k, km_nI, and_comm]

lemma func_contiguous (m_lt_n : m < n) (σ_m_lt_n : asps.σ χ m < asps.σ χ n) :
  ∀ k : ℤ, asps.recon χ m ≤ k → k < asps.recon χ n
  → ∃ l : ℤ, k = asps.recon χ l := by
  let σ := asps.recon χ
  let I := Finset.Ico (σ m) (σ n)
  let J := asps.lf_pos m n ∪ asps.md_pos m n ∪ asps.rt_pos m n
  let K := Finset.image σ J
  have inv_image : σ ⁻¹' I = ↑J:= by
    unfold I σ
    have := contiguity_helper asps m n χ m_lt_n
    rw [← this]
    simp
  have card_J : (J.card : ℤ) = (σ n - σ m) := by
    unfold J
    have : ⟨m, n⟩ ∉ asps := by
      rw [mem_iff_lt asps m n χ (le_of_lt m_lt_n)]
      omega
    rw [σ_diff_pos asps m n χ m_lt_n this]
    simp only [Finset.union_assoc]
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
        unfold M R at hb
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_Ico, Set.Finite.mem_toFinset,
          Set.mem_setOf_eq, not_or] at hb
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
    have : Function.Injective σ := func_injective χ asps
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
    simp only [Finset.mem_Ico, I]
    exact ⟨σm_le_k, k_lt_σn⟩
  rw [← K_eq_I] at k_in_I
  unfold K at k_in_I
  rw [Finset.mem_image] at k_in_I
  rcases k_in_I with ⟨l, l_in_J, hl⟩
  use l
  rw [← hl]

end σ_diff

/-! ### Reconstructing ASP Permutations from ASP Sets

Starting from an abstract ASP set `asps` and a shift `χ`, this section proves
that the reconstructed function is bijective, ASP, and has the expected
inversion data, yielding an `AspPerm`. -/

section OfAspSet
variable (asps : AspSet) (χ : ℤ)

/-- The reconstructed function has the prescribed inversion set. -/
theorem invSet_func : inv_set (asps.recon χ) = asps := by
  ext ⟨u, v⟩
  wlog u_lt_v : u < v
  · have h1 : ⟨u, v⟩ ∉ inv_set (asps.recon χ) := by
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
    exact (mem_iff_lt asps u v χ (le_of_lt u_lt_v)).mpr h.2
  · intro h
    exact ⟨u_lt_v, (mem_iff_lt asps u v χ (le_of_lt u_lt_v)).mp h⟩

lemma inset_eq_nw (n : ℤ) : ↑(asps.inset n)
   = northwest_set (asps.σ χ) ((asps.σ χ n) + 1) n := by
  ext x
  unfold northwest_set
  have := Set.ext_iff.mp <| invSet_func asps χ
  specialize this ⟨x, n⟩
  constructor
  · intro hx
    have hx' : ⟨x, n⟩ ∈ asps := by simpa using hx
    have h_inv : ⟨x, n⟩ ∈ inv_set (asps.σ χ) := by simpa [this] using hx'
    rcases h_inv with ⟨hxn, hσ⟩
    exact ⟨hxn, by omega⟩
  · intro hx
    rcases hx with ⟨hxn, hσ⟩
    have h_inv : ⟨x, n⟩ ∈ inv_set (asps.σ χ) := ⟨hxn, by omega⟩
    have hx' : ⟨x, n⟩ ∈ asps := by simpa [this] using h_inv
    simpa using hx'

lemma outset_eq_se (n : ℤ) : ↑(asps.outset n)
   = southeast_set (asps.σ χ) (asps.σ χ n) (n+1) := by
  ext x
  have := Set.ext_iff.mp <| invSet_func asps χ
  specialize this ⟨n, x⟩
  constructor
  · intro hx
    have hx' : ⟨n, x⟩ ∈ asps := by simpa using hx
    have h_inv : ⟨n, x⟩ ∈ inv_set (asps.σ χ) := by simpa [this] using hx'
    rcases h_inv with ⟨hnx, hσ⟩
    exact ⟨by omega, hσ⟩
  · intro hx
    rcases hx with ⟨hnx, hσ⟩
    have h_inv : ⟨n, x⟩ ∈ inv_set (asps.σ χ) := ⟨by omega, hσ⟩
    have hx' : ⟨n, x⟩ ∈ asps := by simpa [this] using h_inv
    simpa using hx'

-- This lemma is equivalent to the function being bounded above,
-- but it is stated in a strange way. This is just for convenience
-- in the proof of surjectivity.
lemma surj_helper_up (m : ℤ) (n : ℕ) :
  ∃ x : ℤ, x ≥ m ∧ asps.recon χ x ≥ asps.recon χ m + n := by
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
  · simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at y_not_outset_x
    have hlt := σ_inc asps x y χ y_gt_x y_not_outset_x
    simp [Nat.cast_add]; linarith [lt_of_le_of_lt fx_ge hlt]

lemma surj_helper_down (m : ℤ) (n : ℕ) :
  ∃ x : ℤ, x ≤ m ∧ asps.recon χ x ≤ asps.recon χ m - n := by
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
  · simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at y_not_inset_x
    have hlt := σ_inc asps y x χ y_lt_x y_not_inset_x
    simp [Nat.cast_add]; linarith [lt_of_lt_of_le hlt fx_le]


/-- The function reconstructed from an ASP set and a shift is surjective. -/
theorem func_surjective : Function.Surjective (asps.recon χ) := by
  intro y
  have : ∃ m : ℤ, m ≤ 0 ∧ asps.recon χ m ≤ y := by
    by_cases h0 : asps.recon χ 0 ≤ y
    · use 0
    rcases surj_helper_down asps χ 0 (asps.recon χ 0 - y).toNat with
      ⟨m, m_le_0, fm_le⟩
    use m
    simp only [Int.ofNat_toNat] at fm_le
    simp only [m_le_0, true_and]
    apply le_trans fm_le
    rw [max_eq_left (by omega)]
    simp
  rcases this with ⟨m, m_le_0, fm_le_y⟩
  have : ∃ n : ℤ, n ≥ 1 ∧ asps.recon χ n ≥ y + 1 := by
    by_cases h1 : asps.recon χ 1 ≥ y + 1
    · use 1
    rcases surj_helper_up asps χ 1 (y + 1 - asps.recon χ 1).toNat with
      ⟨n, n_ge_1, fn_ge⟩
    use n
    simp only [Int.ofNat_toNat, ge_iff_le] at fn_ge
    rw [max_eq_left (by omega)] at fn_ge
    simp [n_ge_1]
    omega
  rcases this with ⟨n, n_ge_1, fn_ge_y1⟩
  have m_le_n : m ≤ n := by omega
  have contig := func_contiguous asps m n χ (by omega) (lt_of_le_of_lt fm_le_y fn_ge_y1)
  specialize contig y fm_le_y fn_ge_y1
  rcases contig with ⟨l, hl⟩
  use l
  rw [hl]

theorem func_bijective : Function.Bijective (asps.recon χ) :=
  ⟨func_injective χ asps, func_surjective asps χ⟩

theorem func_asp : is_asp (asps.recon χ) := by
  let τ := asps.recon χ
  let se := southeast_set τ (τ 0) 1
  have se_fin : se.Finite := by
    suffices se = outset asps 0 by
      rw [this]
      simp [asps.finite_outdegree 0]
    rw [outset_eq_se asps χ 0]
    congr
  let nw := northwest_set τ ((τ 0) + 1) 0
  have nw_fin : nw.Finite := by
    suffices nw = inset asps 0 by
      rw [this]
      simp [asps.finite_indegree 0]
    rw [inset_eq_nw asps χ 0]
  apply asp_of_finite_quadrants (func_injective χ asps) se_fin nw_fin

/-- Package the function reconstructed from an ASP set and a shift as an
`AspPerm`. -/
noncomputable def toAspPerm : AspPerm :=
  ⟨asps.recon χ, func_bijective asps χ, func_asp asps χ⟩

lemma invSet_of_toAspPerm : inv_set (toAspPerm asps χ)= asps := invSet_func asps χ

lemma inset_of_toAspPerm (n : ℤ) : (toAspPerm asps χ).inset n = asps.inset n := by
  ext x
  have h1 : x ∈ (toAspPerm asps χ).inset n ↔ ⟨x, n⟩ ∈ inv_set (toAspPerm asps χ) := by
    apply AspPerm.invset_iff_inset
  have h2 : x ∈ ↑(asps.inset n) ↔ ⟨x, n⟩ ∈ inv_set (toAspPerm asps χ) := by
    have := asps.inset_eq_nw χ n
    rw [invSet_of_toAspPerm asps χ]
    simp
  simp only [h1, ← h2]
  rfl

lemma outset_of_toAspPerm (n : ℤ) : (toAspPerm asps χ).outset n = asps.outset n := by
  ext x
  have h1 : x ∈ (toAspPerm asps χ).outset n ↔ ⟨n, x⟩ ∈ inv_set (toAspPerm asps χ) := by
    apply AspPerm.invset_iff_outset
  have h2 : x ∈ ↑(asps.outset n) ↔ ⟨n, x⟩ ∈ inv_set (toAspPerm asps χ) := by
    have := asps.outset_eq_se χ n
    rw [invSet_of_toAspPerm asps χ]
    simp
  simp only [h1, ← h2]
  rfl

lemma chi_of_toAspPerm : (toAspPerm asps χ).χ = χ := by
  let σ := toAspPerm asps χ
  have h1 : σ 0 = (asps.outset 0).card - (asps.inset 0).card - χ := by
    unfold σ toAspPerm recon
    simp
  have h2 : σ 0 = (σ.outset 0).ncard - (σ.inset 0).ncard - σ.χ := by
    rw [σ.reconstruction 0]
    omega
  have hout : σ.outset 0 = asps.outset 0 := outset_of_toAspPerm asps χ 0
  have hin : σ.inset 0 = asps.inset 0 := inset_of_toAspPerm asps χ 0
  rw [hout, hin] at h2
  repeat rw [Set.ncard_coe_finset] at h2
  rw [h1] at h2
  linarith [h2]

end OfAspSet

/-- ASP permutations are equivalent to abstract ASP inversion sets together
with a shift parameter. -/
noncomputable def AspPerm_equiv_AspSet :
  AspPerm ≃ AspSet × ℤ where
  toFun τ := (⟨inv_set τ, AspSet_InvSet_of_AspPerm τ⟩, τ.χ)
  invFun := fun ⟨asps, χ⟩ => asps.toAspPerm χ
  left_inv := by
    intro τ
    refine AspPerm.eq_of_inv_set_eq_of_chi_eq _ _ ?_ ?_
    · have h_inv := invSet_of_toAspPerm ⟨inv_set τ, AspSet_InvSet_of_AspPerm τ⟩ τ.χ
      simpa using h_inv
    · have h_chi := chi_of_toAspPerm ⟨inv_set τ, AspSet_InvSet_of_AspPerm τ⟩ τ.χ
      simpa using h_chi
  right_inv := by
    intro ⟨asps, χ⟩
    apply Prod.ext
    · apply SetLike.coe_injective
      change inv_set (asps.toAspPerm χ) = asps
      exact invSet_of_toAspPerm asps χ
    · simpa using chi_of_toAspPerm asps χ

@[simp] lemma AspPerm_equiv_AspSet_toFun_fst (τ : AspPerm) :
    ((AspPerm_equiv_AspSet τ).1 : Set (ℤ × ℤ)) = inv_set τ := rfl

@[simp] lemma AspPerm_equiv_AspSet_toFun_snd (τ : AspPerm) :
    (AspPerm_equiv_AspSet τ).2 = τ.χ := rfl

@[simp] lemma inv_set_AspPerm_equiv_AspSet_invFun (asps : AspSet) (χ : ℤ) :
    inv_set (AspPerm_equiv_AspSet.invFun (asps, χ)) = asps := by
  exact invSet_of_toAspPerm asps χ

@[simp] lemma chi_AspPerm_equiv_AspSet_invFun (asps : AspSet) (χ : ℤ) :
    (AspPerm_equiv_AspSet.invFun (asps, χ)).χ = χ := by
  exact chi_of_toAspPerm asps χ

theorem invSets_of_AspPerms (I : Set (ℤ × ℤ)) (χ : ℤ) :
  (∃ τ : AspPerm, inv_set τ = I ∧ τ.χ = χ) ↔  (AspSet_prop I) := by
  constructor
  · intro h
    rcases h with ⟨τ, τ_inv_eq, τ_chi_eq⟩
    rw [← τ_inv_eq]
    exact AspSet_InvSet_of_AspPerm τ
  · intro asp
    let asps : AspSet := ⟨I, asp⟩
    use asps.toAspPerm χ
    exact ⟨invSet_of_toAspPerm asps χ, chi_of_toAspPerm asps χ⟩

end AspSet
