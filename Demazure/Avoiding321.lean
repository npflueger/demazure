import Mathlib
import Demazure.AspPerm
import Demazure.Utils



def I_directed (S : Set (ℤ × ℤ)) : Prop :=
  ∀ u v : ℤ, ⟨u,v⟩ ∈ S → u < v

def I_tfree (S : Set (ℤ × ℤ)) : Prop :=
  ∀ u v w : ℤ, (u,v) ∉ S ∨ (v,w) ∉ S

def I_coclosed (S : Set (ℤ × ℤ)) : Prop :=
  ∀ u v n : ℤ, (u,v) ∈ S → u < n → n < v → (u,n) ∈ S ∨ (n,v) ∈ S

def I_finite_outdegree (S : Set (ℤ × ℤ)) : Prop :=
  ∀ n : ℤ, { v : ℤ | ⟨n,v⟩ ∈ S }.Finite

def I_finite_indegree (S : Set (ℤ × ℤ)) : Prop :=
  ∀ n : ℤ, { u : ℤ | ⟨u,n⟩ ∈ S }.Finite

def I_locfinite (S : Set (ℤ × ℤ)) : Prop :=
  I_finite_outdegree S ∧ I_finite_indegree S

structure I_321a_prop (I : Set (ℤ × ℤ)) where
  directed : I_directed I
  tfree : I_tfree I
  coclosed : I_coclosed I
  locfinite : I_locfinite I

structure I_321a where
  set : Set (ℤ × ℤ)
  prop : I_321a_prop set

-- Abbreviations for convenience
namespace I_321a

abbrev dir (I : I_321a) := I.prop.directed
abbrev tf (I : I_321a) := I.prop.tfree
abbrev cc (I : I_321a) := I.prop.coclosed
abbrev lf (I : I_321a) := I.prop.locfinite
-- inset and outset as finsets, for use in cardinality
noncomputable abbrev inset (I : I_321a) (n : ℤ) : Finset ℤ := (I.lf.2 n).toFinset
noncomputable abbrev outset (I : I_321a) (n : ℤ) : Finset ℤ := (I.lf.1 n).toFinset

end I_321a

-- Characterization of inset and outset, just to confirm they mean what you think
def inset_char (I : I_321a) (n : ℤ) (u : ℤ) : u ∈ I.inset n ↔ ⟨u,n⟩ ∈ I.set := by
  simp
def outset_char (I : I_321a) (n : ℤ) (v : ℤ) : v ∈ I.outset n ↔ ⟨n,v⟩ ∈ I.set := by
  simp

def is_321a (τ : ℤ → ℤ) : Prop :=
  ∀ (i j k : ℤ), i < j → j < k → τ i < τ j ∨ τ j < τ k

def perm_321a := { τ : ℤ → ℤ // Function.Bijective τ ∧ is_321a τ }

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

theorem criterion_321a (τ : ℤ → ℤ) (hperm : Function.Bijective τ) : is_321a τ ↔
  I_321a_prop (inv_set τ) := by
  constructor
  -- Forward direction
  · intro h321a
    constructor
    · show I_directed (inv_set τ)
      intro u v uvinv
      exact uvinv.1
    · show I_tfree (inv_set τ)
      intro u v w
      by_contra! h; obtain ⟨⟨u_lt_v,τv_lt_τu⟩, ⟨v_lt_w,τw_lt_τv⟩⟩ := h
      cases (h321a u v w u_lt_v v_lt_w) <;> linarith
    · show I_coclosed (inv_set τ)
      rintro u v n ⟨u_lt_v, τv_lt_τu⟩ u_lt_n n_lt_v
      by_cases h_τun : τ n < τ u
      · -- case τ n < τ u
        left; exact ⟨u_lt_n, h_τun⟩
      · -- case τ u ≤ τ n
        right; use n_lt_v
        linarith
    · show I_locfinite (inv_set τ)
      have h_asp : is_asp τ := asp_of_321a ⟨τ, hperm, h321a⟩
      constructor
      · -- Finite outdegree
        intro x
        have : {v | (x, v) ∈ inv_set τ} = southeast_set τ (τ x) (x+1) := by
          unfold southeast_set inv_set
          ext v
          constructor
          · intro h
            simp at *
            obtain ⟨h1, h2⟩ := h
            constructor <;> linarith
          · intro h
            simp at *
            obtain ⟨h1, h2⟩ := h
            constructor <;> linarith
        rw [this]
        exact se_finite_of_asp hperm.injective (τ x) (x+1) h_asp
      · -- Finite indegree
        intro x
        have : {u | ⟨u,x⟩ ∈ inv_set τ} = northwest_set τ ((τ x)+1) x := by
          ext u
          unfold northwest_set inv_set
          constructor
          · intro h
            simp at *
            obtain ⟨h1, h2⟩ := h
            constructor <;> linarith
          · intro h
            simp at *
            obtain ⟨h1, h2⟩ := h
            constructor <;> linarith
        rw [this]
        exact nw_finite_of_asp hperm.injective ((τ x)+1) x h_asp
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


noncomputable section

variable (I : I_321a)

def σ : ℤ → ℤ :=
  fun n : ℤ =>
  n + (I.outset n).card - (I.inset n).card

def slice_set (m n : ℤ) : Finset ℤ :=
  ((I.inset m) \ (I.inset n)) ∪ ((I.outset n) \ (I.outset m))



lemma slice_card (m n : ℤ) : (slice_set I m n).card =
  ((I.inset m) \ (I.inset n)).card
    + ((I.outset n) \ (I.outset m)).card := by
  unfold slice_set; rw [Finset.card_union]
  suffices (I.inset m \ I.inset n ∩ (I.outset n \ I.outset m)).card = 0 by
    rw [this]; simp
  apply Finset.card_eq_zero.mpr

  apply Finset.eq_empty_of_forall_notMem
  rintro x hx
  -- apply Finset.mem_inter.mp at hx
  obtain ⟨h_inset, h_outset⟩ := Finset.mem_inter.mp hx

  apply Finset.mem_sdiff.mp at h_inset
  obtain ⟨h_in_m, _⟩ := h_inset
  have h_in_m : ⟨x, m⟩ ∈ I.set := (inset_char I m x).mp h_in_m

  apply Finset.mem_sdiff.mp at h_outset
  obtain ⟨h_out_n,_⟩ := h_outset
  have h_out_n : ⟨n, x⟩ ∈ I.set := (outset_char I n x).mp h_out_n

  have :=  I.tf n x m
  contrapose! this
  exact ⟨h_out_n, h_in_m⟩

lemma σ_diff_slice (m n : ℤ) : σ I n - σ I m =
  (n - m)
    + ↑(slice_set I m n).card
    - ↑(slice_set I n m).card := by
  have h : σ I n - σ I m =
    (n-m) + ((I.inset m).card - (I.inset n).card) + ((I.outset n).card - (I.outset m).card) := by
    unfold σ
    ring
  rw [h]
  rw [Utils.sub_card_eq_sub_card_diff (I.inset m) (I.inset n)]
  rw [Utils.sub_card_eq_sub_card_diff (I.outset n) (I.outset m)]
  rw [slice_card, slice_card]
  rw [Nat.cast_add, Nat.cast_add]
  ring

/- Helper: ℤ version of Finset.card_sdiff -/
lemma card_sdiff_int (S T : Finset ℤ) :
  (↑(S \ T).card : ℤ) = (↑S.card : ℤ) - (↑(S ∩ T).card : ℤ) := by
  rw [Finset.card_sdiff]
  rw [Nat.cast_sub, Finset.inter_comm T S]
  apply Finset.card_le_card
  apply Finset.inter_subset_right

lemma inc_pair {m n : ℤ} (h_mn : m < n) (h_S : ⟨m, n⟩ ∉ I.set) :
  σ I n - σ I m = 1
    + ((I.inset m) \ (I.inset n)).card
    + ((I.outset n) \ (I.outset m)).card
    + ((Finset.Ioo m n) \ (I.outset m ∪ I.inset n)).card
  := by
  rw [σ_diff_slice]
  have : n-m = 1 + (Finset.Ioo m n).card := by
    simp [h_mn]
  rw [this]
  suffices (↑(Finset.Ioo m n).card : ℤ)
    = ↑(Finset.Ioo m n \ (I.outset m ∪ I.inset n)).card + ↑(slice_set I n m).card by
    simp only [this, slice_card, Nat.cast_add]
    ring
  rw [card_sdiff_int]

  suffices slice_set I n m = (Finset.Ioo m n ∩ (I.outset m ∪ I.inset n)) by
    rw [this, Finset.card_inter]
    ring

  show slice_set I n m = (Finset.Ioo m n ∩ (I.outset m ∪ I.inset n))

  ext x
  unfold slice_set
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
    Finset.mem_Ioo, inset_char, outset_char]

  by_cases I_mx : ⟨m,x⟩ ∈ I.set
  -- Case 1: ⟨m,x⟩ ∈ I.set
  · have : ⟨x, m⟩ ∉ I.set := by
      have := I.tf m x m; tauto
    simp [I_mx, this, I.dir _ _ I_mx]
    by_cases I_xn : ⟨x,n⟩ ∈ I.set
    · -- Case 1a: ⟨m,x⟩ and ⟨x,n⟩ ∈ I
      have : ⟨n,x⟩ ∉ I.set := by
        have := I.tf x n x; tauto
      simp [I_xn, this]
      exact I.dir _ _ I_xn
    · -- Case 1b: ⟨m,x⟩ ∈ I but ⟨x,n⟩ ∉ I
      simp [I_xn]
      constructor
      · intro I_nx
        contrapose! I_nx with x_lt_n
        suffices ⟨m, n⟩ ∈ I.set ∨ ⟨n, x⟩ ∈ I.set by tauto
        apply I.cc m x n I_mx h_mn; show n < x
        apply lt_of_le_of_ne x_lt_n; show n ≠ x
        intro n_eq_x
        rw [n_eq_x] at h_S
        exact h_S I_mx
      · by_contra! h
        obtain ⟨x_lt_n,h_nx⟩ := h
        linarith [I.dir _ _ h_nx]
  -- Case 2: ⟨m,x⟩ ∉ I.set
  · simp [I_mx]
    by_cases I_xn : ⟨x,n⟩ ∈ I.set
    · -- Case 2a: ⟨m,x⟩ ∉ I but ⟨x,n⟩ ∈ I
      simp [I_xn, I.dir _ _ I_xn]
      by_cases m_lt_x : m < x
      · -- Case 2a.i: m < x
        simp [m_lt_x]
        contrapose! m_lt_x with I_mn
        exact le_of_lt (I.dir _ _ I_mn)
      · -- Case 2a.ii: m ≥ x
        simp [m_lt_x]
        have x_lt_m : x < m := by
          push_neg at m_lt_x
          apply lt_of_le_of_ne m_lt_x
          intro m_eq_x
          rw [m_eq_x] at I_xn
          exact h_S I_xn
        have h : (x, m) ∈ I.set ∨ (m, n) ∈ I.set :=
          I.cc x n m I_xn x_lt_m h_mn
        tauto
    · -- Case 2b: ⟨m,x⟩ and ⟨x,n⟩ ∉ I
      simp [I_xn]

lemma card_sum_helper {A B C : Finset ℤ}
  (h_union : A = B ∪ C) (h_disj : ∀ x : ℤ, x ∉ B ∨ x ∉ C) : A.card = B.card + C.card := by
  rw [h_union]
  apply Finset.card_union_of_disjoint
  apply Finset.disjoint_iff_ne.mpr
  intro x x_B y y_C rfl
  specialize h_disj x
  tauto

lemma dec_pair {m n : ℤ} (I_mn : ⟨m, n⟩ ∈ I.set) :
  σ I n - σ I m = -1
    - ((I.inset n).filter (· < m)).card
    - ((I.outset m).filter (· > n)).card
  := by
  have m_lt_n : m < n := I.dir _ _ I_mn
  rw [σ_diff_slice]

  have : n - m = -1 + (Finset.Icc m n).card := by
    have : max (n+1-m) 0 = n+1-m := by
      simp; linarith
    simp [this]; ring
  rw [this]

  have : (slice_set I m n).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    unfold slice_set at hx
    rw [Finset.mem_union] at hx
    rcases hx with (hx | hx)
    · -- Case 1: x ∈ (I.inset m) \ (I.inset n)
      apply Finset.mem_sdiff.mp at hx
      have hx : ⟨x,m⟩ ∈ I.set := (inset_char I m x).mp hx.1
      have := I.tf x m n
      tauto
    · -- Case 2: x ∈ (I.outset n) \ (I.outset m)
      apply Finset.mem_sdiff.mp at hx
      have hx : ⟨n,x⟩ ∈ I.set := (outset_char I n x).mp hx.1
      have := I.tf m n x
      tauto
  rw [this]

  suffices (slice_set I n m).card =
    ((I.inset n).filter (· < m)).card
    + ((I.outset m).filter (· > n)).card
    + (Finset.Icc m n).card by
    rw [this]; simp; ring

  rw [slice_card]

  have : (I.inset n \ I.inset m).card
    = ((I.inset n).filter (· < m)).card
    + ((Finset.Icc m n).filter (· ∈ I.inset n)).card := by
    refine card_sum_helper ?_ ?_
    · -- Show the set is a union
      ext x
      constructor
      rw [Finset.mem_union]
      · intro x_in
        apply Finset.mem_sdiff.mp at x_in
        -- rw [inset_char I n x, inset_char I m x] at x_in
        by_cases x_lt_m : x < m
        · left; simp only [Finset.mem_filter]
          exact ⟨x_in.1, x_lt_m⟩
        · right; simp only [Finset.mem_filter]
          have m_le_x : m ≤ x := by linarith
          have x_le_n : x ≤ n := by
            have := I.dir _ _ ((inset_char I n x).mp x_in.1)
            linarith
          simp [x_in.1, x_le_n, m_le_x]
      · intro h_x; rw [Finset.mem_union] at h_x
        repeat rw [Finset.mem_filter] at h_x
        rcases h_x with (h_x | h_x)
        · simp [h_x]
          intro x_in
          have :=  I.tf x m n
          tauto
        · simp [h_x]
          intro x_im
          have := I.tf x m n
          tauto
    · -- Show the sets are disjoint
      intro x
      by_contra! h
      obtain ⟨x_small, x_big⟩ := h
      have x_lt_m : x < m := ((Finset.mem_filter).mp x_small).2
      have x_ge_m : m ≤ x := by
        have := ((Finset.mem_filter).mp x_big).1
        simp at this; tauto
      linarith
  rw [this]

  have : (I.outset m \ I.outset n).card
    = ((I.outset m).filter (· > n)).card
    + ((Finset.Icc m n).filter (· ∈ I.outset m)).card := by
    refine card_sum_helper ?_ ?_
    · -- Show the set is a union
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_union, outset_char]
      constructor
      · rintro ⟨I_mx, I_xn⟩
        simp [I_mx]
        by_cases n_lt_x : n < x
        · left; exact n_lt_x
        right; have x_le_n : x ≤ n := by linarith
        suffices m ≤ x by tauto
        have : m < x := I.dir _ _ I_mx
        linarith
      · intro h_x
        suffices ⟨n,x⟩ ∉ I.set by tauto
        intro I_nx
        have := I.tf m n x
        tauto
    · -- Show the sets are disjoint
      intro x
      simp only [Finset.mem_filter, Finset.mem_Icc, outset_char]
      by_contra! h
      obtain ⟨x_big, x_small⟩ := h
      have x_gt_n : x > n := x_big.2
      have x_le_n : x ≤ n := x_small.1.2
      linarith
  rw [this]

  suffices (Finset.Icc m n).card = ((Finset.Icc m n).filter (· ∈ I.inset n)).card
    + ((Finset.Icc m n).filter (· ∈ I.outset m)).card by
    simp [this]; ring

  let A := (Finset.Icc m n).filter (· ∈ I.inset n)
  let B := (Finset.Icc m n).filter (· ∈ I.outset m)
  change (Finset.Icc m n).card = A.card + B.card

  have : Finset.Icc m n = A ∪ B := by
    ext x
    rw [Finset.mem_union]

    constructor
    · intro x_Icc
      have : m ≤ x ∧ x ≤ n := by
        simp at x_Icc; assumption
      obtain ⟨m_le_x, x_le_n⟩ := this

      -- Reduce to the case m < x < n
      by_cases x_eq_m : m = x
      · left; dsimp [A]; simp [x_Icc]
        rw [← x_eq_m]; exact I_mn
      have m_lt_x : m < x := lt_of_le_of_ne m_le_x x_eq_m
      by_cases x_eq_n : x = n
      · right; dsimp [B]; simp [x_Icc]
        rw [x_eq_n]; exact I_mn
      have x_lt_n : x < n := lt_of_le_of_ne x_le_n x_eq_n

      have := I.cc m n x I_mn m_lt_x x_lt_n
      dsimp [A,B]
      simp [x_Icc]
      tauto
    · intro hx; dsimp [A,B] at hx
      rcases hx with (hx | hx) <;> (rw [Finset.mem_filter] at hx; tauto)

  rw [this]
  refine card_sum_helper (by rfl) ?_
  intro x
  by_contra! h
  obtain ⟨x_A, x_B⟩ := h
  have xn_I : ⟨x,n⟩ ∈ I.set := by
    dsimp [A] at x_A; simp at x_A; exact x_A.2
  have mx_I : ⟨m, x⟩ ∈ I.set := by
    dsimp [B] at x_B; simp at x_B; exact x_B.2
  have :=  I.tf m x n
  tauto

lemma σ_injective : Function.Injective (σ I) := by
  have helper (m n : ℤ) (m_lt_n : m < n) : σ I m ≠ σ I n := by
    by_cases I_mn : ⟨m, n⟩ ∈ I.set
    · -- Case 1: ⟨m,n⟩ ∈ I.set
      have := dec_pair I I_mn
      intro h
      linarith
    · -- Case 2: ⟨m,n⟩ ∉ I.set
      have := inc_pair I m_lt_n I_mn
      intro h
      linarith
  intro m n h
  by_cases m_lt_n : m < n
  · have := helper m n m_lt_n
    tauto
  · contrapose! helper with m_ne_n
    have : n < m := by
      apply lt_of_le_of_ne (le_of_not_gt m_lt_n)
      tauto
    use n, m
    rw [h]
    exact ⟨this, rfl⟩

lemma σ_inv : inv_set (σ I) = I.set := by
  ext ⟨m,n⟩
  simp [inv_set]
  constructor
  · rintro ⟨m_lt_n, σ_lt⟩
    contrapose! σ_lt with I_mn
    have := inc_pair I m_lt_n I_mn
    linarith
  · intro I_mn
    have := dec_pair I I_mn
    suffices σ I n < σ I m by
      exact ⟨I.dir _ _ I_mn, this⟩
    linarith

lemma σ_is_321a : is_321a (σ I) := by
  have set_eq : inv_set (σ I) = I.set := σ_inv I
  intro u v w u_lt_v v_lt_w
  have h_tf := I.tf u v w
  rw [← set_eq] at h_tf
  unfold inv_set at h_tf
  simp [u_lt_v, v_lt_w] at h_tf
  rcases h_tf with (h_tf | h_tf)
  · left
    apply lt_of_le_of_ne h_tf
    intro heq
    apply σ_injective I at heq
    linarith
  · right
    apply lt_of_le_of_ne h_tf
    intro heq
    apply σ_injective I at heq
    linarith

def inv_index (m n : ℤ) : ℤ := m + ((Finset.Ico m n).filter (· ∈ I.outset m)).card

def inv_index' (m n : ℤ) : ℤ := n - ((Finset.Ico m n).filter (· ∈ I.inset n)).card

lemma inv_index_eq {m n : ℤ} (I_mn : ⟨m, n⟩ ∈ I.set) : inv_index I m n = inv_index' I m n := by
  have m_lt_n : m < n := I.dir _ _ I_mn
  suffices (Finset.Ico m n).card
    = ((Finset.Ico m n).filter (· ∈ I.outset m)).card
    + ((Finset.Ico m n).filter (· ∈ I.inset n)).card by
    have h : (Finset.Ico m n).card = (n-m).toNat := by simp
    have h' : ( (Finset.Ico m n).card : ℤ) = n - m := by
      rw [h]; simp [le_of_lt m_lt_n]
    rw [h] at this
    dsimp [inv_index, inv_index']
    linarith

  refine card_sum_helper ?_ ?_
  · -- Check the set is a union
    ext x
    simp
    constructor
    · intro x_in
      simp [x_in]
      by_cases x_eq_m : x = m
      · right; rw [x_eq_m]; exact I_mn
      have m_lt_x : m < x := by
        apply lt_of_le_of_ne (x_in.1)
        tauto
      exact I.cc m n x I_mn m_lt_x x_in.2
    · -- Converse
      intro h_x
      rcases h_x with (h | h) <;> exact h.1
  · -- Check the sets are disjoint
    intro x
    by_contra! h
    obtain ⟨x_out, x_in⟩ := h
    have mx_I : ⟨m,x⟩ ∈ I.set := by
      rw [Finset.mem_filter] at x_out
      simp at x_out; tauto
    have xn_I : ⟨x,n⟩ ∈ I.set := by
      rw [Finset.mem_filter] at x_in
      simp at x_in; tauto
    have := I.tf m x n
    tauto

def move_right (m n : ℤ) : WithTop ℤ :=
  Finset.min ((I.outset m).filter (· > n))

lemma inv_index_right {m n n' : ℤ} (I_mn : ⟨m, n⟩ ∈ I.set) (h_right : move_right I m n = some n') :
  inv_index I m n' = inv_index I m n + 1 := by
  unfold inv_index
  suffices (Finset.Ico m n').filter (· ∈ I.outset m)
    = (Finset.Ico m n).filter (· ∈ I.outset m) ∪ {n} by
    rw [this]
    simp; ring
  ext x
  simp [Finset.mem_filter]
  by_cases I_mx : ⟨m,x⟩ ∉ I.set
  · -- Case 1: ⟨m,x⟩ ∉ I.set
    simp [I_mx]
    intro x_eq_n
    rw [x_eq_n] at I_mx
    exact I_mx I_mn
  -- Case 2: ⟨m,x⟩ ∈ I.set
  push_neg at I_mx; simp [I_mx]
  have : m ≤ x := by
    have := I.dir _ _ I_mx
    linarith
  simp [this]
  suffices n < n' ∧ (x < n' → x ≤ n) by
    obtain ⟨n_lt_n', h⟩ := this
    constructor
    · intro h'
      apply h at h'
      apply le_iff_lt_or_eq.mp at h'
      tauto
    · intro h'
      rcases h' with (h' | h')
      · rw [h']
        exact n_lt_n'
      · exact lt_trans h' n_lt_n'
  unfold move_right at h_right
  have : (x > n → x ≥ n') := by
    intro n_lt_x
    refine Finset.min_le_of_eq ?_ h_right
    rw [Finset.mem_filter]
    simp; tauto
  constructor
  · have := Finset.mem_of_min h_right
    simp at this
    exact this.2
  · intro h
    contrapose! h
    exact this h

lemma inv_index_right_bot {m n : ℤ} (I_mn : ⟨m, n⟩ ∈ I.set) (h_right : move_right I m n = ⊤) :
  inv_index I m n + 1= σ I m := by
  unfold inv_index σ
  have : (I.inset m).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_of_forall_notMem
    intro x x_in
    have : ⟨x, m⟩ ∈ I.set := by
      rw [inset_char I m x] at x_in
      exact x_in
    have := I.tf x m n
    tauto
  rw [this, Nat.cast_zero, sub_zero]

  have : (I.outset m) = ((I.outset m).filter (· < n) ) ∪ {n}  := by
    ext x
    rw [Finset.mem_union, Finset.mem_filter]
    simp
    constructor
    · intro h; simp [h]
      suffices x ≤ n by
        rw [← le_iff_lt_or_eq]
        exact this
      unfold move_right at h_right
      rw [Finset.min_eq_top, Finset.eq_empty_iff_forall_notMem] at h_right
      specialize h_right x
      simp at h_right
      exact h_right h
    · intro h
      rcases h with (h | h)
      · exact h.1
      · rw [h]; exact I_mn

  have : (I.outset m).card = ((I.outset m).filter (· < n)).card + 1 := by
    nth_rewrite 1 [this]
    rw [Finset.card_union]
    simp
  rw [this]

  suffices {x ∈ Finset.Ico m n | x ∈ I.outset m} = {x ∈ I.outset m | x < n} by
    rw [this]; simp; ring

  ext x
  simp
  constructor
  · intro h
    tauto
  · intro h
    suffices m ≤ x by tauto
    have := I.dir _ _ h.1
    exact le_of_lt this

-- Now prove ``move left'' versions of the two lemmas above...

def move_left (m n : ℤ) : WithBot ℤ :=
  Finset.max ((I.inset n).filter (· < m))

lemma inv_index_left {m n m' : ℤ} (I_mn : ⟨m, n⟩ ∈ I.set) (h_left : move_left I m n = some m') :
  inv_index I m' n = inv_index I m n - 1 := by

  unfold move_left at h_left
  have m'_mem := Finset.mem_of_max h_left
  rw [Finset.mem_filter] at m'_mem
  obtain ⟨I_m'n, m'_lt_m⟩ := m'_mem
  simp at I_m'n

  repeat rw [inv_index_eq I I_mn, inv_index_eq I I_m'n]
  unfold inv_index'

  suffices (Finset.Ico m' n).filter (· ∈ I.inset n)
    = (Finset.Ico m n).filter (· ∈ I.inset n) ∪ {m'} by
    rw [this, Finset.card_union, Finset.card_singleton]
    have : ({x ∈ Finset.Ico m n | x ∈ I.inset n} ∩ {m'}) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x x_in
      rw [Finset.mem_inter, Finset.mem_singleton] at x_in
      obtain ⟨x_in_xo, x_eq_m⟩ := x_in
      rw [Finset.mem_filter] at x_in_xo
      rw [x_eq_m] at x_in_xo
      have : m ≤ m' := by
        have := x_in_xo.1
        simp at this
        exact this.1
      linarith
    rw [this, Finset.card_empty]
    simp [Nat.cast_add]
    linarith

  ext x
  simp
  by_cases I_xn : ⟨x,n⟩ ∉ I.set
  · -- Case 1: ⟨x,n⟩ ∉ I.set
    simp [I_xn]
    intro x_eq_m
    rw [x_eq_m] at I_xn
    exact I_xn I_m'n
  · -- Case 2: ⟨x,n⟩ ∈ I.set
    push_neg at I_xn; simp [I_xn]
    constructor
    · intro h
      simp [h]
      by_cases x_lt_m : x < m
      · have : x ≤ m' := by
          refine Finset.le_max_of_eq ?_ h_left
          rw [Finset.mem_filter]
          simp; tauto
        left; linarith
      · right; linarith
    · intro h
      rcases h with (h | h)
      · simp [h]
        exact I.dir _ _ I_m'n
      · simp [h]
        by_cases x_lt_m : x < m
        · have : x ≤ m' := by
            refine Finset.le_max_of_eq ?_ h_left
            rw [Finset.mem_filter]
            simp; tauto
          linarith
        · linarith

lemma inv_index_left_bot {m n : ℤ} (I_mn : ⟨m, n⟩ ∈ I.set) (h_left : move_left I m n = ⊥) :
  inv_index I m n  = σ I n := by
  rw [inv_index_eq I I_mn]
  unfold inv_index' σ
  have : (I.outset n).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_of_forall_notMem
    intro x x_in
    have : ⟨n, x⟩ ∈ I.set := by
      rw [outset_char I n x] at x_in
      exact x_in
    have tf := I.tf m n x
    tauto
  rw [this, Nat.cast_zero, add_zero]

  congr; ext x; simp
  intro I_xn
  simp [I.dir _ _ I_xn]
  unfold move_left at h_left
  rw [Finset.max_eq_bot, Finset.eq_empty_iff_forall_notMem] at h_left
  specialize h_left x
  simp at h_left
  exact h_left I_xn

lemma helper_zigzag {m n : ℤ} (I_mn : ⟨m, n⟩ ∈ I.set) (ε : ℤ) : (ε = 0 ∨ ε = 1 )
  → ∃ k : ℤ, σ I k  = inv_index I m n + ε := by
  intro hε
  rcases hε with (hε | hε)
  · -- Case 1: ε = 0
    rw [hε]
    match hml : move_left I m n with
    | some m' =>
      have m'_mem := Finset.mem_of_max hml
      rw [Finset.mem_filter] at m'_mem
      simp at m'_mem
      obtain ⟨I_m'n, m'_lt_m⟩ := m'_mem
      have : ⟨m', n⟩ ∈ I.set := by
        unfold move_left at hml
        exact I_m'n
      have := helper_zigzag this 1 (by norm_num)
      rcases this with ⟨k, hk⟩
      use k; rw [hk, inv_index_left I I_mn hml]
      norm_num
    | ⊥ =>
      use n
      simp [inv_index_left_bot I I_mn hml]
  · -- Case 2: ε = 1
    rw [hε]
    match hmr : move_right I m n with
    | some n' =>
      have n'_mem := Finset.mem_of_min hmr
      rw [Finset.mem_filter] at n'_mem
      simp at n'_mem
      obtain ⟨I_mn', n_lt_n'⟩ := n'_mem
      have : ⟨m, n'⟩ ∈ I.set := by
        unfold move_right at hmr
        exact I_mn'
      have := helper_zigzag this 0 (by norm_num)
      rcases this with ⟨k, hk⟩
      use k; rw [hk, inv_index_right I I_mn hmr]
      norm_num
    | ⊤ =>
      use m
      simp [inv_index_right_bot I I_mn hmr]
termination_by _ => (σ I m - σ I n).toNat
decreasing_by
  · have inv_eq := σ_inv I
    have h2 : ⟨m,n⟩ ∈ I.set := I_mn
    suffices σ I m' < σ I m ∧ σ I n < σ I m by
      obtain ⟨h1, h2⟩ := this
      simp; exact ⟨h1, h2⟩
    have h1 : ⟨m',m⟩ ∉ I.set := by
      intro h
      have tf := I.tf m' m n
      tauto
    rw [← inv_eq] at h1 h2
    unfold inv_set at h1 h2
    simp [h2.2]
    contrapose! h1
    have σ_m_lt_m' : σ I m < σ I m' := by
      apply lt_of_le_of_ne h1
      intro σ_eq
      have m_eq_m' : m = m' := by
        apply σ_injective I σ_eq
      rw [m_eq_m'] at m'_lt_m
      linarith
    exact ⟨m'_lt_m, σ_m_lt_m'⟩
  · suffices σ I n < σ I n' ∧ σ I n < σ I m by
      obtain ⟨h1, h2⟩ := this
      simp; exact ⟨h1, h2⟩
    have h1 : ⟨n,n'⟩ ∉ I.set := by
      intro h
      have tf := I.tf m n n'
      tauto
    have inv_eq := σ_inv I
    have h2 : ⟨m,n⟩ ∈ I.set := I_mn
    rw [← inv_eq] at h1 h2
    unfold inv_set at h1 h2
    simp [h2.2]
    contrapose! h1
    have σ_n'_lt_n : σ I n' < σ I n := by
      apply lt_of_le_of_ne h1
      intro σ_eq
      have n_eq_n' : n' = n := by
        apply σ_injective I σ_eq
      rw [n_eq_n'] at n_lt_n'
      linarith
    exact ⟨n_lt_n', σ_n'_lt_n⟩

lemma σ_surjective : Function.Surjective (σ I) := by
  intro y
  by_cases hy : σ I y = y
  · use y
  -- Now assume σ y ≠ y

  have : (I.inset y).Nonempty ∨ (I.outset y).Nonempty := by
    by_contra! h'
    simp at h'
    obtain ⟨h1, h2⟩ := h'
    push_neg at h1 h2
    unfold σ at hy
    let h1 : I.inset y = ∅ := by simp [h1]
    let h2 : I.outset y = ∅ := by simp [h2]
    rw [h1, h2, Finset.card_empty] at hy
    simp at hy

  rcases this with (y_snk | y_src)
  · -- Case 1: there is an edge into y
    let u := Finset.max' (I.inset y) (by simpa using y_snk)
    have I_uy : u ∈ I.inset y := Finset.max'_mem (I.inset y) (by simpa using y_snk)
    simp at I_uy
    have h_index : inv_index I u y = y -1 := by
      rw [inv_index_eq I I_uy]
      unfold inv_index'
      suffices {x ∈ Finset.Ico u y | x ∈ I.inset y} = {u} by
        rw [this, Finset.card_singleton, Nat.cast_one]
      ext u'; simp
      constructor
      · intro u'_in
        simp at u'_in
        have : u' ≤ u := by
          apply Finset.le_max' (I.inset y)
          simp [u'_in]
        linarith
      · intro u'_eq
        rw [u'_eq]; simp [I_uy, I.dir _ _ I_uy]
    have := helper_zigzag I I_uy 1 (by norm_num)
    rcases this with ⟨k, hk⟩
    use k; linarith
  · -- Case 2: there is an edge out of y
    let v := Finset.min' (I.outset y) (by simpa using y_src)
    have I_yv : v ∈ I.outset y := Finset.min'_mem (I.outset y) (by simpa using y_src)
    simp at I_yv
    have h_index : inv_index I y v = y  := by
      unfold inv_index
      suffices {x ∈ Finset.Ico y v | x ∈ I.outset y} = ∅ by
        rw [this, Finset.card_empty, Nat.cast_zero, add_zero]
      ext v'; simp
      intro y_le_v' v'_lt_v
      by_contra! h
      have : v ≤ v' := Finset.min'_le (I.outset y) v' (by simp [h])
      linarith
    have := helper_zigzag I I_yv 0 (by norm_num)
    rcases this with ⟨k, hk⟩
    use k; linarith

lemma σ_perm : Function.Bijective (σ I) := by
  exact ⟨σ_injective I, σ_surjective I⟩

end

theorem inv_321a_char (I : Set (ℤ × ℤ)) :
  I_321a_prop I
  ↔ (∃ τ : (ℤ → ℤ), (is_321a τ ∧ Function.Bijective τ ∧ inv_set τ = I)) := by
  constructor
  · intro Ip
    let I_struc : I_321a := ⟨I, Ip⟩
    let τ : ℤ → ℤ := σ I_struc
    use τ
    constructor
    · exact σ_is_321a I_struc
    constructor
    · exact σ_perm I_struc
    · exact σ_inv I_struc
  · rintro ⟨τ, ⟨h_321a, h_bij, h_inv⟩⟩
    have := (criterion_321a τ h_bij).mp h_321a
    rwa [h_inv] at this
