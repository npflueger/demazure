import Demazure.Utils
import Demazure.SlipFace
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Set.Card

def inv_set (τ : ℤ → ℤ) : Set (ℤ × ℤ) :=
  {(i,j) : ℤ × ℤ | i < j ∧ τ j < τ i}

def southeast_set (τ : ℤ → ℤ) (m n : ℤ) : Set ℤ := { k : ℤ | n ≤ k ∧ τ k < m }

def northwest_set (τ : ℤ → ℤ) (m n : ℤ) : Set ℤ := { k : ℤ | k < n ∧ m ≤ τ k }

abbrev flip_func (f : ℤ → ℤ) : ℤ → ℤ := fun k => -1 - f (-1 - k)

lemma flip_quadrant (f : ℤ → ℤ) (a b : ℤ) :
  (-1 - ·) '' (southeast_set f a b) = northwest_set (flip_func f) (-a) (-b) := by
  ext n
  simp only [Set.mem_image, southeast_set, northwest_set, Set.mem_setOf_eq, flip_func]
  constructor
  · rintro ⟨m, ⟨hm1, hm2⟩, rfl⟩
    constructor
    · omega
    · have hfm : f (-1 - (-1 - m)) = f m := by congr; omega
      rw [hfm]
      omega
  · intro ⟨hn1, hn2⟩
    exact ⟨-1 - n, ⟨by omega, by omega⟩, by ring_nf⟩

lemma se_finite_of_finite {τ : ℤ → ℤ} (h_inj : Function.Injective τ) (m n m' n' : ℤ) :
  (southeast_set τ m n).Finite → (southeast_set τ m' n').Finite := by
  let A := southeast_set τ m n
  let B := southeast_set τ m' n'
  let V := (Finset.Ico n' n).toSet
  let H₀ := (Finset.Ico m m').toSet
  let H := τ⁻¹' H₀

  change A.Finite → B.Finite
  intro fin_A

  have fin_V : V.Finite := Finset.finite_toSet _
  have fin_H₀ : H₀.Finite := Finset.finite_toSet _
  have fin_H : H.Finite := fin_H₀.preimage (Set.injOn_of_injective h_inj)

  have h : B ⊆ A ∪ (H ∪ V) := by
    intro k hk
    simp [A, B] at hk ⊢
    unfold southeast_set at *
    by_cases k_lt_n : k < n
    · right; right
      simp only [V]
      simp [hk.1, k_lt_n]
    obtain k_ge_n : k ≥ n := by
      push_neg at k_lt_n; exact k_lt_n
    by_cases τk_ge_m : τ k ≥ m
    · right; left
      simp only [H, H₀]
      simp [τk_ge_m, hk.2]
    obtain τk_lt_m : τ k < m := by
      push_neg at τk_ge_m; exact τk_ge_m
    left; exact ⟨k_ge_n, τk_lt_m⟩

  refine Set.Finite.subset ?_ h
  exact Set.Finite.union fin_A (Set.Finite.union fin_H fin_V)

lemma nw_finite_of_finite {τ : ℤ → ℤ} (h_inj : Function.Injective τ) (m n m' n' : ℤ) :
  (northwest_set τ m n).Finite → (northwest_set τ m' n').Finite := by
  have hff : flip_func (flip_func τ) = τ := by
    funext n
    simp [flip_func]
  have hf_inj : Function.Injective (flip_func τ) := fun x y h => by
    unfold flip_func at h
    linarith [h_inj (show τ (-1 - x) = τ (-1 - y) from by omega)]
  have key : ∀ a b : ℤ, (northwest_set τ a b).Finite ↔
      (southeast_set (flip_func τ) (-a) (-b)).Finite := fun a b => by
    have hq := flip_quadrant (flip_func τ) (-a) (-b)
    simp only [hff, neg_neg] at hq
    rw [show northwest_set τ a b = (-1 - ·) '' southeast_set (flip_func τ) (-a) (-b) from hq.symm]
    exact ⟨fun h => h.of_finite_image (Set.injOn_of_injective (fun x y h => by omega)),
           fun h => h.image _⟩
  rw [key m n, key m' n']
  exact se_finite_of_finite hf_inj (-m) (-n) (-m') (-n')

def is_asp (τ : ℤ → ℤ) : Prop :=
  { n : ℤ | n * (τ n) < 0 }.Finite

lemma se_finite_of_asp {τ : ℤ → ℤ} (h_inj : Function.Injective τ) (m n : ℤ) :
  is_asp τ → (southeast_set τ m n).Finite := by
  intro h_asp
  have h_se : (southeast_set τ 0 1).Finite := by
    unfold is_asp at h_asp
    have : southeast_set τ 0 1 ⊆ { n : ℤ | n * (τ n) < 0 } := by
      intro k hk
      simp [southeast_set] at hk
      obtain ⟨k_pos, τk_neg⟩ := hk
      have : k > 0 := by omega
      exact mul_neg_of_pos_of_neg this τk_neg
    exact Set.Finite.subset h_asp this
  exact se_finite_of_finite h_inj 0 1 m n h_se

lemma nw_finite_of_asp {τ : ℤ → ℤ} (h_inj : Function.Injective τ) (m n : ℤ) :
  is_asp τ → (northwest_set τ m n).Finite := by
  intro h_asp
  have h_nw : (northwest_set τ 1 0).Finite := by
    unfold is_asp at h_asp
    have : northwest_set τ 1 0 ⊆ { n : ℤ | n * (τ n) < 0 } := by
      intro k hk
      simp [northwest_set] at hk
      obtain ⟨k_neg, τk_pos⟩ := hk
      have : τ k > 0 := by omega
      exact mul_neg_of_neg_of_pos k_neg this
    exact Set.Finite.subset h_asp this
  exact nw_finite_of_finite h_inj 1 0 m n h_nw

lemma asp_of_finite_quadrants {τ : ℤ → ℤ} (h_inj : Function.Injective τ)
  {m n m' n' : ℤ} (fin_se : (southeast_set τ m n).Finite)
  (fin_nw : (northwest_set τ m' n').Finite) :
  is_asp τ := by
  unfold is_asp
  have : { n : ℤ | n * (τ n) < 0 } ⊆ (southeast_set τ 0 1) ∪ (northwest_set τ 1 0) := by
    intro n hn; simp at hn
    have := mul_neg_iff.mp hn
    rcases this with (pos_neg | neg_pos)
    · left
      unfold southeast_set
      simp; congr
    · right
      unfold northwest_set
      simp; congr
  refine Set.Finite.subset ?_ this
  apply Set.Finite.union
  · exact se_finite_of_finite h_inj m n 0 1 fin_se
  · exact nw_finite_of_finite h_inj m' n' 1 0 fin_nw

structure AspPerm where
  func : ℤ → ℤ
  bijective : Function.Bijective func
  asp : is_asp func

instance : CoeFun AspPerm (fun _ => ℤ → ℤ) :=
  ⟨AspPerm.func⟩

namespace AspPerm
variable (τ : AspPerm)

lemma injective : Function.Injective τ.func := τ.bijective.injective

lemma surjective : Function.Surjective τ.func := τ.bijective.surjective

-- Lemmas for convenience, to handle edge cases involving i = j
lemma inv_iff_lt {i j : ℤ} (i_le_j : i ≤ j) :
  ⟨i, j⟩ ∈ inv_set τ ↔  τ j < τ i := by
  rw [inv_set]
  wlog i_lt_j : i < j
  · have i_eq_j : i = j := le_antisymm i_le_j (le_of_not_gt i_lt_j)
    rw [i_eq_j]; simp
  constructor
  · intro ij_inv
    exact ij_inv.2
  · intro τ_j_lt_i
    exact ⟨i_lt_j, τ_j_lt_i⟩
lemma inv_iff_le {i j : ℤ} (i_lt_j : i < j) :
  ⟨i, j⟩ ∈ inv_set τ ↔ τ j ≤ τ i := by
  constructor
  · intro ij_inv
    exact le_of_lt ij_inv.2
  · intro τ_j_le_i
    have : τ j ≠ τ i := by
      intro heq
      apply τ.injective at heq
      rw [heq] at i_lt_j; exact lt_irrefl i i_lt_j
    exact ⟨i_lt_j, lt_of_le_of_ne τ_j_le_i this⟩

@[simp] lemma ext {σ τ : AspPerm} : σ = τ ↔ σ.func = τ.func := by
  constructor
  · intro h; rw [h]
  · intro h; cases σ; cases τ; congr

def mul (σ τ : AspPerm) : AspPerm where
  func := Function.comp σ.func τ.func
  bijective :=
    Function.Bijective.comp σ.bijective τ.bijective
  asp := by
    have : {n | n * (σ (τ n)) < 0}
      ⊆ {n | n * (τ n) < 0} ∪ {n | (τ n) * (σ (τ n)) < 0} ∪ { n | τ n = 0}:= by
      intro n hn
      contrapose! hn
      simp at hn ⊢
      obtain ⟨⟨hτ, hσ⟩, h0⟩ := hn
      have h := mul_nonneg hσ hτ
      let C := (τ n) ^ 2
      have h' : n * (σ (τ n)) * C ≥ 0 := by
        linarith
      have h'' : C > 0 := by
        simp [C]
        exact pow_two_pos_of_ne_zero h0
      contrapose! h'
      exact mul_neg_of_neg_of_pos h' h''
    refine Set.Finite.subset ?_ this
    have h_pre : Set.Finite {n | τ n * σ (τ n) < 0} := by
      have h : {n | τ n * σ (τ n) < 0} = τ ⁻¹' {n | n * σ n < 0} := by
        ext n
        simp
      rw [h]
      exact Set.Finite.preimage (Set.injOn_of_injective τ.injective) σ.asp
    have h_zero : Set.Finite {n | τ n = 0} := by
      have h : {n | τ n = 0} = τ ⁻¹' ({0} : Set ℤ) := by
        ext n
        simp
      rw [h]
      exact Set.Finite.preimage (Set.injOn_of_injective τ.injective) (Set.finite_singleton 0)
    exact Set.Finite.union (Set.Finite.union τ.asp h_pre) h_zero

noncomputable def inv (τ : AspPerm) : AspPerm where
  func := Function.invFun τ.func
  bijective := by
    have hR : Function.RightInverse (Function.invFun τ.func) τ.func :=
      Function.rightInverse_invFun τ.surjective
    have hL : Function.LeftInverse (Function.invFun τ.func) τ.func :=
      Function.leftInverse_invFun τ.injective
    exact ⟨hR.injective, hL.surjective⟩
  asp := by
    refine Set.Finite.of_preimage ?_ τ.surjective
    suffices (τ.func ⁻¹' {n | n * Function.invFun τ.func n < 0}) = {n | n * τ n < 0} by
      rw [this]
      exact τ.asp
    ext n
    have := Function.leftInverse_invFun τ.injective n
    simp [this, mul_comm]

def id : AspPerm where
  func := _root_.id
  bijective := ⟨Function.injective_id, Function.surjective_id⟩
  asp := by
    have : {n:ℤ | n * _root_.id n < 0} = ∅ := by
      ext n; simp
      exact mul_self_nonneg n
    unfold is_asp; rw [this]
    exact Set.finite_empty

noncomputable instance : Group AspPerm where
  mul := mul
  inv := inv
  one := id
  mul_assoc := by intros a b c; rfl
  one_mul := by intro a; rfl
  mul_one := by intro a; rfl
  inv_mul_cancel := by
    intro τ
    apply (ext).2
    funext n
    change Function.invFun τ.func (τ.func n) = n
    exact Function.leftInverse_invFun τ.injective n

@[simp] lemma inv_mul_cancel_eval (n : ℤ) : τ⁻¹ (τ n) = n := by
  change Function.invFun τ.func (τ.func n) = n
  exact Function.leftInverse_invFun τ.injective n

@[simp] lemma mul_inv_cancel_eval (n : ℤ) : τ (τ⁻¹ n) = n := by
  change τ.func (Function.invFun τ.func n) = n
  exact Function.rightInverse_invFun τ.surjective n

lemma se_finite (a b : ℤ) : (southeast_set τ a b).Finite := se_finite_of_asp τ.injective a b τ.asp

lemma nw_finite (a b : ℤ) : (northwest_set τ a b).Finite := nw_finite_of_asp τ.injective a b τ.asp

noncomputable def se_finset (a b : ℤ) : Finset ℤ := (τ.se_finite a b).toFinset

@[simp] lemma mem_se (a b n : ℤ) : n ∈ (τ.se_finset a b) ↔ n ≥ b ∧ τ n < a := by
  unfold se_finset southeast_set
  simp

noncomputable def nw_finset (a b : ℤ) : Finset ℤ := (τ.nw_finite a b).toFinset

@[simp] lemma mem_nw (a b n : ℤ) : n ∈ (τ.nw_finset a b) ↔ n < b ∧ τ n ≥ a := by
  unfold nw_finset northwest_set
  simp

lemma inv_set_inverse (u v : ℤ) : ⟨u, v⟩ ∈ inv_set τ ↔ ⟨τ v, τ u⟩ ∈ inv_set τ⁻¹.func := by
  constructor
  · intro h
    obtain ⟨u_lt_v, τv_lt_τu⟩ := h
    use τv_lt_τu
    simpa
  · intro h
    obtain ⟨τv_lt_τu, u_lt_v⟩ := h
    simp at u_lt_v
    exact ⟨u_lt_v, τv_lt_τu⟩

noncomputable def s (a b : ℤ) : ℤ := ↑(southeast_set τ a b).ncard
noncomputable def s' (b a : ℤ) : ℤ := ↑(northwest_set τ a b).ncard
noncomputable def χ : ℤ := τ.s 0 0 - τ.s' 0 0

lemma s_eq_se_card (a b : ℤ) : τ.s a b = (τ.se_finset a b).card := by
  unfold AspPerm.s se_finset
  rw [Set.ncard_eq_toFinset_card _ (τ.se_finite a b)]

lemma s'_eq_nw_card (b a : ℤ) : τ.s' b a = (τ.nw_finset a b).card := by
  unfold AspPerm.s' nw_finset
  rw [Set.ncard_eq_toFinset_card _ (τ.nw_finite a b)]


lemma s_nonneg (a b : ℤ) : τ.s a b ≥ 0 := by
  unfold s
  exact Nat.cast_nonneg _

lemma s'_nonneg (a b : ℤ) : τ.s' a b ≥ 0 := by
  unfold s'
  exact Nat.cast_nonneg _

-- The s'-value at τ u (from the left of b) is positive whenever u < b.
lemma s'_pos_of_lt {u b : ℤ} (u_lt_b : u < b) : τ.s' b (τ u) ≥ 1 := by
  simp only [s']
  have h_nonempty : ↑(northwest_set τ (τ u) b).Nonempty := by use u, u_lt_b
  have := (Set.ncard_pos (τ.nw_finite (τ u) b)).mpr h_nonempty
  omega

lemma dual_inverse : τ.s' = (τ⁻¹).s := by
  funext b a
  calc
    τ.s' b a = (northwest_set τ a b).ncard := by rfl
    _ = ( τ.func '' (northwest_set τ a b)).ncard := by
      rw [Set.ncard_image_of_injective (northwest_set τ a b) τ.injective]
    _ = (southeast_set τ⁻¹.func b a).ncard := by
      congr
      ext n
      constructor
      · intro h; unfold southeast_set
        rcases h with ⟨m, hm, rfl⟩; simp
        exact ⟨hm.2, hm.1⟩
      · intro h
        use τ⁻¹ n
        unfold northwest_set; unfold southeast_set at h
        obtain ⟨a_le_n, τin_lt_b⟩ := h
        simpa using ⟨τin_lt_b, a_le_n⟩
    _ = (τ⁻¹).s b a := by rfl

lemma χ_dual : τ⁻¹.χ = - τ.χ := by
  dsimp [AspPerm.χ]
  simp only [AspPerm.dual_inverse, inv_inv]
  norm_num

lemma χ_dual' : τ.χ = - (τ⁻¹).χ := by
  rw [← χ_dual τ⁻¹, inv_inv]

lemma flip_bij (τ : AspPerm) : Function.Bijective (flip_func τ.func) := by
  constructor
  · intro x y h; simp at h
    apply τ.injective at h
    omega
  · intro y
    use -1 - τ⁻¹ (-1 - y)
    simp [flip_func]

def flip : AspPerm := {
  func := fun n => -1 - τ (-1 - n)
  bijective := flip_bij τ
  asp := by
    let f := flip_func τ
    let g := fun n => -1 - n
    change is_asp f
    have hinj : Function.Injective f := (flip_bij τ).injective
    have : g '' (southeast_set τ 0 0) = northwest_set f 0 0 := by
      exact flip_quadrant τ 0 0
    have nw_finite : (northwest_set f 0 0).Finite := by
      rw [← this]
      apply Set.Finite.image g
      exact se_finite_of_asp τ.injective 0 0 τ.asp
    have : g '' (southeast_set f 0 0) = northwest_set τ 0 0 := by
      have h := flip_quadrant f 0 0
      have : flip_func f = τ := by
        funext n
        simp [flip_func, f]
      rw [this] at h
      exact h
    have se_finite : (southeast_set f 0 0).Finite := by
      have h : (g '' (southeast_set f 0 0)).Finite := by
        rw [this]
        exact nw_finite_of_asp τ.injective 0 0 τ.asp
      have h_inj : Set.InjOn g (southeast_set f 0 0) := by
        intro x _ y _ h
        linarith
      exact Set.Finite.of_finite_image h h_inj
    exact asp_of_finite_quadrants hinj se_finite nw_finite
}

lemma flip_inv : τ.flip⁻¹ = τ⁻¹.flip := by
  simp; ext n
  suffices τ.flip (τ.flip⁻¹ n) = τ.flip (τ⁻¹.flip n) by
    exact τ.flip.injective this
  simp
  dsimp [AspPerm.flip]
  simp

lemma flip_flip : τ.flip.flip = τ := by
  suffices ∀ n, τ.flip.flip n = τ n by
    simp; funext n; exact this n
  intro n
  simp [flip]

lemma flip_s (a b : ℤ) : τ.flip.s a b = τ.s' (-b) (-a) := by
  unfold AspPerm.s AspPerm.s'
  let A := southeast_set τ.flip a b
  let B := northwest_set τ (-a) (-b)
  suffices A.ncard = B.ncard by congr
  have hflip : flip_func τ.flip = τ := by
    funext n
    simp [flip_func, AspPerm.flip]
  have himage : (-1 - ·) '' A = B := by
    dsimp [A, B]
    simpa [hflip] using (flip_quadrant τ.flip a b)
  have himage_card : ((-1 - ·) '' A).ncard = A.ncard :=
    Set.ncard_image_of_injective A (fun x y h => by omega)
  calc
    A.ncard = ((-1 - ·) '' A).ncard := by simpa using himage_card.symm
    _ = B.ncard := by simp [himage]

lemma s_flip (a b : ℤ) : τ.s a b = τ⁻¹.flip.s (-b) (-a) := by
  rw [flip_s, dual_inverse, inv_inv, neg_neg, neg_neg]

lemma b_move_up (a b b' : ℤ) (b_le_b' : b ≤ b') :
  τ.s a b' = τ.s a b - ((Finset.Ico b b').filter (τ · < a)).card := by
  let A := τ.se_finset a b'
  let B := τ.se_finset a b
  let C := (Finset.Ico b b').filter (τ · < a)

  suffices B.card = A.card + C.card by
    unfold A B at this
    have hcard : ((τ.se_finset a b).card : ℤ) = (τ.se_finset a b').card + C.card := by
      exact_mod_cast this
    rw [τ.s_eq_se_card, τ.s_eq_se_card]
    linarith

  have h_disj : Disjoint A C := by
    apply Finset.disjoint_left.mpr
    intro n hA hC
    simp only [A, mem_se] at hA
    simp [C, Finset.mem_filter] at hC
    linarith [hA.1, hC.1]

  have h_union : A ∪ C = B := by
    apply Finset.ext; intro n
    simp [A,B,C, mem_se, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro h
      rcases h with (hA | hC)
      · simp [hA.2]
        exact le_trans b_le_b' hA.1
      · simp [hC.2]
        exact hC.1.1
    · intro hB
      by_cases n_ge_b' : b' ≤ n
      · left; exact ⟨n_ge_b', hB.2⟩
      right
      have : n < b' := by linarith [n_ge_b']
      simp [hB.1, hB.2, this]
  rw [← h_union, Finset.card_union_of_disjoint h_disj]

lemma s_noninc (a : ℤ) {b b' : ℤ} (b_le_b' : b ≤ b') :
  τ.s a b ≥ τ.s a b' ∧ (τ.s a b = τ.s a b' ↔ ∀ x : ℤ, b ≤ x → x < b' → τ x ≥ a) := by
  let S := {x ∈ Finset.Ico b b' | τ x < a}
  have heq : τ.s a b = τ.s a b' + S.card := by
    rw [b_move_up τ a b b' b_le_b']
    simp [S]
  constructor
  · have : S.card ≥ 0 := by simp
    omega
  · have : τ.s a b = τ.s a b' ↔ S.card = 0 := by
      rw [heq]
      constructor <;> (intro; omega)
    rw [this, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    unfold S
    simp

lemma b_step (a b : ℤ) : τ.s a (b+1) = τ.s a b - (if τ b < a then 1 else 0) := by
  have move_up := b_move_up τ a b (b+1) (by omega)
  suffices {x ∈ Finset.Ico b (b + 1) | τ.func x < a}.card = if τ b < a then 1 else 0 by linarith
  by_cases h_lt : τ b < a
  · simp [h_lt]
    suffices {x ∈ Finset.Ico b (b+1) | τ x < a} = {b} by
      rw [this]; simp [Finset.card_singleton]
    ext n
    constructor
    · intro h; simp at h ⊢
      linarith [h.1]
    · intro h; simp at h ⊢
      simp [h, h_lt]
  · have ge_a : τ b ≥ a := by omega
    simp [h_lt]
    intro x x_ge_b x_le_b
    have x_eq_b : x = b := by omega
    rwa [x_eq_b]

lemma b_step_one_iff (a b : ℤ) : τ.s a (b+1) = τ.s a b - 1 ↔ τ b < a := by
  rw [b_step τ a b]
  by_cases h_lt : τ b < a
  · simp [h_lt]
  · simp [h_lt]
    intro h_eq
    omega

lemma b_step_eq_iff (a b : ℤ) : τ.s a (b+1) = τ.s a b ↔ τ b ≥ a := by
  rw [b_step τ a b]
  by_cases h_lt : τ b < a
  · simp [h_lt]
  · simp [h_lt]
    omega

-- Helper: the number of elements of se(a',b) \ se(a,b) equals the number of
-- elements of Ico a a' whose τ-preimage is ≥ b, via the bijection k ↦ τ k.
private lemma se_diff_card (a a' b : ℤ) :
    ((τ.se_finset a' b) \ (τ.se_finset a b)).card =
      ((Finset.Ico a a').filter (τ⁻¹ · ≥ b)).card := by
  apply Finset.card_bij (fun k _ => τ k)
  · intro k hk
    simp only [Finset.mem_sdiff, mem_se] at hk
    obtain ⟨⟨k_ge_b, τk_lt_a'⟩, hk_not⟩ := hk
    have τk_ge_a : a ≤ τ k := by
      by_contra h; push_neg at h
      exact hk_not ⟨k_ge_b, h⟩
    simp only [Finset.mem_filter, Finset.mem_Ico, τ.inv_mul_cancel_eval]
    exact ⟨⟨τk_ge_a, τk_lt_a'⟩, k_ge_b⟩
  · intro k₁ _ k₂ _ h; exact τ.injective h
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_Ico] at hx
    obtain ⟨⟨x_ge_a, x_lt_a'⟩, τinv_ge_b⟩ := hx
    refine ⟨τ⁻¹ x, ?_, τ.mul_inv_cancel_eval x⟩
    simp only [Finset.mem_sdiff, mem_se, τ.mul_inv_cancel_eval]
    exact ⟨⟨τinv_ge_b, x_lt_a'⟩, fun ⟨_, h⟩ => by omega⟩

lemma a_move_up (a a' b : ℤ) (a_le_a' : a ≤ a') :
    τ.s a' b = τ.s a b + ((Finset.Ico a a').filter (τ⁻¹ · ≥ b)).card := by
  have h_sub : τ.se_finset a b ⊆ τ.se_finset a' b := fun k hk => by
    simp only [mem_se] at *; exact ⟨hk.1, lt_of_lt_of_le hk.2 a_le_a'⟩
  suffices (τ.se_finset a' b).card
    = (τ.se_finset a b).card + ((Finset.Ico a a').filter (τ⁻¹ · ≥ b)).card by
    have hcard : ((τ.se_finset a' b).card : ℤ) =
        (τ.se_finset a b).card + ((Finset.Ico a a').filter (τ⁻¹ · ≥ b)).card := by
      exact_mod_cast this
    rw [τ.s_eq_se_card, τ.s_eq_se_card]
    omega
  rw [← se_diff_card τ a a' b]
  have h_disj : Disjoint (τ.se_finset a b) (τ.se_finset a' b \ τ.se_finset a b) :=
    disjoint_sdiff_self_right
  have h_union : τ.se_finset a b ∪ τ.se_finset a' b \ τ.se_finset a b = τ.se_finset a' b :=
    Finset.union_sdiff_of_subset h_sub
  have h_card := Finset.card_union_of_disjoint h_disj
  rw [h_union] at h_card
  omega

lemma s_nondec {a a' : ℤ} (a_le_a' : a ≤ a') (b : ℤ) :
  τ.s a b ≤ τ.s a' b ∧ (τ.s a b = τ.s a' b ↔ ∀ x : ℤ, a ≤ τ x → τ x < a' → x < b ) :=  by
  rw [a_move_up τ a a' b a_le_a']
  let S := {x ∈ Finset.Ico a a' | τ⁻¹ x ≥ b}

  constructor
  · have : S.card ≥ 0 := by simp
    omega

  -- Now handle the equality case
  suffices (∀ (x : ℤ), a ≤ τ.func x → τ.func x < a' → x < b) ↔ S.card = 0 by
    simp only [this]
    constructor <;> (intro; linarith)
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h x xS
    specialize h (τ⁻¹ x)
    simp [S] at xS
    simp [τ.mul_inv_cancel_eval, xS] at h
    omega
  · intro hS x a_le τx_le
    specialize hS (τ x)
    simp [S, a_le, τx_le] at hS
    exact hS


lemma a_step (a b : ℤ) : τ.s (a + 1) b = τ.s a b + (if τ⁻¹ a ≥ b then 1 else 0) := by
  rw [a_move_up τ a (a + 1) b (by omega)]
  by_cases h : τ⁻¹ a ≥ b
  · have hfilt : ((Finset.Ico a (a + 1)).filter (τ⁻¹ · ≥ b)) = {a} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
      constructor
      · intro ⟨⟨hge, hlt⟩, _⟩; omega
      · rintro rfl; exact ⟨⟨le_refl _, by omega⟩, h⟩
    simp [hfilt, if_pos h, Finset.card_singleton]
  · have hfilt : ((Finset.Ico a (a + 1)).filter (τ⁻¹ · ≥ b)) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.notMem_empty, iff_false]
      rintro ⟨⟨hge, hlt⟩, htau⟩
      have hxa : x = a := by omega
      rw [hxa] at htau; exact h htau
    simp [hfilt, if_neg h, Finset.card_empty]

lemma a_step_one_iff (a b : ℤ) : τ.s (a+1) b = τ.s a b + 1 ↔ τ⁻¹ a ≥ b := by
  rw [a_step τ a b]
  by_cases h_ge : τ⁻¹ a ≥ b <;> simp [h_ge]

lemma a_step_one_iff' (u b : ℤ) : τ.s (τ u + 1) b = τ.s (τ u) b + 1 ↔ u ≥ b := by
  have := a_step_one_iff τ (τ u) b
  simpa [τ.mul_inv_cancel_eval] using this

lemma a_step_eq_iff (a b : ℤ) : τ.s (a+1) b = τ.s a b ↔ τ⁻¹ a < b := by
  rw [a_step τ a b]
  by_cases h_ge : τ⁻¹ a ≥ b
  · simp [h_ge]
  · simp [h_ge]
    omega

lemma a_step_eq_iff' (u b : ℤ) : τ.s (τ u + 1) b = τ.s (τ u) b ↔ u < b := by
  have := a_step_eq_iff τ (τ u) b
  simpa [τ.mul_inv_cancel_eval] using this

theorem duality (a b : ℤ) : τ.s a b - (τ⁻¹).s b a = τ.χ + a - b := by
  let h (a b : ℤ) := τ.s a b - (τ⁻¹).s b a - a + b
  have h_zero : h 0 0 = τ.χ := by
    simp [h, AspPerm.χ]
    rw [dual_inverse τ]

  have change_a : ∀ (a a' b : ℤ), h a' b = h a b := by
    intro a a' b
    wlog a_le_a' : a ≤ a' generalizing a a'
    · specialize this a' a (by omega)
      rw [this]
    calc
      h a' b = τ.s a' b - τ⁻¹.s b a' - a' + b := by rfl
      _ = τ.s a b - τ⁻¹.s b a' - a' + b
        + ((Finset.Ico a a').filter (τ⁻¹ · ≥ b)).card := by
        rw [a_move_up τ a a' b a_le_a']
        omega
      _ = τ.s a b - τ⁻¹.s b a - a' + b
        + ((Finset.Ico a a').filter (τ⁻¹ · ≥ b)).card
        + ((Finset.Ico a a').filter (τ⁻¹ · < b)).card := by
        rw [b_move_up (τ⁻¹) b a a' (by omega)]
        omega
      _ = τ.s a b - τ⁻¹.s b a - a' + b
        + (Finset.Ico a a').card := by
        rw [← Utils.card_filter_helper (Finset.Ico a a') (τ⁻¹).func b]
        simp; omega
      _ = τ.s a b - τ⁻¹.s b a - a' + b + (a' - a) := by
        simp [a_le_a']
      _ = h a b := by linarith
  have change_b : ∀ (a b b' : ℤ), h a b' = h a b := by
    intro a b b'
    wlog b_le_b' : b ≤ b' generalizing b b'
    · specialize this b' b (by linarith [b_le_b'])
      rw [this]
    calc
      h a b' = τ.s a b' - τ⁻¹.s b' a - a + b' := by rfl
      _ = τ.s a b - τ⁻¹.s b' a - a + b'
        - ((Finset.Ico b b').filter (τ · < a)).card := by
        rw [b_move_up τ a b b' b_le_b']
        omega
      _ = τ.s a b - τ⁻¹.s b a - a + b'
        - ((Finset.Ico b b').filter (τ · < a)).card
        - ((Finset.Ico b b').filter (τ · ≥ a)).card := by
        rw [a_move_up (τ⁻¹) b b' a (by omega)]
        simp; omega
      _ = τ.s a b - τ⁻¹.s b a - a + b'
        - (Finset.Ico b b').card := by
        rw [← Utils.card_filter_helper (Finset.Ico b b') τ.func a]
        simp; omega
      _ = τ.s a b - τ⁻¹.s b a - a + b' - (b' - b) := by
        simp [b_le_b']
      _ = h a b := by linarith
  have : h a b = h 0 0 := by
    rw [change_a 0 a b, change_b 0 b 0]
  unfold h at this
  linarith

def inset (v : ℤ) : Set ℤ := {u | ⟨u, v⟩ ∈ inv_set τ}

lemma inset_eq_nw (v : ℤ) : τ.inset v = northwest_set τ (τ v) v := by
  ext u
  constructor
  · intro uv_inv
    obtain ⟨u_lt_v, τv_lt_τu⟩ := uv_inv
    exact ⟨u_lt_v, le_of_lt τv_lt_τu⟩
  · intro uv_se
    obtain ⟨u_lt_v, τv_le_τu⟩ := uv_se
    exact (τ.inv_iff_le u_lt_v).mpr τv_le_τu

lemma invset_iff_inset (u v : ℤ) : ⟨u, v⟩ ∈ inv_set τ ↔ u ∈ τ.inset v := by
  simp only [inset_eq_nw, northwest_set, Set.mem_setOf_eq]
  constructor
  · intro ⟨u_lt, τ_le⟩
    exact ⟨u_lt, le_of_lt τ_le⟩
  · intro ⟨x_lt_n, σx_le_σn⟩
    exact (inv_iff_le τ x_lt_n).mpr σx_le_σn

lemma inset_finite (v : ℤ) : (τ.inset v).Finite := by
  rw [τ.inset_eq_nw v]
  apply τ.nw_finite

def outset (u : ℤ) : Set ℤ := {v | ⟨u, v⟩ ∈ inv_set τ}

lemma outset_eq_se (u : ℤ) : τ.outset u = southeast_set τ (τ u) u := by
  ext v
  constructor
  · intro uv_inv
    obtain ⟨u_lt_v, τv_lt_τu⟩ := uv_inv
    exact ⟨le_of_lt u_lt_v, τv_lt_τu⟩
  · intro uv_se
    obtain ⟨u_le_v, τv_lt_τu⟩ := uv_se
    exact (τ.inv_iff_lt u_le_v).mpr τv_lt_τu

lemma invset_iff_outset (u v : ℤ) : ⟨u, v⟩ ∈ inv_set τ ↔ v ∈ τ.outset u := by
  simp only [outset_eq_se, southeast_set, Set.mem_setOf_eq]
  constructor
  · intro ⟨u_lt, τ_le⟩
    exact ⟨le_of_lt u_lt, τ_le⟩
  · intro ⟨x_le_n, σx_lt_σn⟩
    exact (inv_iff_lt τ x_le_n).mpr σx_lt_σn

lemma outset_finite (u : ℤ) : (τ.outset u).Finite := by
  rw [τ.outset_eq_se u]
  apply τ.se_finite

theorem reconstruction : ∀ n : ℤ,
  τ n = n - τ.χ + (τ.outset n).ncard - (τ.inset n).ncard := by
  intro n
  have : τ.s (τ n) n = (τ.outset n).ncard := by
    rw [AspPerm.s, τ.outset_eq_se]
  rw [← this]
  have : τ⁻¹.s n (τ n) = (τ.inset n).ncard := by
    rw [← τ.dual_inverse, AspPerm.s', τ.inset_eq_nw]
  rw [← this]
  have := τ.duality (τ n) n
  omega

/-- If two ASP permutations have the same shift and inversion set, then they are equal. -/
theorem unique_from_inv_and_χ (σ τ : AspPerm) (h_inv : inv_set σ = inv_set τ) (h_χ : σ.χ = τ.χ) :
  σ = τ := by
  apply AspPerm.ext.mpr
  ext n
  rw [reconstruction σ n, reconstruction τ n, h_χ]
  suffices σ.outset n = τ.outset n ∧ σ.inset n = τ.inset n by
    simp [this]
  constructor
  · ext v
    simp only [← invset_iff_outset]
    rw [h_inv]
  · ext v
    simp only [← invset_iff_inset]
    rw [h_inv]

lemma s_eq (a b : ℤ) : τ.s a b = (τ⁻¹).s b a + τ.χ + a - b := by
  have := duality τ a b
  omega

lemma s'_eq (a b : ℤ) : τ⁻¹.s a b = τ.s b a - τ.χ + a - b := by
  have := duality τ b a
  omega

lemma s_ge (a b : ℤ) : τ.s a b ≥ a - b + τ.χ := by
  rw [τ.s_eq a b]
  linarith [τ⁻¹.s_nonneg b a]

lemma s'_ge (a b : ℤ) : τ.s' a b ≥ a - b - τ.χ := by
  rw [dual_inverse τ]
  have := (τ⁻¹).s_ge a b
  rwa [χ_dual] at this

def tend_zero_a (b : ℤ) : ∃ a : ℤ, τ.s a b = 0 := by
  by_cases h : τ.s 0 b = 0
  · use 0
  · let S := Finset.image τ (τ.se_finset 0 b)
    have S_nonempty : S.Nonempty := by
      have h_ne : (southeast_set τ 0 b).ncard ≠ 0 := by
        simpa [AspPerm.s] using h
      have h_nonempty : (southeast_set τ 0 b).Nonempty := Set.nonempty_of_ncard_ne_zero h_ne
      have h_se_nonempty : (τ.se_finset 0 b).Nonempty := by
        rcases h_nonempty with ⟨n, hn⟩
        exact ⟨n, by simpa [se_finset] using hn⟩
      unfold S
      exact Finset.image_nonempty.mpr h_se_nonempty
    let a := Finset.min' S S_nonempty
    have a_lt_0 : a < 0 := by
      have : a ∈ S := Finset.min'_mem S S_nonempty
      simp only [S, Finset.mem_image] at this
      obtain ⟨n, ⟨n_se, n_eq⟩⟩ := this
      have := ((τ.mem_se 0 b n).mp n_se).2
      rwa [n_eq] at this
    use a
    suffices southeast_set τ (Finset.min' S S_nonempty) b = ∅ by
      have h_ncard : (southeast_set τ (Finset.min' S S_nonempty) b).ncard = 0 := by
        exact (Set.ncard_eq_zero
          (s := southeast_set τ (Finset.min' S S_nonempty) b)
          (hs := τ.se_finite (Finset.min' S S_nonempty) b)).2 this
      unfold AspPerm.s
      exact_mod_cast h_ncard
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro n ⟨b_le_n, τn_lt_min⟩
    have : τ n < 0 := lt_trans τn_lt_min a_lt_0
    have : n ∈ τ.se_finset 0 b := (τ.mem_se 0 b n).mpr ⟨b_le_n, this⟩
    have : τ n ∈ S := Finset.mem_image.mpr ⟨n, this, rfl⟩
    have : a ≤ τ n := Finset.min'_le S (τ n) this
    exact lt_irrefl (τ n) <| lt_of_lt_of_le τn_lt_min this

def tend_zero_b (a : ℤ) : ∃ b : ℤ, τ.s a b = 0 := by
  have := tend_zero_a (τ := τ⁻¹.flip) (-a)
  obtain ⟨b, hb⟩ := this
  use -b
  rw [τ⁻¹.flip_s, τ⁻¹.dual_inverse] at hb
  simpa using hb

noncomputable def sf : SlipFace := {
  func := τ.s
  χ := τ.χ
  a_step := by
    intro a b
    rw [τ.a_step a b]
    by_cases h : τ⁻¹ a ≥ b <;> simp [h]
  b_step := by
    intro a b
    rw [τ.b_step a b]
    by_cases h : τ b < a <;> simp [h]
  nonneg := τ.s_nonneg
  ge_diff := τ.s_ge
  small_a := by
    intro b
    obtain ⟨A, hA⟩ := τ.tend_zero_a b
    use A
    intro a a_le_A
    have := (τ.s_nondec a_le_A b).1
    rw [hA] at this
    apply le_antisymm this
    exact τ.s_nonneg a b
  large_a := by
    intro b
    obtain ⟨A, hA⟩ := τ⁻¹.tend_zero_b b
    use A; intro a a_ge_A
    have ha : τ⁻¹.s b a = 0 := by
      apply le_antisymm
      · have := (τ⁻¹.s_noninc b a_ge_A).1
        rwa [hA] at this
      · exact τ⁻¹.s_nonneg b a
    rw [τ.s_eq a b, ha]
    omega
  small_b := by
    intro a
    obtain ⟨B, hB⟩ := τ⁻¹.tend_zero_a a
    use B; intro b b_le_B
    have hb : τ⁻¹.s b a = 0 := by
      apply le_antisymm
      · have := (τ⁻¹.s_nondec b_le_B a).1
        rwa [hB] at this
      · exact τ⁻¹.s_nonneg b a
    rw [τ.s_eq a b, hb]
    omega
  large_b := by
    intro a
    obtain ⟨B, hB⟩ := τ.tend_zero_b a
    use B; intro b b_ge_B
    apply le_antisymm
    · have := (τ.s_noninc a b_ge_B).1
      rwa [hB] at this
    · exact τ.s_nonneg a b
}

@[simp] lemma sf_func_eq_s : τ.sf.func = τ.s := rfl
@[simp] lemma sf_χ_eq : τ.sf.χ = τ.χ := rfl

lemma sf_dual : τ.sf.dual = (τ⁻¹).sf := by
  apply (SF_ext τ.sf.dual τ⁻¹.sf).mpr
  intro a b
  simp
  rw [τ.s'_eq]
  have := τ.sf.duality b a
  simp at this
  omega

lemma Δ_eq (a b : ℤ) : τ.sf.Δ a b = if τ b = a then 1 else 0 := by
  let d1 := τ.s (a+1) b - τ.s (a+1) (b+1)
  let d2 := τ.s a b - τ.s a (b+1)
  suffices d1 - d2 = if τ b = a then 1 else 0 by
    unfold SlipFace.Δ AspPerm.sf
    simp; omega
  have h1 : d1 = if τ b ≤ a then 1 else 0 := by
    unfold d1; rw [τ.b_step (a+1) b]
    omega
  have h2 : d2 = if τ b < a then 1 else 0 := by
    unfold d2; rw [τ.b_step a b]
    omega
  rw [h1, h2]
  by_cases h : τ b < a
  · have h' : τ b ≤ a := le_of_lt h
    have h'' : τ b ≠ a := ne_of_lt h
    simp [h, h', h'']
  simp [h]
  by_cases h' : τ b = a
  · simp [h']
  have h' : ¬ (τ b ≤ a) := by
    contrapose! h'
    push_neg at h
    exact le_antisymm h' h
  simpa [h, h']

lemma Γ_eq : τ.sf.Γ = { ⟨a, b⟩ | τ b = a } := by
  ext ⟨a, b⟩
  simp [SlipFace.Γ, τ.Δ_eq]

lemma submodular : τ.sf.submodular := by
  intro a b
  have Δ_eq := τ.Δ_eq a b
  by_cases h : τ b = a <;> simp [h, Δ_eq]

section RampWings
variable (τ : AspPerm)

def ramp (b : ℤ) : Set (ℤ × ℤ) :=
  {⟨m, n⟩ | ∃ l : ℤ, τ.s l b ≥ m ∧ τ.s' b l ≥ n}

def lamp (a : ℤ) : Set (ℤ × ℤ) :=
  {⟨m, n⟩ | ∃ l : ℤ, τ.s a l ≥ m ∧ τ.s' l a ≥ n}

def ramp_closed (b : ℤ) {m₁ n₁ m₂ n₂ : ℤ} (hm : m₁ ≤ m₂) (hn : n₁ ≤ n₂) :
  ⟨m₂, n₂⟩ ∈ τ.ramp b → ⟨m₁, n₁⟩ ∈ τ.ramp b := by
  intro h
  rcases h with ⟨l, hlm, hln⟩
  use l
  constructor <;> omega


lemma ramp_lamp_dual (b m n : ℤ) :
  ⟨m,n⟩ ∈ τ.ramp b ↔ ⟨n, m⟩ ∈ (τ⁻¹).lamp b := by
  unfold ramp lamp
  rw [← dual_inverse τ, dual_inverse τ⁻¹, inv_inv τ]
  constructor <;> (intro h; rcases h with ⟨l, _, _⟩; use l)

lemma mem_ramp_iff_s_geq (b m n : ℤ) :
  ⟨m, n⟩ ∈ τ.ramp b ↔ τ.s (b + m - n - τ.χ) b ≥ m := by
  constructor
  · intro mn_ramp
    rcases mn_ramp with ⟨l, hm, hn⟩
    by_cases hl : l ≤ b + m - n - τ.χ
    · have := a_move_up τ l (b + m - n - τ.χ) b hl
      omega
    · have ineq := b_move_up τ⁻¹ b (b + m - n - τ.χ) l (by omega)
      rw [dual_inverse τ] at hn
      rw [τ.s_eq (b + m - n - τ.χ) b]
      omega
  · intro s_geq
    use b + m - n - τ.χ
    rw [dual_inverse τ]
    constructor
    · exact s_geq
    · rw [s_eq] at s_geq
      omega

lemma mem_lamp_iff_s_geq (a m n : ℤ) :
  ⟨m, n⟩ ∈ τ.lamp a ↔ τ⁻¹.s (a - m + n + τ.χ) a ≥ n := by
  have := ramp_lamp_dual (τ := τ⁻¹) a n m
  rw [inv_inv] at this
  rw [← this]
  rw [mem_ramp_iff_s_geq, χ_dual]
  constructor <;> (intro h; convert h using 2; omega)

namespace Wings
variable (b m n : ℤ) (m_pos : m > 0) (n_pos : n > 0)

def R : Set ℤ := {n : ℤ | τ.s n b < m}

lemma R_nonempty (m_pos : m > 0) : (R τ b m).Nonempty := by
  have := tend_zero_a (τ := τ) b
  obtain ⟨n, hn⟩ := this
  use n
  unfold R; simp
  linarith [m_pos, hn]

lemma R_bddAbove : ∃ N : ℤ, ∀ n ∈ R τ b m, n ≤ N := by
  use m + b - τ.χ
  intro n hn
  simp [R] at hn
  have := lt_of_le_of_lt (τ.s_ge n b) hn
  omega

def L : Set ℤ := {a : ℤ | τ.s' b a ≥ n}

lemma L_nonnempty : (L τ b n).Nonempty := by
  use b - n - τ.χ
  unfold L; simp
  refine le_trans ?_ (τ.s'_ge b (b - n - τ.χ))
  omega

lemma L_bddAbove (n_pos : n > 0) : ∃ A : ℤ, ∀ a ∈ L τ b n, A ≥ a := by
  have := tend_zero_b (τ := τ⁻¹) b
  obtain ⟨a, ha⟩ := this
  use a
  intro a' a'_L
  unfold L at a'_L; simp at a'_L
  contrapose! a'_L with a_lt_a'
  have := (τ⁻¹.s_noninc b (le_of_lt a_lt_a')).1
  rw [dual_inverse τ]
  omega

end Wings

noncomputable def v (b : ℤ) {m : ℤ} (m_pos : m > 0) : ℤ :=
  τ⁻¹ ( Classical.choose <| Int.exists_greatest_of_bdd
    (Wings.R_bddAbove τ b m) (Wings.R_nonempty τ b m m_pos) )

lemma v_spec (b : ℤ) {m : ℤ} (m_pos : m > 0) :
  τ.s (τ (τ.v b m_pos)) b < m
  ∧ ∀ a : ℤ, τ.s a b < m → a ≤ τ (τ.v b m_pos) := by
  let v := τ.v b m_pos
  let τv := Classical.choose <| Int.exists_greatest_of_bdd
    (Wings.R_bddAbove τ b m) (Wings.R_nonempty τ b m m_pos)
  have τ_vs: τ v = τv := by simp [v, AspPerm.v, τv]
  let R := Wings.R τ b m

  have : τv ∈ R ∧ ∀ n : ℤ, n ∈ R → n ≤ τv := Classical.choose_spec
    (Int.exists_greatest_of_bdd (Wings.R_bddAbove τ b m) (Wings.R_nonempty τ b m m_pos))
  rw [← τ_vs] at this
  simpa [v, R, Wings.R] using this

lemma v_crit (b : ℤ) {m : ℤ} (m_pos : m > 0) (v : ℤ) :
  v = τ.v b m_pos ↔ τ.s (τ v) b = m - 1 ∧ b ≤ v := by
  constructor
  · intro v_eq
    have v_spec : τ.s (τ v) b < m ∧ ∀ a : ℤ, τ.s a b < m → a ≤ τ v := by
      subst v; exact τ.v_spec b m_pos
    obtain ⟨s_lt_m, τv_max⟩ := v_spec
    have s_next : τ.s (τ v + 1) b ≥ m := by
      by_contra! s_next_lt
      have a_le : τ v + 1 ≤ τ v := τv_max (τ v + 1) s_next_lt
      omega
    have s_inc : τ.s (τ v) b < τ.s (τ v + 1) b := lt_of_lt_of_le s_lt_m s_next
    have v_ge_b : b ≤ v := by
      by_contra! v_lt_b
      have : τ.s (τ v + 1) b = τ.s (τ v) b := (a_step_eq_iff' τ v b).mpr v_lt_b
      rw [this] at s_inc
      exact lt_irrefl _ s_inc
    let s_inc : τ.s (τ v + 1) b = τ.s (τ v) b + 1 := (a_step_one_iff' τ v b).mpr v_ge_b
    have s_next_leq : τ.s (τ v + 1) b ≤ m := by
      rw [s_inc]
      apply Int.lt_iff_add_one_le.mpr
      linarith [v_eq]
    have : τ.s (τ v + 1) b = m := le_antisymm s_next_leq s_next
    rw [s_inc] at this
    exact ⟨by linarith [this, s_inc], v_ge_b⟩
  · rintro ⟨s_eq, v_ge_b⟩
    let v₀ := τ.v b m_pos
    have τv_le : τ v ≤ τ v₀ := by
      apply (τ.v_spec b m_pos).2 (τ v)
      linarith [s_eq]
    have τv_ge : τ v₀ ≤ τ v := by
      by_contra! τv_lt
      have τv_le : τ v + 1 ≤ τ (τ.v b m_pos) := by linarith [τv_le]
      have : (τ.s (τ v + 1) b ≤ τ.s (τ v₀) b) := (τ.s_nondec τv_le b).1
      have : (τ.s (τ v) b) + 1 ≤ τ.s (τ v₀) b := by
        rwa [(a_step_one_iff' τ v b).mpr v_ge_b] at this
      linarith [this, s_eq, (τ.v_spec b m_pos).1]
    exact τ.injective <| le_antisymm τv_le τv_ge

lemma s_τv_b (b : ℤ) {m : ℤ} (m_pos : m > 0) :
  τ.s (τ (τ.v b m_pos)) b = m - 1 := by
  exact ((τ.v_crit b m_pos (τ.v b m_pos)).mp rfl).1

lemma v_ge (b : ℤ) {m : ℤ} (m_pos : m > 0) : b ≤ τ.v b m_pos :=
  ((τ.v_crit b m_pos (τ.v b m_pos)).mp rfl).2

lemma τv_lt (b : ℤ) {m : ℤ} (m_pos : m > 0)
  {a : ℤ} (s_ge_m : m ≤ τ.s a b) : τ (τ.v b m_pos) < a := by
  by_contra! τv_ge_a
  have h := (τ.s_nondec τv_ge_a b).1
  have := ((τ.v_crit b m_pos (τ.v b m_pos)).mp rfl).1
  rw [this] at h
  have : m ≤ m-1 := le_trans s_ge_m h
  linarith [this]

noncomputable def u (b : ℤ) {n : ℤ} (n_pos : n > 0) : ℤ :=
  τ⁻¹ <|Classical.choose <| Int.exists_greatest_of_bdd
    (Wings.L_bddAbove τ b n n_pos) (Wings.L_nonnempty τ b n)

lemma u_spec (b : ℤ) {n : ℤ} (n_pos : n > 0) :
  τ.s' b (τ (τ.u b n_pos)) ≥ n
  ∧ ∀ a : ℤ, τ.s' b a ≥ n → a ≤ τ (τ.u b n_pos) := by
  let u := τ.u b n_pos
  let τu := Classical.choose <| Int.exists_greatest_of_bdd
    (Wings.L_bddAbove τ b n n_pos) (Wings.L_nonnempty τ b n)
  have τ_us: τ u = τu := by simp [u, AspPerm.u, τu]
  let L := Wings.L τ b n
  have : τu ∈ L ∧ ∀ n : ℤ, n ∈ L → τu ≥ n := Classical.choose_spec
    (Int.exists_greatest_of_bdd (Wings.L_bddAbove τ b n n_pos) (Wings.L_nonnempty τ b n))
  rw [← τ_us] at this
  simpa [L, Wings.L, dual_inverse τ] using this

lemma u_crit (b : ℤ) {n : ℤ} (n_pos : n > 0) (u : ℤ) :
  u = τ.u b n_pos ↔ τ.s' b (τ u) = n ∧ u < b := by
  constructor
  · intro u_eq
    have u_spec : τ.s' b (τ u) ≥ n ∧ ∀ a : ℤ, τ.s' b a ≥ n → a ≤ τ u := by
      subst u; exact τ.u_spec b n_pos
    obtain ⟨s_ge_n, τu_max⟩ := u_spec
    have s_next : τ.s' b (τ u + 1) < n := by
      by_contra! s_next_ge
      have a_le : τ u + 1 ≤ τ u := τu_max (τ u + 1) s_next_ge
      omega
    have s_ge_n_inv : (τ⁻¹).s b (τ u) ≥ n := by
      simpa [dual_inverse τ] using s_ge_n
    have s_next_inv : (τ⁻¹).s b (τ u + 1) < n := by
      simpa [dual_inverse τ] using s_next
    have u_lt_b : u < b := by
      by_contra! u_ge_b
      have hs_eq : (τ⁻¹).s b (τ u + 1) = (τ⁻¹).s b (τ u) := by
        apply ((τ⁻¹).b_step_eq_iff b (τ u)).2
        simpa using u_ge_b
      rw [hs_eq] at s_next_inv
      exact lt_irrefl _ (lt_of_lt_of_le s_next_inv s_ge_n_inv)
    have hs_dec : (τ⁻¹).s b (τ u + 1) = (τ⁻¹).s b (τ u) - 1 := by
      apply ((τ⁻¹).b_step_one_iff b (τ u)).2
      simpa using u_lt_b
    have hs_eq_n : (τ⁻¹).s b (τ u) = n := by
      rw [hs_dec] at s_next_inv
      omega
    exact ⟨by simpa [dual_inverse τ] using hs_eq_n, u_lt_b⟩
  · rintro ⟨s_eq, u_lt_b⟩
    let u₀ := τ.u b n_pos
    have τu_le : τ u ≤ τ u₀ := by
      apply (τ.u_spec b n_pos).2 (τ u)
      rw [s_eq]
    have τu_ge : τ u₀ ≤ τ u := by
      by_contra! τu_lt
      have τu_succ_le : τ u + 1 ≤ τ u₀ := by omega
      have hs_noninc : (τ⁻¹).s b (τ u₀) ≤ (τ⁻¹).s b (τ u + 1) := by
        exact ((τ⁻¹).s_noninc (a := b) τu_succ_le).1
      have hs_dec : (τ⁻¹).s b (τ u + 1) = (τ⁻¹).s b (τ u) - 1 := by
        apply ((τ⁻¹).b_step_one_iff b (τ u)).2
        simpa using u_lt_b
      have hs_u0_ge_n : (τ⁻¹).s b (τ u₀) ≥ n := by
        simpa [u₀, dual_inverse τ] using (τ.u_spec b n_pos).1
      have hs_u0_le : (τ⁻¹).s b (τ u₀) ≤ n - 1 := by
        rw [hs_dec] at hs_noninc
        have hs_eq_inv : (τ⁻¹).s b (τ u) = n := by
          simpa [dual_inverse τ] using s_eq
        omega
      omega
    exact τ.injective <| le_antisymm τu_le τu_ge

lemma s'_b_τu (b : ℤ) {n : ℤ} (n_pos : n > 0) :
  τ.s' b (τ (τ.u b n_pos)) = n := by
  exact ((τ.u_crit b n_pos (τ.u b n_pos)).mp rfl).1

lemma u_lt (b : ℤ) {n : ℤ} (n_pos : n > 0) : τ.u b n_pos < b :=
  ((τ.u_crit b n_pos (τ.u b n_pos)).mp rfl).2

lemma τu_ge (b : ℤ) {n : ℤ} (n_pos : n > 0)
  {a : ℤ} (s_ge_n : n ≤ τ.s' b a) : τ (τ.u b n_pos) ≥ a := by
  by_contra! τu_lt_a
  have hu_ge : a ≤ τ (τ.u b n_pos) := (τ.u_spec b n_pos).2 a s_ge_n
  omega

theorem inv_ramp_correspondence (b : ℤ) {m n : ℤ} (m_pos : m > 0) (n_pos : n > 0) :
  ⟨m, n⟩ ∈ τ.ramp b ↔ ⟨τ.u b n_pos, τ.v b m_pos⟩ ∈ inv_set τ := by
  let u := τ.u b n_pos
  let v := τ.v b m_pos

  have u_lt_b : u < b := τ.u_lt b n_pos
  have v_gt_b : b ≤ v := τ.v_ge b m_pos

  have inv_simp : ⟨u, v⟩ ∈ inv_set τ ↔ τ v < τ u := by
    simp [inv_set, lt_of_lt_of_le u_lt_b v_gt_b]
  suffices ⟨m, n⟩ ∈ τ.ramp b ↔ τ v < τ u by
    rw [this, inv_simp]
  let a := b + m - n - τ.χ
  constructor
  · intro mn_ramp
    have s_ge_m : τ.s a b ≥ m := (mem_ramp_iff_s_geq (τ := τ) b m n).mp mn_ramp
    have s'_ge_n : τ.s' b a ≥ n := by
      rw [dual_inverse τ]
      have := τ.duality a b
      omega
    have a_gt_v : a > τ v := by
      contrapose! s_ge_m with a_le_v
      have h_lt : τ.s (τ v) b < m := (τ.v_spec b m_pos).1
      have h_le : τ.s a b ≤ τ.s (τ (τ.v b m_pos)) b := (τ.s_nondec a_le_v b).1
      exact lt_of_le_of_lt h_le h_lt
    have a_le_u : a ≤ τ u := by
      exact (τ.u_spec b n_pos).2 a s'_ge_n
    exact lt_of_lt_of_le a_gt_v a_le_u
  · intro τ_v_lt_u
    use τ u
    constructor
    · have u_spec := (τ.v_spec b m_pos).2 (τ u)
      contrapose! τ_v_lt_u with h
      exact u_spec h
    · exact (τ.u_spec b n_pos).1

end RampWings

def le_weak_L (σ τ : AspPerm) : Prop := inv_set σ ⊆ inv_set τ
infix:50 " ≤L " => le_weak_L

def le_weak_R (σ τ : AspPerm) : Prop := inv_set (σ⁻¹).func ⊆ inv_set (τ⁻¹).func
infix:50 " ≤R " => le_weak_R

lemma le_weak_L_of_R {σ τ : AspPerm} (h_R : σ ≤R τ) : σ⁻¹ ≤L τ⁻¹ := h_R

lemma le_weak_R_of_L {σ τ : AspPerm} (h_L : σ ≤L τ) : σ⁻¹ ≤R τ⁻¹ := by
  intro x; simp; intro hx
  exact h_L hx

-- "Slide right" inversions from α to inversions of τ
noncomputable def sr (τ α : AspPerm) : (ℤ × ℤ) → (ℤ × ℤ) := fun x => ⟨ τ⁻¹ (α x.1), τ⁻¹ (α x.2) ⟩

lemma sr_crit (τ α : AspPerm) : ∀ (u v : ℤ),
  ⟨u, v⟩ ∈ (τ.sr α) '' inv_set α ↔ ⟨τ v, τ u⟩ ∈ inv_set α⁻¹.func := by
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

lemma sr_subset (τ α : AspPerm) (h_R : α ≤R τ) : (τ.sr α) '' inv_set α ⊆ inv_set τ := by
  intro x hx; obtain ⟨u, v⟩ := x
  apply (sr_crit τ α u v).mp at hx
  apply h_R at hx
  obtain ⟨τu_gt_τv, u_lt_v⟩ := hx
  simp at u_lt_v
  exact ⟨u_lt_v, τu_gt_τv⟩

-- Proposition mean that (α ⋆ β).s a b ≥ n.
def dprod_val_ge (α β : AspPerm) (a b n : ℤ) : Prop :=
  ∀ l : ℤ, α.s a l + β.s l b ≥ n

def le_dprod (τ α β : AspPerm) : Prop :=
  ∀ a b : ℤ, dprod_val_ge α β a b (τ.s a b)

def dprod_val_le (α β : AspPerm) (a b n : ℤ) : Prop :=
  ∃ l : ℤ, α.s a l + β.s l b ≤ n

def ge_dprod (τ α β : AspPerm) : Prop :=
  ∀ a b : ℤ, dprod_val_le α β a b (τ.s a b)

def eq_dprod (τ α β : AspPerm) : Prop :=
  τ.le_dprod α β ∧ τ.ge_dprod α β

lemma chi_ge_of_dprod_ge {α β τ : AspPerm} (h_ge : τ.le_dprod α β) :
  α.χ + β.χ ≥ τ.χ := by
  rcases α⁻¹.tend_zero_a 0 with ⟨l, hl⟩
  rcases β⁻¹.tend_zero_a l with ⟨c, hc⟩
  have eq := h_ge 0 c l
  rw [α.s_eq, β.s_eq] at eq
  linarith [τ.s_ge 0 c]

lemma chi_le_of_dprod_le {α β τ : AspPerm} (h_le : τ.ge_dprod α β) :
  α.χ + β.χ ≤ τ.χ := by
  rcases τ⁻¹.tend_zero_a 0 with ⟨c, hc⟩
  rcases h_le 0 c with ⟨l, hl⟩
  rw [τ.s_eq] at hl
  linarith [α.s_ge 0 l, β.s_ge l c]

lemma chi_eq_of_drop_eq {τ α β : AspPerm} (h_eq : τ.eq_dprod α β) :
  α.χ + β.χ = τ.χ :=
  Int.le_antisymm (chi_le_of_dprod_le h_eq.2) (chi_ge_of_dprod_ge h_eq.1)

lemma dprod_inv_eq_inv_dprod (τ α β : AspPerm) (h_eq : τ.eq_dprod α β) :
  τ⁻¹.eq_dprod (β⁻¹) (α⁻¹) := by
  have hχ : α.χ + β.χ = τ.χ := chi_eq_of_drop_eq h_eq
  constructor
  · intro a b l
    have eqα : α⁻¹.s l b = l - b + α.s b l - α.χ := by have := α.s'_eq l b; omega
    have eqβ : β⁻¹.s a l = a - l + β.s l a - β.χ := by have := β.s'_eq a l; omega
    have eqτ : τ⁻¹.s a b = a - b + τ.s b a - τ.χ := by have := τ.s'_eq a b; omega
    rw [eqα, eqβ, eqτ, ← hχ]
    have := h_eq.1 b a l
    omega
  · intro a b
    rcases h_eq.2 b a with ⟨l, hl⟩
    use l
    have eqα : α⁻¹.s l b = l - b + α.s b l - α.χ := by have := α.s'_eq l b; omega
    have eqβ : β⁻¹.s a l = a - l + β.s l a - β.χ := by have := β.s'_eq a l; omega
    have eqτ : τ⁻¹.s a b = a - b + τ.s b a - τ.χ := by have := τ.s'_eq a b; omega
    rw [eqα, eqβ, eqτ, ← hχ]
    omega

theorem ramp_dprod_legos (α β : AspPerm) (a b M N : ℤ)
  (habMN : a - b + α.χ + β.χ = M - N) :
  dprod_val_ge α β a b M ↔
  ∀ m ∈ Set.Icc 1 M, ∀ n ∈ Set.Icc 1 N,
  ⟨m, n⟩ ∈ β.ramp b ∨ ⟨M+1-m, N+1-n⟩ ∈ α.lamp a
  := by
  constructor
  · intro dprod m m_icc n n_icc
    let m' := M + 1 - m
    let n' := N + 1 - n
    suffices ⟨m, n⟩ ∈ β.ramp b ∨ ⟨n', m'⟩ ∈ α⁻¹.ramp a by
      have h := ramp_lamp_dual α⁻¹ a (N+1-n) (M+1-m)
      rw [inv_inv] at h
      rw [← h]
      exact this

    have sα := mem_ramp_iff_s_geq α⁻¹ a n' m'
    have sβ := mem_ramp_iff_s_geq β b m n
    rw [sα, sβ]

    unfold dprod_val_ge at dprod
    contrapose! dprod with ineqs

    let l := b + m - n  - β.χ
    use l

    have l_eq : l = a + n' - m' - α⁻¹.χ := by
      simp [n', m', l, α.χ_dual]
      linarith [habMN]
    rw [← l_eq] at ineqs
    obtain ⟨hβ, hα⟩ := ineqs
    have hβ : β.s l b ≤ m-1 := by exact Int.le_sub_one_of_lt hβ
    have hα : α.s a l ≤ M  - m := by
      linarith [α.s_eq a l]
    have : α.s a l + β.s l b ≤ M-1 := by
      linarith [add_le_add (α.s_ge a l) hβ]
    exact Int.lt_of_le_sub_one this
  · unfold dprod_val_ge
    intro hramp l
    contrapose! hramp with ineq
    obtain ineq : α.s a l + β.s l b ≤ M - 1 := Int.le_sub_one_of_lt ineq
    have ineq' : α⁻¹.s l a + β⁻¹.s b l ≤ N -1 := by
      linarith [α.s'_eq l a, β.s'_eq b l]

    let m := β.s l b + 1
    let n := β⁻¹.s b l + 1
    have l_eq : l = m - n + b - β.χ := by
      linarith [β.s_eq l b]

    have m_icc : m ∈ Set.Icc 1 M := by
      constructor
      · linarith [β.s_nonneg l b]
      · linarith [ineq, α.s_nonneg a l]
    have n_icc : n ∈ Set.Icc 1 N := by
      constructor
      · linarith [β⁻¹.s_nonneg b l]
      · linarith [ineq', α⁻¹.s_nonneg l a]

    use m, m_icc, n, n_icc
    constructor
    · show ⟨m, n⟩ ∉ β.ramp b
      intro h_mn
      apply (mem_ramp_iff_s_geq β b m n).mp at h_mn
      have hm : β.s l b ≥ m := by
        convert h_mn using 2
        linarith [l_eq]
      unfold m at hm
      linarith [hm]
    · show ⟨M+1-m, N+1-n⟩ ∉ α.lamp a
      intro h_mn
      have s_geq := (mem_lamp_iff_s_geq α a (M+1-m) (N+1-n)).mp h_mn
      have : (a - (M + 1 - m) + (N + 1 - n) + α.χ) = l := by
        linarith [N, l_eq]
      have : α⁻¹.s l a ≥ N + 1 - n := by
        rwa [this] at s_geq
      linarith [ineq']

end AspPerm
