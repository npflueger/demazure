import Mathlib
import Demazure.Utils

def inv_set (τ : ℤ → ℤ) : Set (ℤ × ℤ) :=
  {(i,j) : ℤ × ℤ | i < j ∧ τ j < τ i}





def southeast_set (τ : ℤ → ℤ) (m n : ℤ) : Set ℤ := { k : ℤ | n ≤ k ∧ τ k < m }

def northwest_set (τ : ℤ → ℤ) (m n : ℤ) : Set ℤ := { k : ℤ | k < n ∧ m ≤ τ k }

lemma se_finite_of_finite {τ : ℤ → ℤ} (h_inj : Function.Injective τ) (m n m' n' : ℤ) :
  (southeast_set τ m n).Finite → (southeast_set τ m' n').Finite := by
  let A := southeast_set τ m n
  let B := southeast_set τ m' n'
  let V := (Finset.Ico n' n).toSet
  let H₀ := (Finset.Ico m m').toSet
  let H := τ⁻¹' H₀

  change A.Finite → B.Finite
  intro fin_A

  have fin_V : V.Finite := by
    apply Finset.finite_toSet

  have fin_H₀ : H₀.Finite := by
    apply Finset.finite_toSet

  have fin_H : H.Finite := by
    refine Set.Finite.preimage ?_ fin_H₀
    exact Set.injOn_of_injective h_inj

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
  let A := northwest_set τ m n
  let B := northwest_set τ m' n'
  let V := (Finset.Ico n n').toSet
  let H₀ := (Finset.Ico m' m).toSet
  let H := τ⁻¹' H₀

  change A.Finite → B.Finite
  intro fin_A

  have fin_V : V.Finite := by
    apply Finset.finite_toSet

  have fin_H₀ : H₀.Finite := by
    apply Finset.finite_toSet

  have fin_H : H.Finite := by
    refine Set.Finite.preimage ?_ fin_H₀
    exact Set.injOn_of_injective h_inj

  have h : B ⊆ A ∪ (H ∪ V) := by
    intro k hk
    simp [A, B] at hk ⊢
    unfold northwest_set at *
    by_cases k_ge_n : k ≥ n
    · right; right
      simp only [V]
      simp [hk.1, k_ge_n]
    obtain k_lt_n : k < n := by
      push_neg at k_ge_n; exact k_ge_n
    by_cases τk_lt_m : τ k < m
    · right; left
      simp only [H, H₀]
      simp [τk_lt_m, hk.2]
    obtain τk_ge_m : τ k ≥ m := by
      push_neg at τk_lt_m; exact τk_lt_m
    left
    exact ⟨k_lt_n, τk_ge_m⟩

  refine Set.Finite.subset ?_ h
  exact Set.Finite.union fin_A (Set.Finite.union fin_H fin_V)

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
      have : k > 0 := by linarith
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
      have : τ k > 0 := by linarith
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

@[simp] lemma eq_iff_eq_func {σ τ : AspPerm} : σ = τ ↔ σ.func = τ.func := by
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
    repeat apply Set.Finite.union
    · exact τ.asp
    · have : {n | τ n * σ (τ n) < 0} = τ ⁻¹' {n | n * σ n < 0} := by ext n; simp

      rw [this]
      exact  Set.Finite.preimage (Set.injOn_of_injective τ.injective) σ.asp
    · have : {n | τ n = 0} = τ ⁻¹' {0} := by ext n; simp
      rw [this]
      exact Set.Finite.preimage (Set.injOn_of_injective τ.injective) (Set.finite_singleton 0)

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

def one : AspPerm where
  func := id
  bijective := ⟨Function.injective_id, Function.surjective_id⟩
  asp := by
    have : {n:ℤ | n * id n < 0} = ∅ := by
      ext n; simp
      exact mul_self_nonneg n
    unfold is_asp; rw [this]
    exact Set.finite_empty

noncomputable instance : Group AspPerm where
  mul := mul
  inv := inv
  one := one
  mul_assoc := by intros a b c; rfl
  one_mul := by intro a; rfl
  mul_one := by intro a; rfl
  inv_mul_cancel := by
    intro τ
    apply (eq_iff_eq_func).2
    funext n
    change Function.invFun τ.func (τ.func n) = n
    exact Function.leftInverse_invFun τ.injective n

@[simp] lemma inv_mul_cancel_eval (n : ℤ) : τ⁻¹ (τ n) = n := by
  change Function.invFun τ.func (τ.func n) = n
  exact Function.leftInverse_invFun τ.injective n

@[simp] lemma mul_inv_cancel_eval (n : ℤ) : τ (τ⁻¹ n) = n := by
  change τ.func (Function.invFun τ.func n) = n
  exact Function.rightInverse_invFun τ.surjective n

noncomputable def se (a b : ℤ) : Finset ℤ := (se_finite_of_asp τ.injective a b τ.asp).toFinset

@[simp] lemma mem_se (a b n : ℤ) : n ∈ (τ.se a b) ↔ n ≥ b ∧ τ n < a := by
  unfold se southeast_set
  simp

noncomputable def nw (a b : ℤ) : Finset ℤ := (nw_finite_of_asp τ.injective a b τ.asp).toFinset

@[simp] lemma mem_nw (a b n : ℤ) : n ∈ (τ.nw a b) ↔ n < b ∧ τ n ≥ a := by
  unfold nw northwest_set
  simp

noncomputable def s (a b : ℤ) : ℤ := (τ.se a b).card
noncomputable def s' (a b : ℤ) : ℤ := (τ.nw b a).card
noncomputable def χ : ℤ := τ.s 0 0 - τ.s' 0 0

lemma dual_inverse : τ.s' = (τ⁻¹).s := by
  funext b a
  calc
    τ.s' b a = (τ.nw a b).card := by rfl
    _ = (Finset.image τ.func (τ.nw a b)).card := by
      have := Finset.card_image_of_injective (τ.nw a b) τ.injective
      rw [this]
    _ = ((τ⁻¹).se b a).card := by
      congr
      ext n
      simp only [Finset.mem_image, mem_nw, mem_se]
      constructor
      · intro h
        rcases h with ⟨m, hm, rfl⟩
        rw [τ.inv_mul_cancel_eval m]
        exact ⟨hm.2, hm.1⟩
      · intro h
        use τ⁻¹ n
        rw [τ.mul_inv_cancel_eval n]
        simp [h]
    _ = (τ⁻¹).s b a := by rfl

abbrev refl : ℤ → ℤ := fun n => -1 - n

abbrev flip_func (f : ℤ → ℤ) : ℤ → ℤ := refl ∘ f ∘ refl

lemma flip_bij (τ : AspPerm) : Function.Bijective (flip_func τ.func) := by
  constructor
  · intro x y h; simp at h
    apply τ.injective at h
    linarith
  · intro y
    use -1 - τ⁻¹ (-1 - y)
    simp [flip_func]

lemma flip_quadrant (f : ℤ → ℤ) (a b : ℤ) :
  (-1 - ·) '' (southeast_set f a b) = northwest_set (flip_func f) (-a) (-b)
  := by
  ext n; unfold southeast_set northwest_set
  constructor
  · intro h
    rcases h with ⟨m, hm, rfl⟩
    simp at hm ⊢
    constructor <;> linarith
  · intro hn
    simp at hn ⊢
    use -1 - n; simp
    constructor <;> linarith

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
      have : Set.InjOn g (southeast_set f 0 0) := by
        intro x _ y _ h; linarith
      apply Set.Finite.of_finite_image h this
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
  let A := τ.flip.se a b
  let B := τ.nw (-a) (-b)
  suffices A.card = B.card by congr
  apply Finset.card_bij (fun n _ => -1 - n)
  · show ∀ n ∈ A, -1 - n ∈ B
    intro n hn
    have : n ≥ b ∧ -1 - τ (-1 - n) < a := by rwa [mem_se] at hn
    rw [mem_nw]
    constructor <;> linarith
  · -- Injectivity
    intro _ _ _ _  _; linarith
  · -- Surjectivity
    intro n hn
    have : -1 - n ∈ A := by
      rw [mem_nw] at hn
      rw [mem_se]
      unfold flip; simp
      constructor <;> linarith
    use (-1 - n),  this
    linarith

lemma s_flip (a b : ℤ) : τ.s a b = τ⁻¹.flip.s (-b) (-a) := by
  rw [flip_s, dual_inverse, inv_inv, neg_neg, neg_neg]

lemma b_move_up (a b b' : ℤ) (b_le_b' : b ≤ b') :
  τ.s a b' = τ.s a b - ((Finset.Ico b b').filter (τ · < a)).card := by
  let A := τ.se a b'
  let B := τ.se a b
  let C := (Finset.Ico b b').filter (τ · < a)

  suffices B.card = A.card + C.card by
    unfold A B at this
    unfold AspPerm.s
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
    linarith
  · have : τ.s a b = τ.s a b' ↔ S.card = 0 := by
      rw [heq]
      constructor <;> (intro; linarith)
    rw [this, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    unfold S
    simp

lemma b_step (a b : ℤ) : τ.s a (b+1) = τ.s a b - (if τ b < a then 1 else 0) := by
  have move_up := b_move_up τ a b (b+1) (by linarith)
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
  · have ge_a : τ b ≥ a := by linarith
    simp [h_lt]
    intro x x_ge_b x_le_b
    have x_eq_b : x = b := by linarith
    rwa [x_eq_b]

lemma b_step_one_iff (a b : ℤ) : τ.s a (b+1) = τ.s a b - 1 ↔ τ b < a := by
  rw [b_step τ a b]
  by_cases h_lt : τ b < a
  · simp [h_lt]
  · simp [h_lt]
    intro h_eq
    linarith

lemma b_step_eq_iff (a b : ℤ) : τ.s a (b+1) = τ.s a b ↔ τ b ≥ a := by
  rw [b_step τ a b]
  by_cases h_lt : τ b < a
  · simp [h_lt]
  · simp [h_lt]
    linarith

lemma a_move_up (a a' b : ℤ) (a_le_a' : a ≤ a') :
  -- Deduce from b_move_up using the flipped inverse
  τ.s a' b = τ.s a b + ((Finset.Ico a a').filter (τ⁻¹ · ≥ b)).card := by
  let A := {x ∈ Finset.Ico (-a') (-a) | τ⁻¹.flip.func x < -b}
  let B := ((Finset.Ico a a').filter (τ⁻¹ · ≥ b))
  suffices A.card = B.card by
    have : ∀ x y : ℤ, τ.s x y = τ⁻¹.flip.s (-y) (-x) := by simp [flip_s, dual_inverse]
    rw [this a' b, this a b]
    have := (τ⁻¹.flip).b_move_up (-b) (-a') (-a) (by linarith)
    linarith
  have h (n : ℤ): n ∈ A ↔ -1-n ∈ B := by
    simp only [A, B, Finset.mem_filter, Finset.mem_Ico, flip]
    constructor <;>
      (intro hn; obtain ⟨⟨h1,h2⟩,h3⟩ := hn; repeat constructor; repeat linarith)
  apply Finset.card_bij (fun n _ => -1 - n)
  · intro a; exact (h a).mp
  · intro _ _ _ _ _; linarith
  · intro n hn
    have : -1-n ∈ A := by
      apply (h (-1-n)).mpr
      simp [hn]
    use -1-n, this
    linarith

lemma s_nondec {a a' : ℤ} (a_le_a' : a ≤ a') (b : ℤ) :
  τ.s a b ≤ τ.s a' b ∧ (τ.s a b = τ.s a' b ↔ ∀ x : ℤ, a ≤ τ x → τ x < a' → x < b ) :=  by
  rw [a_move_up τ a a' b a_le_a']
  let S := {x ∈ Finset.Ico a a' | τ⁻¹ x ≥ b}

  constructor
  · have : S.card ≥ 0 := by simp
    linarith

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
    linarith
  · intro hS x a_le τx_le
    specialize hS (τ x)
    simp [S, a_le, τx_le] at hS
    exact hS


lemma a_step (a b : ℤ) : τ.s (a + 1) b = τ.s a b + (if τ⁻¹ a ≥ b then 1 else 0) := by
  calc
    τ.s (a+1) b = τ⁻¹.flip.s (-b) (-(a+1)) := by rw [τ.s_flip (a+1) b]
    _ = τ⁻¹.flip.s (-b) (-(a+1)+1) + if τ⁻¹.flip.func (-(a + 1)) < -b then 1 else 0 := by
      linarith [(τ⁻¹.flip).b_step (-b) (-(a+1)) ]
    _ = τ⁻¹.flip.s (-b) (-a) + if -1 - τ⁻¹.func a < -b then 1 else 0 := by
      unfold flip; simp
    _ = τ⁻¹.flip.s (-b) (-a) + if b ≤ τ⁻¹.func a then 1 else 0 := by
      have : -1 - τ⁻¹.func a < -b ↔ b ≤ τ⁻¹.func a := by
        constructor <;> (intro h; linarith)
      simp [this]
    _ = τ.s a b + (if τ⁻¹ a ≥ b then 1 else 0) := by rw[τ.s_flip a b]

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
    linarith

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
    · specialize this a' a (by linarith)
      rw [this]
    calc
      h a' b = τ.s a' b - τ⁻¹.s b a' - a' + b := by rfl
      _ = τ.s a b - τ⁻¹.s b a' - a' + b
        + ((Finset.Ico a a').filter (τ⁻¹ · ≥ b)).card := by
        rw [a_move_up τ a a' b a_le_a']
        linarith
      _ = τ.s a b - τ⁻¹.s b a - a' + b
        + ((Finset.Ico a a').filter (τ⁻¹ · ≥ b)).card
        + ((Finset.Ico a a').filter (τ⁻¹ · < b)).card := by
        rw [b_move_up (τ⁻¹) b a a' (by linarith)]
        linarith
      _ = τ.s a b - τ⁻¹.s b a - a' + b
        + (Finset.Ico a a').card := by
        rw [← Utils.card_filter_helper (Finset.Ico a a') (τ⁻¹).func b]
        simp; linarith
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
        linarith
      _ = τ.s a b - τ⁻¹.s b a - a + b'
        - ((Finset.Ico b b').filter (τ · < a)).card
        - ((Finset.Ico b b').filter (τ · ≥ a)).card := by
        rw [a_move_up (τ⁻¹) b b' a (by linarith)]
        simp; linarith
      _ = τ.s a b - τ⁻¹.s b a - a + b'
        - (Finset.Ico b b').card := by
        rw [← Utils.card_filter_helper (Finset.Ico b b') τ.func a]
        simp; linarith
      _ = τ.s a b - τ⁻¹.s b a - a + b' - (b' - b) := by
        simp [b_le_b']
      _ = h a b := by linarith
  have : h a b = h 0 0 := by
    rw [change_a 0 a b, change_b 0 b 0]
  unfold h at this
  linarith

def ramp (τ : AspPerm) (b : ℤ) : Set (ℤ × ℤ) :=
  {⟨m, n⟩ | ∃ l : ℤ, τ.s l b ≥ m ∧ τ.s' b l ≥ n}

def lamp (τ : AspPerm) (a : ℤ) : Set (ℤ × ℤ) :=
  {⟨m, n⟩ | ∃ l : ℤ, τ.s a l ≥ m ∧ τ.s' l a ≥ n}

lemma ramp_lamp_dual (τ : AspPerm) (b m n : ℤ) :
  ⟨m,n⟩ ∈ τ.ramp b ↔ ⟨n, m⟩ ∈ (τ⁻¹).lamp b := by
  unfold ramp lamp
  rw [← dual_inverse τ, dual_inverse τ⁻¹, inv_inv τ]
  constructor <;> (intro h; rcases h with ⟨l, _, _⟩; use l)

lemma mem_ramp_iff_s_geq (τ : AspPerm) (b m n : ℤ) :
  ⟨m, n⟩ ∈ τ.ramp b ↔ τ.s (b + m - n - τ.χ) b ≥ m := by
  constructor
  · intro mn_ramp
    rcases mn_ramp with ⟨l, hm, hn⟩
    by_cases hl : l ≤ b + m - n - τ.χ
    · have := a_move_up τ l (b + m - n - τ.χ) b hl
      linarith
    · have ineq := b_move_up τ⁻¹ b (b + m - n - τ.χ) l (by linarith)
      rw [dual_inverse τ] at hn
      linarith [τ.duality (b + m - n - τ.χ) b, τ.duality l b]
  · intro s_geq
    use b + m - n - τ.χ
    rw [dual_inverse τ]
    constructor
    · exact s_geq
    · linarith [τ.duality (b + m - n - τ.χ) b]


def le_weak_L (σ τ : AspPerm) : Prop := inv_set σ ⊆ inv_set τ
infix:50 " ≤L " => le_weak_L

def le_weak_R (σ τ : AspPerm) : Prop := inv_set (σ⁻¹).func ⊆ inv_set (τ⁻¹).func
infix:50 " ≤R " => le_weak_R

-- Proposition mean that (α ⋆ β).s a b ≥ n.
def dprod_geq (α β : AspPerm) (a b n : ℤ) : Prop :=
  ∀ l : ℤ, α.s a l + β.s l b ≥ n

def dprod_leq (α β : AspPerm) (a b n : ℤ) : Prop :=
  ∃ l : ℤ, α.s a l + β.s l b ≤ n



end AspPerm
