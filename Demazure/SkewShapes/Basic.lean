/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import Demazure.Avoiding321
public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.Data.Set.Finite.Lattice


/-!
# Skew shapes and their associated 321-avoiding permutations

IOU more description here.
-/

@[expose] public section

namespace SkewShapes

open ASP321a

/-- The content $j - i$ of the box $(i,j)$. -/
def Δ : ℤ × ℤ → ℤ :=
  fun (i,j) => j - i

lemma Δ_eq (x : ℤ × ℤ) : Δ x = x.2 - x.1 := rfl

/-- Reflection through the line $y = -x$, sending $(i,j)$ to $(-j,-i)$. -/
def flip : ℤ × ℤ → ℤ × ℤ :=
  fun ⟨i,j⟩ => (-j,-i)

@[simp] lemma flip_flip (x : ℤ × ℤ) : flip (flip x) = x := by
  simp only [flip, neg_neg]

lemma flip_involutive : Function.Involutive flip := flip_flip

lemma le_flip {x y : ℤ × ℤ} : x ≤ flip y ↔ y ≤ flip x := by
  simp only [flip, Prod.le_def]
  omega

lemma flip_le {x y : ℤ × ℤ} : flip x ≤ y ↔ flip y ≤ x := by
  simp only [flip, Prod.le_def]
  omega

@[simp] lemma flip_le_flip {x y : ℤ × ℤ} : flip x ≤ flip y ↔ y ≤ x := by
  rw [le_flip, flip_flip]

@[simp] lemma flip_fst (x : ℤ × ℤ) : (flip x).1 = -x.2 := rfl

@[simp] lemma flip_snd (x : ℤ × ℤ) : (flip x).2 = -x.1 := rfl

@[simp] lemma flip_mk (i j : ℤ) : flip (i, j) = (-j, -i) := rfl

lemma flip_add (x y : ℤ × ℤ) : flip (x + y) = flip x + flip y := by
  ext <;> simp only [flip_fst, flip_snd, Prod.fst_add, Prod.snd_add, neg_add]

lemma flip_sub (x y : ℤ × ℤ) : flip (x - y) = flip x - flip y := by
  ext <;> simp only [flip_fst, flip_snd, Prod.fst_sub, Prod.snd_sub] <;> ring

@[simp] lemma Δ_flip (x : ℤ × ℤ) : Δ (flip x) = Δ x := by
  simp only [Δ_eq, flip_fst, flip_snd]
  ring

lemma Δ_add_fst (x : ℤ × ℤ) : Δ (x + (1,0)) = Δ x - 1 := by
  simp only [Δ_eq, Prod.fst_add, Prod.snd_add]
  ring

lemma Δ_add_snd (x : ℤ × ℤ) : Δ (x + (0,1)) = Δ x + 1 := by
  simp only [Δ_eq, Prod.fst_add, Prod.snd_add]
  ring

/-- A skew shape: a convex set of boxes in $\mathbb{Z} \times \mathbb{Z}$, in matrix
coordinates (row $i$ increasing southward, column $j$ increasing eastward), such that each box
has only finitely many boxes weakly northwest and weakly southeast of it. -/
structure SkewShape where
    boxes : Set (ℤ × ℤ)
    closed : ∀ x y z : (ℤ × ℤ), x ≤ y → y ≤ z → x ∈ boxes → z ∈ boxes → y ∈ boxes
    finite_below : ∀ x ∈ boxes, Finite {y ∈ boxes | y ≤ x}
    finite_above : ∀ x ∈ boxes, Finite {y ∈ boxes | x ≤ y}

instance : SetLike SkewShape (ℤ × ℤ) where
    coe := SkewShape.boxes
    coe_injective := by
        intro a b h
        cases a; cases b
        congr

namespace SkewShape

variable (S : SkewShape)

/-- The reflection of $S$ through the line $y = -x$. -/
protected def flip : SkewShape :=
  { boxes := flip '' S.boxes,
    closed := by
      intros x y z hxy hyz hx hz
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨z, hz, rfl⟩ := hz
      use flip y
      constructor
      · exact S.closed z (flip y) x (le_flip.mp hyz) (flip_le.mp hxy) hz hx
      · rw [flip_flip]
    finite_below := by
      rintro  _ ⟨x, hx, rfl⟩
      refine (Set.Finite.image flip (S.finite_above _ hx)).subset ?_
      rintro _ ⟨⟨y, hy, rfl⟩, hle⟩
      exact ⟨_, ⟨hy, flip_le_flip.mp hle⟩, rfl⟩
    finite_above := by
      rintro _ ⟨x, hx, rfl⟩
      refine (Set.Finite.image flip (S.finite_below _ hx)).subset ?_
      rintro _ ⟨⟨y, hy, rfl⟩, hle⟩
      exact ⟨_, ⟨hy, flip_le_flip.mp hle⟩, rfl⟩
}

@[simp] lemma flip_mem_flip {x : ℤ × ℤ} : flip x ∈ S.flip ↔ x ∈ S :=
  flip_involutive.injective.mem_set_image

/-- The box of the flipped shape obtained by reflecting a box of $S$. -/
def flipBox (x : S) : S.flip := ⟨flip x, (S.flip_mem_flip).mpr x.prop⟩

@[simp] lemma flipBox_val (x : S) : (S.flipBox x : ℤ × ℤ) = flip x := rfl

lemma mem_flip {y : ℤ × ℤ} : y ∈ S.flip ↔ flip y ∈ S := by
  rw [← S.flip_mem_flip, flip_flip]

lemma flipBox_bijective : Function.Bijective (S.flipBox) := by
  constructor
  · intro x y hxy
    apply SetLike.coe_eq_coe.mp
    apply flip_involutive.injective
    exact Subtype.ext_iff.mp hxy
  · rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

protected lemma flip_flip : S.flip.flip = S := by
  apply SetLike.coe_injective
  change flip '' (flip '' S.boxes) = S.boxes
  rw [Set.image_image]
  simp only [flip_flip, Set.image_id']

/-- The integers $\Delta(x)$ and $\Delta(x) + 1$ for boxes $x$ of $S$. -/
def support : Set ℤ :=
  Δ '' S.boxes ∪ (fun x => Δ x + 1) '' S.boxes

private lemma above_dec (x : S) (v : ℤ × ℤ) (vpos : 0 < v) :
  {y ∈ S.boxes | x.val + v ≤ y}.ncard
  < {y ∈ S.boxes | x.val ≤ y}.ncard := by
  refine Set.ncard_lt_ncard ?_ (S.finite_above x x.prop)
  constructor
  · intro y hy
    use hy.1
    calc
      x.val ≤ x.val + v := le_add_of_nonneg_right vpos.le
      _ ≤ y := hy.2
  · intro h
    have : x.val + v ≤ x.val := (h ⟨x.prop, le_refl x⟩).2
    have :=
      calc
        x < x + v := (lt_add_iff_pos_right ↑x).mpr vpos
        _ ≤ x := by assumption
    exact (and_not_self_iff (↑x ≤ ↑x)).mp this

open Classical in
/-- The southernmost box in the column of $x$. -/
noncomputable def U (x : S) : ℤ × ℤ :=
  if h : x.val + (1,0) ∈ S
    then U ⟨x.val + (1,0), h⟩
    else x.val
termination_by Set.ncard {y ∈ S.boxes | x.val ≤ y}
decreasing_by
  simp [above_dec S x, Prod.lt_iff]

open Classical in
/-- The first box east of the row of $x$ that is not in $S$. -/
noncomputable def V (x : S) : ℤ × ℤ :=
  if h : x.val + (0,1) ∈ S
    then V ⟨x.val + (0,1), h⟩
    else x.val + (0,1)
termination_by Set.ncard {y ∈ S.boxes | x.val ≤ y}
decreasing_by
  simp [above_dec S x, Prod.lt_iff]

/-- The westernmost box in the row of $x$ (the reflection of $U$). -/
noncomputable def U' (x : S) : ℤ × ℤ :=
  flip (S.flip.U (S.flipBox x))

/-- The first box north of the column of $x$ that is not in $S$ (the reflection of $V$). -/
noncomputable def V' (x : S) : ℤ × ℤ :=
  flip (S.flip.V (S.flipBox x))

noncomputable abbrev u (x : S) : ℤ := Δ (S.U x)
noncomputable abbrev u' (x : S) : ℤ := Δ (S.U' x)
noncomputable abbrev v (x : S) : ℤ := Δ (S.V x)
noncomputable abbrev v' (x : S) : ℤ := Δ (S.V' x)

/-- The pairs $(u(x), v(x))$ for $x \in S$; this is the inversion set of $\sigma$. -/
def I : Set (ℤ × ℤ) := { ⟨S.u x, S.v x⟩ | x : S }

/-- The pairs $(u'(x), v'(x))$ for $x \in S$. -/
def I' : Set (ℤ × ℤ) := { ⟨S.u' x, S.v' x⟩ | x : S }

lemma mem_I {a b : ℤ} : (a, b) ∈ S.I ↔ ∃ x : S, S.u x = a ∧ S.v x = b :=
  exists_congr fun _ => Prod.mk_inj

/-- The pair $(u(x), v(x))$ attached to a box $x$; these pairs make up $I$. -/
noncomputable def pair (x : S) : ℤ × ℤ := (S.u x, S.v x)

lemma I_eq_range_pair : S.I = Set.range S.pair := rfl

lemma U_spec (x : S) : ∀ y : ℤ × ℤ,
  y = S.U x ↔ y.2 = x.val.2 ∧ y ∈ S ∧ y + (1,0) ∉ S := by
    intro y
    rw [U]
    by_cases h : x.val + (1,0) ∈ S
    · rw [dite_eq_left h, U_spec ⟨x.val+(1,0),h⟩]
      simp only [Prod.snd_add, add_zero]
    · rw [dite_eq_right h]
      constructor <;> intro hy
      · rw [hy]
        simp only [SetLike.coe_mem, h, not_false_eq_true, and_self]
      obtain ⟨eq2, yS, yNS⟩ := hy
      rw [Prod.eq_iff_fst_eq_snd_eq]
      refine And.intro ?_ eq2
      apply le_antisymm
      · contrapose! h
        refine S.closed x (x.val + (1,0)) y ?_ ?_ x.prop yS
          <;> (rw [Prod.le_def, Prod.snd_add, Prod.fst_add]; constructor <;> omega)
      · contrapose! yNS
        refine S.closed y (y+(1,0)) x ?_ ?_ yS x.prop
          <;> (rw [Prod.le_def, Prod.snd_add, Prod.fst_add]; constructor <;> omega)
termination_by Set.ncard {y ∈ S.boxes | x.val ≤ y}
decreasing_by
  simp [above_dec S x, Prod.lt_iff]

lemma U_snd (x : S) : (S.U x).2 = x.val.2 := ((S.U_spec x (S.U x)).mp rfl).1
lemma U_in_S (x : S) : S.U x ∈ S := ((S.U_spec x (S.U x)).mp rfl).2.1
lemma U_add_not_in_S (x : S) : S.U x + (1,0) ∉ S := ((S.U_spec x (S.U x)).mp rfl).2.2
lemma U_fst (x : S) : x.val.1 ≤ (S.U x).1 := by
  by_contra! lt1
  apply (S.U_add_not_in_S x)
  refine S.closed (S.U x) (S.U x + (1,0)) x ?_ ?_ (S.U_in_S x) x.prop
  · simp [Prod.le_def]
  · rw [Prod.le_def]
    constructor
    · rw [Prod.fst_add]
      omega
    · rw [Prod.snd_add, U_snd]
      omega


lemma U'_spec (x : S) : ∀ y : ℤ × ℤ,
  y = S.U' x ↔ y.1 = x.val.1 ∧ y ∈ S ∧ y - (0,1) ∉ S := by
    -- Proof written by Claude Opus 5.5.
    intro y
    obtain ⟨y, rfl⟩ := flip_involutive.surjective y
    rw [U', flip_involutive.injective.eq_iff, U_spec]
    simp only [flipBox_val, flip_fst, flip_snd, mem_flip, flip_add, flip_mk, neg_zero,
      sub_eq_add_neg, Prod.neg_mk, neg_eq_iff_eq_neg]

lemma U'_fst (x : S) : (S.U' x).1 = x.val.1 := ((S.U'_spec x (S.U' x)).mp rfl).1
lemma U'_in_S (x : S) : S.U' x ∈ S := ((S.U'_spec x (S.U' x)).mp rfl).2.1
lemma U'_sub_not_in_S (x : S) : S.U' x - (0,1) ∉ S := ((S.U'_spec x (S.U' x)).mp rfl).2.2
lemma U'_snd (x : S) : (S.U' x).2 ≤ x.val.2 := by
  -- Proof written by Claude Opus 5.5.
  by_contra! lt2
  apply (S.U'_sub_not_in_S x)
  refine S.closed x (S.U' x - (0,1)) (S.U' x) ?_ ?_ x.prop (S.U'_in_S x)
  · rw [Prod.le_def]
    constructor
    · rw [Prod.fst_sub, U'_fst]
      omega
    · rw [Prod.snd_sub]
      omega
  · simp [Prod.le_def]

lemma V_spec (x : S) : ∀ y : ℤ × ℤ,
  y = S.V x ↔ y.1 = x.val.1 ∧ y - (0,1) ∈ S ∧ y ∉ S := by
    intro y
    rw [V]
    by_cases h: x.val + (0,1) ∈ S
    · rw [dite_eq_left h, V_spec ⟨x.val + (0,1),h⟩]
      simp only [Prod.fst_add, add_zero]
    · rw [dite_eq_right h]
      constructor <;> intro hy
      · rw [hy]
        simp only [h, add_sub_cancel_right,  not_false_eq_true,
          and_true, x.prop, Prod.fst_add, add_zero]
      obtain ⟨eq1, yS, yNS⟩ := hy
      rw [Prod.eq_iff_fst_eq_snd_eq, Prod.fst_add, eq1]
      apply And.intro (by omega)
      rw [Prod.snd_add]
      apply le_antisymm
      · contrapose! h
        refine S.closed x (x.val+(0,1)) (y - (0,1)) ?_ ?_ x.prop yS
          <;> (rw [Prod.le_def, Prod.snd_add, Prod.fst_add]; constructor)
        · omega
        · omega
        · rw [Prod.fst_sub]
          omega
        · rw [Prod.snd_sub]
          omega
      · contrapose! yNS
        refine S.closed (y - (0,1)) y x ?_ ?_ yS x.prop
          <;> (rw [Prod.le_def]; constructor)
        · rw [Prod.fst_sub]
          omega
        · rw [Prod.snd_sub]
          omega
        · rw [eq1]
        · omega
termination_by Set.ncard {y ∈ S.boxes | x.val ≤ y}
decreasing_by
  simp [above_dec S x, Prod.lt_iff]

lemma V_fst (x : S) : (S.V x).1 = x.val.1 := ((S.V_spec x (S.V x)).mp rfl).1
lemma V_sub_in_S (x : S) : S.V x - (0,1) ∈ S := ((S.V_spec x (S.V x)).mp rfl).2.1
lemma V_not_in_S (x : S) : S.V x ∉ S := ((S.V_spec x (S.V x)).mp rfl).2.2
lemma V_snd (x : S) : x.val.2 < (S.V x).2 := by
  -- Proof written by Claude Opus 5.5.
  by_contra! le2
  apply (S.V_not_in_S x)
  refine S.closed (S.V x - (0,1)) (S.V x) x ?_ ?_ (S.V_sub_in_S x) x.prop
  · simp [Prod.le_def]
  · rw [Prod.le_def]
    exact ⟨(S.V_fst x).le, le2⟩

lemma V'_spec (x : S) : ∀ y : ℤ × ℤ,
  y = S.V' x ↔ y.2 = x.val.2 ∧ y + (1,0) ∈ S ∧ y ∉ S := by
    intro y
    obtain ⟨y', rfl⟩ := flip_involutive.surjective y
    rw [V', flip_involutive.injective.eq_iff, V_spec]
    simp only [flipBox_val, flip_fst, flip_snd, mem_flip, flip_add, flip_mk, neg_zero,
      sub_eq_add_neg, Prod.neg_mk, neg_neg, neg_eq_iff_eq_neg]

lemma V'_snd (x : S) : (S.V' x).2 = x.val.2 := ((S.V'_spec x (S.V' x)).mp rfl).1
lemma V'_add_in_S (x : S) : S.V' x + (1,0) ∈ S := ((S.V'_spec x (S.V' x)).mp rfl).2.1
lemma V'_not_in_S (x : S) : S.V' x ∉ S := ((S.V'_spec x (S.V' x)).mp rfl).2.2
lemma V'_fst (x : S) : (S.V' x).1 < x.val.1 := by
  -- Proof written by Claude Opus 5.5.
  by_contra! le1
  apply (S.V'_not_in_S x)
  refine S.closed x (S.V' x) (S.V' x + (1,0)) ?_ ?_ x.prop (S.V'_add_in_S x)
  · rw [Prod.le_def]
    exact ⟨le1, (S.V'_snd x).ge⟩
  · simp [Prod.le_def]

/-! ### Rows and columns -/

/-- The boxes of $S$ in the row of $x$. -/
def row (x : S) : Set S := {y | y.val.1 = x.val.1}

/-- The boxes of $S$ in the column of $x$. -/
def col (x : S) : Set S := {y | y.val.2 = x.val.2}

@[simp] lemma mem_row {x y : S} : y ∈ S.row x ↔ y.val.1 = x.val.1 := Iff.rfl

@[simp] lemma mem_col {x y : S} : y ∈ S.col x ↔ y.val.2 = x.val.2 := Iff.rfl

/-- Two boxes have the same $U$ exactly when they lie in the same column. -/
lemma U_eq_U_iff (x y : S) : S.U y = S.U x ↔ y.val.2 = x.val.2 := by
  -- Proof written by Claude Opus 5.5.
  constructor
  · intro h
    rw [← S.U_snd x, ← S.U_snd y, h]
  · intro h
    exact ((S.U_spec y (S.U x)).mpr
      ⟨(S.U_snd x).trans h.symm, S.U_in_S x, S.U_add_not_in_S x⟩).symm

/-- Two boxes have the same $V$ exactly when they lie in the same row. -/
lemma V_eq_V_iff (x y : S) : S.V y = S.V x ↔ y.val.1 = x.val.1 := by
  -- Proof written by Claude Opus 5.5.
  constructor
  · intro h
    rw [← S.V_fst x, ← S.V_fst y, h]
  · intro h
    exact ((S.V_spec y (S.V x)).mpr
      ⟨(S.V_fst x).trans h.symm, S.V_sub_in_S x, S.V_not_in_S x⟩).symm

/-- The column of $x$ runs from just south of $V'(x)$ down to $U(x)$. -/
lemma col_mem_iff (x : S) (i : ℤ) : (i, x.val.2) ∈ S ↔ (S.V' x).1 < i ∧ i ≤ (S.U x).1 := by
  -- Proof written by Claude Opus 5.5.
  have := S.U_snd x
  have := S.U_fst x
  have := S.V'_snd x
  have := S.V'_fst x
  constructor
  · intro hi
    constructor
    · by_contra! h
      refine S.V'_not_in_S x (S.closed (i, x.val.2) (S.V' x) x ?_ ?_ hi x.prop) <;>
        simp only [Prod.le_def] <;> omega
    · by_contra! h
      refine S.U_add_not_in_S x (S.closed x (S.U x + (1,0)) (i, x.val.2) ?_ ?_ x.prop hi) <;>
        simp only [Prod.le_def, Prod.fst_add, Prod.snd_add] <;> omega
  · rintro ⟨h1, h2⟩
    refine S.closed (S.V' x + (1,0)) (i, x.val.2) (S.U x) ?_ ?_ (S.V'_add_in_S x)
      (S.U_in_S x) <;> simp only [Prod.le_def, Prod.fst_add, Prod.snd_add] <;> omega

/-- The row of $x$ runs from $U'(x)$ east to just west of $V(x)$. -/
lemma row_mem_iff (x : S) (j : ℤ) : (x.val.1, j) ∈ S ↔ (S.U' x).2 ≤ j ∧ j < (S.V x).2 := by
  -- Proof written by Claude Opus 5.5.
  have := S.U'_fst x
  have := S.U'_snd x
  have := S.V_fst x
  have := S.V_snd x
  constructor
  · intro hj
    constructor
    · by_contra! h
      refine S.U'_sub_not_in_S x
        (S.closed (x.val.1, j) (S.U' x - (0,1)) (S.U' x) ?_ ?_ hj (S.U'_in_S x)) <;>
        simp only [Prod.le_def, Prod.fst_sub, Prod.snd_sub] <;> omega
    · by_contra! h
      refine S.V_not_in_S x (S.closed x (S.V x) (x.val.1, j) ?_ ?_ x.prop hj) <;>
        simp only [Prod.le_def] <;> omega
  · rintro ⟨h1, h2⟩
    refine S.closed (S.U' x) (x.val.1, j) (S.V x - (0,1)) ?_ ?_ (S.U'_in_S x)
      (S.V_sub_in_S x) <;> simp only [Prod.le_def, Prod.fst_sub, Prod.snd_sub] <;> omega

/-- Projecting the column of $x$ to row indices gives the interval $(V'(x)_1, U(x)_1]$. -/
private lemma col_image (x : S) :
    (fun y : S => y.val.1) '' S.col x = Set.Ioc (S.V' x).1 (S.U x).1 := by
  -- Proof written by Claude Opus 5.5.
  ext i
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (S.col_mem_iff x y.val.1).mp (by rw [← S.mem_col.mp hy]; exact y.prop)
  · intro hi
    exact ⟨⟨(i, x.val.2), (S.col_mem_iff x i).mpr hi⟩, rfl, rfl⟩

/-- Projecting the row of $x$ to column indices gives the interval $[U'(x)_2, V(x)_2)$. -/
private lemma row_image (x : S) :
    (fun y : S => y.val.2) '' S.row x = Set.Ico (S.U' x).2 (S.V x).2 := by
  -- Proof written by Claude Opus 5.5.
  ext j
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (S.row_mem_iff x y.val.2).mp (by rw [← S.mem_row.mp hy]; exact y.prop)
  · intro hj
    exact ⟨⟨(x.val.1, j), (S.row_mem_iff x j).mpr hj⟩, rfl, rfl⟩

private lemma fst_injOn_col (x : S) : Set.InjOn (fun y : S => y.val.1) (S.col x) :=
  fun _ hy _ hy' h => Subtype.ext (Prod.ext h (hy.trans hy'.symm))

private lemma snd_injOn_row (x : S) : Set.InjOn (fun y : S => y.val.2) (S.row x) :=
  fun _ hy _ hy' h => Subtype.ext (Prod.ext (hy.trans hy'.symm) h)

lemma col_finite (x : S) : (S.col x).Finite :=
  Set.Finite.of_finite_image (S.col_image x ▸ Set.toFinite _) (S.fst_injOn_col x)

lemma row_finite (x : S) : (S.row x).Finite :=
  Set.Finite.of_finite_image (S.row_image x ▸ Set.toFinite _) (S.snd_injOn_row x)

lemma col_ncard (x : S) : ((S.col x).ncard : ℤ) = (S.U x).1 - (S.V' x).1 := by
  -- Proof written by Claude Opus 5.5.
  rw [← (S.fst_injOn_col x).ncard_image, S.col_image, ← Finset.coe_Ioc,
    Set.ncard_coe_finset, Int.card_Ioc, Int.toNat_of_nonneg]
  linarith [S.V'_fst x, S.U_fst x]

lemma row_ncard (x : S) : ((S.row x).ncard : ℤ) = (S.V x).2 - (S.U' x).2 := by
  -- Proof written by Claude Opus 5.5.
  rw [← (S.snd_injOn_row x).ncard_image, S.row_image, ← Finset.coe_Ico,
    Set.ncard_coe_finset, Int.card_Ico, Int.toNat_of_nonneg]
  linarith [S.U'_snd x, S.V_snd x]

lemma support_convexity (x : S) : ∀ n : ℤ, S.u x ≤ n → n ≤ S.v x → n ∈ S.support := by
  intro n u_le_n n_le_v
  simp only [u, v, Δ_eq] at u_le_n n_le_v
  have := S.U_snd x
  have := S.V_fst x
  by_cases hn : n ≤ Δ x
  · -- Proof of this case written by Claude Opus 5.5.
    -- The box of content $n$ in the column of $x$.
    have := S.V'_fst x
    rw [Δ_eq] at hn
    refine Or.inl ⟨(x.val.2 - n, x.val.2), (S.col_mem_iff x _).mpr ⟨by omega, by omega⟩, ?_⟩
    simp only [Δ_eq]
    omega
  · -- Proof of this case written by Claude Opus 5.5.
    -- The box of content $n - 1$ in the row of $x$.
    have := S.U'_snd x
    rw [Δ_eq] at hn
    refine Or.inr ⟨(x.val.1, x.val.1 + n - 1), (S.row_mem_iff x _).mpr ⟨by omega, by omega⟩, ?_⟩
    simp only [Δ_eq]
    omega

lemma u_le_Δ (x : S) : S.u x ≤ Δ x := by
  simp only [u, Δ_eq]
  linarith [S.U_fst x, S.U_snd x]

lemma Δ_lt_v (x : S) : Δ x < S.v x := by
  simp only [v, Δ_eq]
  linarith [S.V_fst x, S.V_snd x]

/-- The boxes $U(x)$ and $V(x)$ for $x \in S$. -/
noncomputable def fringe : Set (ℤ × ℤ) :=
  Set.range S.U ∪ Set.range S.V

lemma U_fringe (x : S) : S.U x ∈ S.fringe := by left; use x
lemma V_fringe (x : S) : S.V x ∈ S.fringe := by right; use x





noncomputable def fringe' : Set (ℤ × ℤ) :=
  Set.range S.U' ∪ Set.range S.V'

open Classical in
noncomputable def fringe_flip (x : S.fringe) : S.fringe' :=
  if h : x.val ∈ Set.range S.U then
    ⟨S.V' (Classical.choose h), .inr ⟨_, rfl⟩⟩
  else
    have h' : x.val ∈ Set.range S.V := x.prop.resolve_left h
    ⟨S.U' (Classical.choose h'), .inl ⟨_, rfl⟩⟩

def down_closure : Set (ℤ × ℤ) :=
  {x | ∃ y ∈ S, x ≤ y}

def ext_fringe : Set (ℤ × ℤ) :=
  {x | x - (0,1) ∈ S.down_closure ∧ x + (1,0) ∉ S.down_closure}

lemma mem_down_closure_of_le {x y : ℤ × ℤ} (hy : y ∈ S.down_closure) (hxy : x ≤ y) :
    x ∈ S.down_closure :=
  let ⟨z, hz, hyz⟩ := hy
  ⟨z, hz, hxy.trans hyz⟩

lemma mem_down_closure {x : ℤ × ℤ} (hx : x ∈ S) : x ∈ S.down_closure := ⟨x, hx, le_rfl⟩

/-- A box of the extended fringe is determined by its content. -/
lemma ext_fringe_inj {x y : ℤ × ℤ} (hx : x ∈ S.ext_fringe) (hy : y ∈ S.ext_fringe)
    (h : Δ x = Δ y) : x = y := by
  -- Proof written by Claude Opus 5.5.
  -- If $x$ lay strictly northwest of $y$ on the same diagonal, the box south of $x$ would be
  -- northwest of the box west of $y$.
  rw [Δ_eq, Δ_eq] at h
  have key (a b : ℤ × ℤ) (ha : a ∈ S.ext_fringe) (hb : b ∈ S.ext_fringe)
      (hab : b.2 - b.1 = a.2 - a.1) : ¬ a.1 < b.1 := fun hlt =>
    ha.2 (S.mem_down_closure_of_le hb.1
      (Prod.le_def.mpr ⟨by simp only [Prod.fst_add, Prod.fst_sub]; omega,
        by simp only [Prod.snd_add, Prod.snd_sub]; omega⟩))
  rcases lt_trichotomy x.1 y.1 with hlt | heq | hgt
  · exact absurd hlt (key x y hx hy h.symm)
  · exact Prod.ext heq (by omega)
  · exact absurd hgt (key y x hy hx h)

/-- A nonempty skew shape has an extended fringe box of each content. -/
lemma exists_ext_fringe (hS : S.boxes.Nonempty) (n : ℤ) :
    ∃ x ∈ S.ext_fringe, Δ x = n := by
  -- Proof written by Claude Opus 5.5.
  -- Take the southeasternmost box of the down-closure on the diagonal of content $n - 1$; it
  -- exists since the boxes of $S$ southeast of a fixed box are finite in number.
  obtain ⟨s₀, hs₀⟩ := hS
  have hF : {y ∈ S.boxes | s₀ ≤ y}.Finite :=
    have := S.finite_above s₀ hs₀
    Set.toFinite _
  obtain ⟨B, hB⟩ := (hF.image Prod.fst).bddAbove
  obtain ⟨t₀, ht₀, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun t => ((t, t + n - 1) : ℤ × ℤ) ∈ S.down_closure)
    ⟨max (max s₀.1 (s₀.2 - n + 1)) B, fun t ⟨y, hy, hle⟩ => by
      obtain ⟨h1, h2⟩ := Prod.le_def.mp hle
      by_cases hs : s₀.1 ≤ t ∧ s₀.2 ≤ t + n - 1
      · have : y.1 ≤ B := hB ⟨y, ⟨hy, Prod.le_def.mpr ⟨by omega, by omega⟩⟩, rfl⟩
        simp only at h1
        omega
      · omega⟩
    ⟨min s₀.1 (s₀.2 - n + 1), s₀, hs₀, Prod.le_def.mpr ⟨min_le_left _ _, by omega⟩⟩
  refine ⟨(t₀, t₀ + n), ⟨?_, fun h => ?_⟩, by rw [Δ_eq]; ring⟩
  · rw [Prod.mk_sub_mk, sub_zero]
    exact ht₀
  · rw [Prod.mk_add_mk, add_zero] at h
    have := hmax (t₀ + 1) (by rw [show t₀ + 1 + n - 1 = t₀ + n by ring]; exact h)
    omega

/-- The box east of $U(x)$ lies on the extended fringe. -/
lemma U_add_mem_ext_fringe (x : S) : S.U x + (0,1) ∈ S.ext_fringe := by
  refine ⟨by rw [add_sub_cancel_right]; exact S.mem_down_closure (S.U_in_S x), ?_⟩
  rintro ⟨y, hy, hle⟩
  refine S.U_add_not_in_S x (S.closed _ _ y ?_ (le_trans ?_ hle) (S.U_in_S x) hy)
  · simp only [Prod.le_def, Prod.fst_add, Prod.snd_add]
    omega
  · simp only [Prod.le_def, Prod.fst_add, Prod.snd_add]
    omega

/-- The box north of $V(x)$ lies on the extended fringe. -/
lemma V_sub_mem_ext_fringe (x : S) : S.V x - (1,0) ∈ S.ext_fringe := by
  refine ⟨S.mem_down_closure_of_le (S.mem_down_closure (S.V_sub_in_S x)) ?_, ?_⟩
  · simp only [Prod.le_def, Prod.fst_sub, Prod.snd_sub]
    omega
  · rw [sub_add_cancel]
    rintro ⟨y, hy, hle⟩
    refine S.V_not_in_S x (S.closed _ _ y ?_ hle (S.V_sub_in_S x) hy)
    simp only [Prod.le_def, Prod.fst_sub, Prod.snd_sub]
    omega

lemma fringe_crit (x : ℤ × ℤ) :
  x ∈ S.fringe → x ∈ S.ext_fringe := by
  intro h
  obtain hU | hV := h
  · obtain ⟨y, hy⟩ := hU
    let hy := Eq.symm hy
    rw [S.U_spec y] at hy
    obtain ⟨_, xS, xNS⟩ := hy
    constructor
    · use x, xS
      rw [Prod.le_def, Prod.fst_sub, Prod.snd_sub]
      constructor <;> norm_num
    · contrapose! xNS
      obtain ⟨z, zS, hx⟩ := xNS
      refine S.closed x (x+(1,0)) z ?_ hx xS zS
      rw [Prod.le_def, Prod.fst_add, Prod.snd_add]
      constructor <;> norm_num
  · obtain ⟨y, hy⟩ := hV
    let hy := Eq.symm hy
    rw [S.V_spec y] at hy
    obtain ⟨_, xS, xNS⟩ := hy
    constructor
    · use x - (0,1)
    · contrapose! xNS
      obtain ⟨z, zS, zNS⟩ := xNS
      refine S.closed (x-(0,1)) x z ?_ ?_ xS zS
      · rw [Prod.le_def, Prod.fst_sub, Prod.snd_sub]
        constructor <;> norm_num
      · apply le_trans _ zNS
        rw [Prod.le_def, Prod.fst_add, Prod.snd_add]
        constructor <;> norm_num

private lemma fringe_mono {x y : ℤ × ℤ} (hx : x ∈ S.fringe) (hy : y ∈ S.fringe) (hxy : x ≤ y) :
    x.1 = y.1 ∨ x.2 = y.2 := by
  by_contra!
  obtain ⟨ne1, ne2⟩ := this
  obtain ⟨le1, le2⟩ := hxy
  have lt1 : x.1 < y.1 := lt_of_le_of_ne le1 ne1
  have lt2 : x.2 < y.2 := lt_of_le_of_ne le2 ne2
  apply (S.fringe_crit x hx).2
  obtain ⟨⟨z, zS, zNS⟩, _⟩ := S.fringe_crit y hy
  use z, zS
  apply le_trans _ zNS
  rw [Prod.le_def]
  constructor
  · rw [Prod.fst_add, Prod.fst_sub]
    omega
  · rw [Prod.snd_add, Prod.snd_sub]
    omega

private lemma fringe_mono1 {x y : ℤ × ℤ} : x ∈ S.fringe → y ∈ S.fringe → Δ x ≤ Δ y → x.1 ≥ y.1 := by
  intro hx hy h
  by_contra! lt1
  have lt2 : x.2 < y.2 := by
    rw [Δ_eq, Δ_eq] at h
    linarith
  have := S.fringe_mono hx hy (Prod.le_def.mpr ⟨lt1.le, lt2.le⟩)
  omega

private lemma fringe_mono2 {x y : ℤ × ℤ} : x ∈ S.fringe → y ∈ S.fringe → Δ x ≤ Δ y → x.2 ≤ y.2 := by
  intro hx hy h
  by_contra! lt2
  have lt1 : y.1 < x.1 := by
    rw [Δ_eq, Δ_eq] at h
    linarith
  have := S.fringe_mono hy hx (Prod.le_def.mpr ⟨lt1.le, lt2.le⟩)
  omega

/-- A fringe box is determined by its content. -/
lemma fringe_inj {x y : ℤ × ℤ} (hx : x ∈ S.fringe) (hy : y ∈ S.fringe) (h : Δ x = Δ y) :
    x = y := by
  wlog le1 : x.1 ≤ y.1 generalizing x y
  · exact (this hy hx h.symm (le_of_not_ge le1)).symm
  rw [Δ_eq, Δ_eq] at h
  obtain eq1 | eq2 := S.fringe_mono hx hy ⟨le1, by omega⟩
  · exact Prod.ext eq1 (by omega)
  · exact Prod.ext (by omega) eq2

private lemma support_fringe_helper (x : S) :
    (∃ y : S.fringe, Δ y = Δ x) ∧ (∃ z : S.fringe, Δ z = Δ x + 1) := by
  constructor
  · by_cases h : x.val + (1,0) ∈ S
    · obtain ⟨y, hy⟩ := (support_fringe_helper ⟨x.val + (1,0), h⟩).2
      exact ⟨y, by rw [hy, Δ_add_fst, sub_add_cancel]⟩
    · exact ⟨⟨x, .inl ⟨x, by rw [U, dite_eq_right h]⟩⟩, rfl⟩
  · by_cases h : x.val + (0,1) ∈ S
    · obtain ⟨z, hz⟩ := (support_fringe_helper ⟨x.val + (0,1), h⟩).1
      exact ⟨z, hz.trans (Δ_add_snd x)⟩
    · exact ⟨⟨x.val + (0,1), .inr ⟨x, by rw [V, dite_eq_right h]⟩⟩, Δ_add_snd x⟩
termination_by Set.ncard {y ∈ S.boxes | x.val ≤ y}
decreasing_by all_goals simp [above_dec S x, Prod.lt_iff]

lemma support_fringe (n : S.support) : ∃! y : S.fringe, Δ y = n := by
  obtain ⟨y, hy⟩ : ∃ y : S.fringe, Δ y = n := by
    rcases n with ⟨_, ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩⟩
    · exact (S.support_fringe_helper ⟨x, hx⟩).1
    · exact (S.support_fringe_helper ⟨x, hx⟩).2
  use y, hy
  intro y' hy'
  exact Subtype.ext (S.fringe_inj y'.prop y.prop (by rw [hy', hy]))

theorem support_spec : S.support = Set.range S.u ∪ Set.range S.v := by
  ext n
  constructor
  · intro hn
    obtain ⟨y, ⟨hy,_⟩⟩ := S.support_fringe ⟨n, hn⟩
    obtain yU | yV := y.prop
    · left
      obtain ⟨x, hx⟩ := yU
      use x
      change Δ (S.U x) = n
      rw [hx, hy]
    · right
      obtain ⟨x, hx⟩ := yV
      use x
      change Δ (S.V x) = n
      rw [hx, hy]
  · intro hn
    obtain ⟨x,hx⟩ | ⟨x, hx⟩ := hn
    · left
      use S.U x, S.U_in_S x
    · right
      refine ⟨S.V x - (0,1), S.V_sub_in_S x, ?_⟩
      rw [← hx]
      simp only [v, Δ_eq, Prod.fst_sub, Prod.snd_sub]
      omega

lemma uv_disjoint : Set.range S.u ∩ Set.range S.v = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro n ⟨⟨x, rfl⟩, ⟨y, hxy⟩⟩
  apply S.fringe_inj (S.V_fringe y) (S.U_fringe x) at hxy
  apply S.V_not_in_S y
  rw [hxy]
  exact S.U_in_S x

noncomputable def δ (n : S.support) : S.fringe :=  Classical.choose (S.support_fringe n)

@[simp] lemma δ_spec (n : S.support) : Δ (S.δ n) = n :=
  (Classical.choose_spec (S.support_fringe n)).1

lemma δ_unique (n : S.support) (x : S.fringe) : Δ x = n → x = S.δ n := by
  intro h
  rw [← S.δ_spec] at h
  exact Subtype.ext (S.fringe_inj x.prop (S.δ n).prop h)

/-- Two boxes have the same $u$ exactly when they lie in the same column. -/
lemma u_eq_u_iff (x y : S) : S.u y = S.u x ↔ y.val.2 = x.val.2 := by
  -- Proof written by Claude Opus 5.5.
  rw [← U_eq_U_iff]
  exact ⟨S.fringe_inj (S.U_fringe y) (S.U_fringe x), congrArg Δ⟩

/-- Two boxes have the same $v$ exactly when they lie in the same row. -/
lemma v_eq_v_iff (x y : S) : S.v y = S.v x ↔ y.val.1 = x.val.1 := by
  -- Proof written by Claude Opus 5.5.
  rw [← V_eq_V_iff]
  exact ⟨S.fringe_inj (S.V_fringe y) (S.V_fringe x), congrArg Δ⟩

/-- Distinct boxes in the same column have distinct $v$. -/
lemma v_injOn_col (x : S) : Set.InjOn S.v (S.col x) := fun y hy y' hy' h =>
  Subtype.ext (Prod.ext ((S.v_eq_v_iff y' y).mp h) (hy.trans hy'.symm))

/-- Distinct boxes in the same row have distinct $u$. -/
lemma u_injOn_row (x : S) : Set.InjOn S.u (S.row x) := fun y hy y' hy' h =>
  Subtype.ext (Prod.ext (hy.trans hy'.symm) ((S.u_eq_u_iff y' y).mp h))

/-- A box of $S$ is determined by its pair $(u(x), v(x))$. -/
lemma eq_of_u_eq_of_v_eq {x y : S} (hu : S.u x = S.u y) (hv : S.v x = S.v y) : x = y :=
  Subtype.ext (Prod.ext ((S.v_eq_v_iff y x).mp hv) ((S.u_eq_u_iff y x).mp hu))

/-- The function $u$ is weakly increasing from west to east. -/
lemma u_mono {x y : S} (h : x.val.2 ≤ y.val.2) : S.u x ≤ S.u y := by
  -- Proof written by Claude Opus 5.5.
  by_contra! hlt
  have := S.fringe_mono2 (S.U_fringe y) (S.U_fringe x) hlt.le
  rw [S.U_snd, S.U_snd] at this
  exact hlt.ne ((S.u_eq_u_iff x y).mpr (le_antisymm this h))

/-- The function $v$ is weakly decreasing from north to south. -/
lemma v_anti {x y : S} (h : x.val.1 ≤ y.val.1) : S.v y ≤ S.v x := by
  -- Proof written by Claude Opus 5.5.
  by_contra! hlt
  have := S.fringe_mono1 (S.V_fringe x) (S.V_fringe y) hlt.le
  rw [S.V_fst, S.V_fst] at this
  exact hlt.ne ((S.v_eq_v_iff y x).mpr (le_antisymm h this))

lemma pair_injective : Function.Injective S.pair :=
  fun _ _ h => S.eq_of_u_eq_of_v_eq (Prod.mk_inj.mp h).1 (Prod.mk_inj.mp h).2

/-- The function $u$ is strictly increasing from west to east. -/
lemma u_le_u_iff (x y : S) : S.u x ≤ S.u y ↔ x.val.2 ≤ y.val.2 := by
  -- Proof written by Claude Opus 5.5.
  refine ⟨fun h => ?_, S.u_mono⟩
  by_contra! hlt
  exact hlt.ne ((S.u_eq_u_iff x y).mp (le_antisymm (S.u_mono hlt.le) h))

/-- The function $v$ is strictly decreasing from north to south. -/
lemma v_le_v_iff (x y : S) : S.v x ≤ S.v y ↔ y.val.1 ≤ x.val.1 := by
  -- Proof written by Claude Opus 5.5.
  refine ⟨fun h => ?_, S.v_anti⟩
  by_contra! hlt
  exact hlt.ne ((S.v_eq_v_iff y x).mp (le_antisymm h (S.v_anti hlt.le)))

/-- The interval of $x$ lies inside the interval of $y$ exactly when $y$ is weakly northwest
of $x$. -/
lemma pair_prec_iff (x y : S) : S.pair x ≼ S.pair y ↔ y.val ≤ x.val := by
  -- Proof written by Claude Opus 5.5.
  rw [Prod.le_def, and_comm]
  exact and_congr (S.u_le_u_iff y x) (S.v_le_v_iff x y)

/-- The pairs in $I$ starting at $u(x)$ are indexed by the column of $x$. -/
lemma I_out_u (x : S) : {w | (S.u x, w) ∈ S.I} = S.v '' S.col x := by
  -- Proof written by Claude Opus 5.5.
  ext w
  constructor
  · intro hw
    obtain ⟨y, hu, rfl⟩ := S.mem_I.mp hw
    exact ⟨y, (S.u_eq_u_iff x y).mp hu, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact S.mem_I.mpr ⟨y, (S.u_eq_u_iff x y).mpr hy, rfl⟩

/-- The pairs in $I$ ending at $v(x)$ are indexed by the row of $x$. -/
lemma I_in_v (x : S) : {w | (w, S.v x) ∈ S.I} = S.u '' S.row x := by
  -- Proof written by Claude Opus 5.5.
  ext w
  constructor
  · intro hw
    obtain ⟨y, rfl, hv⟩ := S.mem_I.mp hw
    exact ⟨y, (S.v_eq_v_iff x y).mp hv, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact S.mem_I.mpr ⟨y, rfl, (S.v_eq_v_iff x y).mpr hy⟩

/-- No pair in $I$ ends at $u(x)$, since $u(x)$ is not a value of $v$. -/
lemma I_in_u (x : S) : {w | (w, S.u x) ∈ S.I} = ∅ := by
  -- Proof written by Claude Opus 5.5.
  refine Set.eq_empty_iff_forall_notMem.mpr fun w hw => ?_
  obtain ⟨y, -, hy⟩ := S.mem_I.mp hw
  have : S.u x ∈ Set.range S.u ∩ Set.range S.v := ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
  rwa [S.uv_disjoint] at this

/-- No pair in $I$ starts at $v(x)$, since $v(x)$ is not a value of $u$. -/
lemma I_out_v (x : S) : {w | (S.v x, w) ∈ S.I} = ∅ := by
  -- Proof written by Claude Opus 5.5.
  refine Set.eq_empty_iff_forall_notMem.mpr fun w hw => ?_
  obtain ⟨y, hy, -⟩ := S.mem_I.mp hw
  have : S.v x ∈ Set.range S.u ∩ Set.range S.v := ⟨⟨y, hy⟩, ⟨x, rfl⟩⟩
  rwa [S.uv_disjoint] at this

/-- The set $I$ contains no chain $(u,w), (w,v)$. -/
lemma I_tfree : ∀ u w v : ℤ, (u, w) ∉ S.I ∨ (w, v) ∉ S.I := by
  intro u w v
  rw [← not_and_or, mem_I, mem_I]
  rintro ⟨⟨x, -, rfl⟩, ⟨y, hy, -⟩⟩
  have U_eq_V : S.V x = S.U y := S.fringe_inj (S.V_fringe x) (S.U_fringe y) hy.symm
  absurd (S.V_not_in_S x)
  rw [U_eq_V]
  apply S.U_in_S

lemma I_aspset_prop : AspSet_prop S.I := by
  constructor
  · -- directed
    intro u v huv
    obtain ⟨x, ⟨rfl,rfl⟩⟩ := huv
    exact lt_of_le_of_lt (S.u_le_Δ x) (S.Δ_lt_v x)
  · -- closed
    intro u w v huw hwv
    exact (S.I_tfree u w v).elim (absurd huw) (absurd hwv)
  · -- coclosed
    intro u w v u_lt_w w_lt_v huw hwv huv
    obtain ⟨x, ⟨rfl, rfl⟩⟩ := huv
    have hw : w ∈ S.support := S.support_convexity x w u_lt_w.le w_lt_v.le
    obtain ⟨y, ⟨hy,_⟩⟩ := S.support_fringe ⟨w, hw⟩
    obtain hy : Δ y = w := hy
    have x1_le_y1 : x.val.1 ≤ y.val.1 := by
      rw [← S.V_fst x]
      apply S.fringe_mono1 y.prop (S.V_fringe x)
      rw [hy]
      exact w_lt_v.le
    obtain yU | yV := y.prop
    · obtain ⟨y', hy'⟩ := yU
      have yS : y.val ∈ S := hy' ▸ S.U_in_S y'
      set z : ℤ × ℤ := ⟨x.val.1, y.val.2⟩ with hz
      have hxz : x ≤ z := by
        refine Prod.le_def.mpr ⟨le_rfl, ?_⟩
        rw [← S.U_snd x]
        apply S.fringe_mono2 (S.U_fringe x) y.prop
        rw [hy]
        exact u_lt_w.le
      have hzy : z ≤ y := Prod.le_def.mpr ⟨x1_le_y1, le_rfl⟩
      have zS : z ∈ S := S.closed x z y hxz hzy x.prop yS
      -- The box $z$ lies in the row of $x$ and the column of $y$, so $(w, v) \in I$.
      have hUz : S.U ⟨z, zS⟩ = y := by rw [← hy', S.U_eq_U_iff, ← S.U_snd y', hy']
      have hVz : S.V ⟨z, zS⟩ = S.V x := (S.V_eq_V_iff x _).mpr rfl
      exact hwv ⟨⟨z, zS⟩, by simp only [u, v, hUz, hVz, hy]⟩
    · -- Proof of this branch written by Claude Opus 5.5.
      -- Here $z$ lies in the row of $y$ and the column of $x$, so $(u, w) \in I$.
      obtain ⟨y', hy'⟩ := yV
      set z : ℤ × ℤ := ⟨y.val.1, x.val.2⟩
      have zS : z ∈ S := by
        refine S.closed x z (S.U x) (Prod.le_def.mpr ⟨x1_le_y1, le_rfl⟩) ?_ x.prop (S.U_in_S x)
        refine Prod.le_def.mpr ⟨?_, (S.U_snd x).ge⟩
        apply S.fringe_mono1 (S.U_fringe x) y.prop
        rw [hy]
        exact u_lt_w.le
      have hUz : S.U ⟨z, zS⟩ = S.U x := (S.U_eq_U_iff x _).mpr rfl
      have hVz : S.V ⟨z, zS⟩ = y := by rw [← hy', S.V_eq_V_iff, ← S.V_fst y', hy']
      exact huw ⟨⟨z, zS⟩, by simp only [u, v, hUz, hVz, hy]⟩
  · -- finite outdegree
    -- Proof written by Claude Opus 5.5.
    intro u
    rcases Set.eq_empty_or_nonempty {v | (u, v) ∈ S.I} with h | ⟨_, hx₀⟩
    · rw [h]
      exact Set.finite_empty
    obtain ⟨x₀, rfl, -⟩ := S.mem_I.mp hx₀
    rw [S.I_out_u x₀]
    exact (S.col_finite x₀).image _
  · -- finite indegree
    -- Proof written by Claude Opus 5.5.
    intro v
    rcases Set.eq_empty_or_nonempty {u | (u, v) ∈ S.I} with h | ⟨_, hx₀⟩
    · rw [h]
      exact Set.finite_empty
    obtain ⟨x₀, -, rfl⟩ := S.mem_I.mp hx₀
    rw [S.I_in_v x₀]
    exact (S.row_finite x₀).image _

def I_asp : AspSet := ⟨S.I, S.I_aspset_prop⟩


/-
  # The shift-zero permutation associated to a skew shape `S`.
-/


/-- The shift-zero permutation associated to a skew shape `S`. -/
noncomputable def σ : AspPerm := AspSet.toAspPerm S.I_asp 0

lemma σ_321a : is_321a S.σ := by
  rw [ASP321a.is_321a_iff_set_321a_prop]
  constructor
  · exact AspSet.AspSet_InvSet_of_AspPerm S.σ
  · rw [σ, AspSet.invSet_of_toAspPerm]
    exact S.I_tfree
  exact S.σ.bijective

lemma σ_invSet : inv_set S.σ = S.I := by
  rw [σ]
  exact AspSet.invSet_of_toAspPerm S.I_asp 0

lemma σ_shift : S.σ.χ = 0 := by
  rw [σ]
  exact AspSet.chi_of_toAspPerm S.I_asp 0

/-- The reconstruction formula for $\sigma$, which has shift $0$. -/
lemma σ_eq (n : ℤ) :
    S.σ n = n + {v | (n, v) ∈ S.I}.ncard - {u | (u, n) ∈ S.I}.ncard := by
  rw [AspPerm.reconstruction, σ_shift, sub_zero]
  simp only [AspPerm.outset, AspPerm.inset, σ_invSet]

lemma σ_of_u (x : S) : S.σ (S.u x) = S.v' x := by
  -- Proof written by Claude Opus 5.5.
  rw [σ_eq, S.I_out_u, S.I_in_u, Set.ncard_empty, (S.v_injOn_col x).ncard_image, S.col_ncard]
  have := S.U_snd x
  have := S.V'_snd x
  simp only [u, v', Δ_eq]
  omega

lemma σ_of_v (x : S) : S.σ (S.v x) = S.u' x := by
  -- Proof written by Claude Opus 5.5.
  rw [σ_eq, S.I_out_v, S.I_in_v, Set.ncard_empty, (S.u_injOn_row x).ncard_image, S.row_ncard]
  have := S.V_fst x
  have := S.U'_fst x
  simp only [v, u', Δ_eq]
  omega

/-- Integers outside the support of $S$ are fixed by $\sigma$. -/
lemma σ_fixes {n : ℤ} (hn : n ∉ S.support) : S.σ n = n := by
  -- Proof written by Claude Opus 5.5.
  rw [S.support_spec] at hn
  have hout : {w | (n, w) ∈ S.I} = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun w hw => by
    obtain ⟨x, hx, -⟩ := S.mem_I.mp hw
    exact hn (.inl ⟨x, hx⟩)
  have hin : {w | (w, n) ∈ S.I} = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun w hw => by
    obtain ⟨x, -, hx⟩ := S.mem_I.mp hw
    exact hn (.inr ⟨x, hx⟩)
  rw [σ_eq, hout, hin, Set.ncard_empty, Nat.cast_zero, add_zero, sub_zero]

lemma σ_inverse_invset : inv_set S.σ.inv = S.I' := by
  ext ⟨u',v'⟩
  set u := S.σ⁻¹ v' with hu
  set v := S.σ⁻¹ u' with hv
  have hv' : S.σ u = v' := by rw [hu, AspPerm.mul_inv_cancel_eval]
  have hu' : S.σ v = u' := by rw [hv, AspPerm.mul_inv_cancel_eval]
  rw [← hu', ← hv']
  have: S.σ.inv = S.σ⁻¹ := by rfl
  rw [this]
  rw [← AspPerm.inv_set_inverse S.σ u v]
  constructor
  · intro h
    rw [S.σ_invSet] at h
    obtain ⟨x, hx⟩ := h
    obtain ⟨ueq, veq⟩ := Prod.mk_inj.mp hx
    use x
    rw [← ueq, ← veq, Prod.eq_iff_fst_eq_snd_eq, S.σ_of_u, S.σ_of_v]
    constructor <;> rfl
  · intro h
    obtain ⟨x, hx⟩ := h
    obtain ⟨ueq, veq⟩ := Prod.mk_inj.mp hx
    rw [S.σ_invSet]
    use x
    rw [← σ_of_u] at veq
    rw [← σ_of_v] at ueq
    rw [S.σ.injective veq, S.σ.injective ueq]

/-- Reflecting $S$ exchanges $I(S)$ and $I'(S)$. -/
lemma u'_eq_flip_u (x : S) : S.u' x = S.flip.u (S.flipBox x) := by
  simp only [u', u, U', Δ_flip]

lemma v'_eq_flip_v (x : S) : S.v' x = S.flip.v (S.flipBox x) := by
  simp only [v', v, V', Δ_flip]

lemma I'_eq_flip_I : S.I' = S.flip.I := by
  -- Proof written by Claude Opus 5.5.
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨S.flipBox x, by rw [u'_eq_flip_u, v'_eq_flip_v]⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := S.flipBox_bijective.2 y
    exact ⟨x, by rw [u'_eq_flip_u, v'_eq_flip_v]⟩

/-- The permutation of the reflected shape is the inverse permutation. -/
lemma flip_σ : S.flip.σ = S.σ⁻¹ := by
  -- Proof written by Claude Opus 5.5.
  apply AspPerm.eq_of_inv_set_eq_of_chi_eq
  · rw [σ_invSet, ← I'_eq_flip_I, ← σ_inverse_invset]
    rfl
  · rw [σ_shift, AspPerm.chi_dual, σ_shift, neg_zero]

/-- If $\operatorname{Inv}(\tau) \subseteq I(S)$, then the boxes of $S$ whose pairs lie in
$\operatorname{Inv}(\tau)$ are closed to the southeast. -/
lemma inv_up_closed {τ : AspPerm} (hle : τ ≤L S.σ) {x y : S} (hxy : x.val ≤ y.val)
    (hx : (S.u x, S.v x) ∈ inv_set τ) : (S.u y, S.v y) ∈ inv_set τ := by
  -- Proof written by Claude Opus 5.5.
  have hJ : inv_set τ ⊆ S.I := fun p hp => S.σ_invSet ▸ hle hp
  -- No inversion of $\tau$ joins two values of $u$, or two values of $v$.
  have hu : τ (S.u x) ≤ τ (S.u y) := by
    rcases (S.u_mono (Prod.le_def.mp hxy).2).lt_or_eq with hlt | heq
    · by_contra! h
      obtain ⟨z, -, hz⟩ := S.mem_I.mp (hJ ⟨hlt, h⟩)
      have : S.u y ∈ Set.range S.u ∩ Set.range S.v := ⟨⟨y, rfl⟩, ⟨z, hz⟩⟩
      rwa [S.uv_disjoint] at this
    · rw [heq]
  have hv : τ (S.v y) ≤ τ (S.v x) := by
    rcases (S.v_anti (Prod.le_def.mp hxy).1).lt_or_eq with hlt | heq
    · by_contra! h
      obtain ⟨z, hz, -⟩ := S.mem_I.mp (hJ ⟨hlt, h⟩)
      have : S.v y ∈ Set.range S.u ∩ Set.range S.v := ⟨⟨z, hz⟩, ⟨y, rfl⟩⟩
      rwa [S.uv_disjoint] at this
    · rw [heq]
  obtain ⟨-, hτ⟩ := hx
  exact ⟨lt_of_le_of_lt (S.u_le_Δ y) (S.Δ_lt_v y), by omega⟩

/-- The boxes of $S$ satisfying a predicate closed to the southeast form a skew shape. -/
def restrict (P : S → Prop)
    (hP : ∀ x y : S, x.val ≤ y.val → P x → P y) : SkewShape where
  boxes := Subtype.val '' {x | P x}
  closed := by
    rintro x y z hxy hyz ⟨x, hx, rfl⟩ ⟨z, -, rfl⟩
    have hy : y ∈ S := S.closed x y z hxy hyz x.prop z.prop
    exact ⟨⟨y, hy⟩, hP x ⟨y, hy⟩ hxy hx, rfl⟩
  finite_below := by
    rintro _ ⟨x, -, rfl⟩
    have := S.finite_below x x.prop
    exact Finite.Set.subset {y ∈ S.boxes | y ≤ x.val}
      fun _ ⟨⟨y, _, hy⟩, hle⟩ => ⟨hy ▸ y.prop, hle⟩
  finite_above := by
    rintro _ ⟨x, -, rfl⟩
    have := S.finite_above x x.prop
    exact Finite.Set.subset {y ∈ S.boxes | x.val ≤ y}
      fun _ ⟨⟨y, _, hy⟩, hle⟩ => ⟨hy ▸ y.prop, hle⟩

lemma mem_restrict {P : S → Prop} {hP : ∀ x y : S, x.val ≤ y.val → P x → P y}
    (x : S) : x.val ∈ S.restrict P hP ↔ P x := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [← Subtype.ext hyx]
  · exact fun hx => ⟨x, hx, rfl⟩

lemma σ_eq_id_of_boxes_eq_empty (h : S.boxes = ∅) : S.σ = AspPerm.id := by
  refine AspPerm.eq_id_of_inv_set_eq_empty_of_chi_eq_zero S.σ ?_ S.σ_shift
  rw [S.σ_invSet]
  refine Set.eq_empty_of_forall_notMem fun _ ⟨x, _⟩ => ?_
  have : x.val ∈ S.boxes := x.prop
  rw [h] at this
  exact this

lemma boxes_eq_empty_of_σ_eq_id (h : S.σ = AspPerm.id) : S.boxes = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun p hp => ?_
  have : S.pair ⟨p, hp⟩ ∈ inv_set S.σ := S.σ_invSet ▸ ⟨⟨p, hp⟩, rfl⟩
  rw [h, AspPerm.inv_set_id] at this
  exact this

end SkewShape

end SkewShapes
