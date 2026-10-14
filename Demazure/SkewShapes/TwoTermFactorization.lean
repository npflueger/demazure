/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import Demazure.SkewShapes.Basic

/-!
# Weak orders on skew shapes and two-term factorizations

This file defines the left and right weak orders $S' \le_L S$ and $S' \le_R S$ on skew shapes and
shows that they correspond, via $S' \mapsto \sigma_{S'}$, to the left and right weak orders on
shift-$0$ ASP permutations below $\sigma_S$. It then classifies the Demazure factorizations
$\sigma_S = \alpha \star \beta$ into two shift-$0$ factors: they correspond to pairs of shapes
$A \le_R S$ and $B \le_L S$ with $A \cup B = S$ such that no two boxes of $A \cap B$ share a row
or a column.

The first draft of this file was written by Claude Opus 5.5, following a design by
Nathan Pflueger.
-/

@[expose] public section

namespace SkewShapes

open ASP321a

/-- A set $P$ of boxes of $T$ that is closed to the southeast within $T$: whenever $x \le y$
are boxes of $T$ with $x \in P$, also $y \in P$. -/
def lelSet (P : Set (ℤ × ℤ)) (T : SkewShape) : Prop :=
  P ⊆ T.boxes ∧ ∀ x ∈ T, ∀ y ∈ T, x ≤ y → x ∈ P → y ∈ P

/-- A set $P$ of boxes of $T$ that is closed to the northwest within $T$: whenever $x \le y$
are boxes of $T$ with $y \in P$, also $x \in P$. -/
def lerSet (P : Set (ℤ × ℤ)) (T : SkewShape) : Prop :=
  P ⊆ T.boxes ∧ ∀ x ∈ T, ∀ y ∈ T, x ≤ y → y ∈ P → x ∈ P

/-- The left weak order on skew shapes: $S \le_L T$ when $S \subseteq T$ and $S$ is closed
to the southeast within $T$. It corresponds to the left weak order on $\sigma$. -/
def lel (S T : SkewShape) : Prop := lelSet S.boxes T
infix:50 " ≤L " => lel

/-- The right weak order on skew shapes: $S \le_R T$ when $S \subseteq T$ and $S$ is closed
to the northwest within $T$. It corresponds to the right weak order on $\sigma$. -/
def ler (S T : SkewShape) : Prop := lerSet S.boxes T
infix:50 " ≤R " => ler

variable {S S' : SkewShape}

/-- A box of $S' \le_L S$, regarded as a box of $S$. -/
def lel.box (h : S' ≤L S) (x : S') : S := ⟨x, h.1 x.prop⟩

@[simp] lemma lel.box_val (h : S' ≤L S) (x : S') : (h.box x : ℤ × ℤ) = x := rfl

/-- Passing to $S' \le_L S$ does not change $U$. -/
lemma lel.U_eq (h : S' ≤L S) (x : S') : S'.U x = S.U (h.box x) := by
  -- Proof written by Claude Opus 5.5.
  have hxU : (x : ℤ × ℤ) ≤ S.U (h.box x) :=
    Prod.le_def.mpr ⟨S.U_fst (h.box x), (S.U_snd (h.box x)).ge⟩
  refine ((S'.U_spec x _).mpr ⟨S.U_snd (h.box x), ?_, ?_⟩).symm
  · exact h.2 x (h.box x).prop _ (S.U_in_S _) hxU x.prop
  · exact fun h' => S.U_add_not_in_S _ (h.1 h')

/-- Passing to $S' \le_L S$ does not change $V$. -/
lemma lel.V_eq (h : S' ≤L S) (x : S') : S'.V x = S.V (h.box x) := by
  -- Proof written by Claude Opus 5.5.
  have hxV : (x : ℤ × ℤ) ≤ S.V (h.box x) - (0,1) := by
    have := S.V_fst (h.box x)
    have := S.V_snd (h.box x)
    simp only [lel.box_val] at *
    simp only [Prod.le_def, Prod.fst_sub, Prod.snd_sub]
    omega
  refine ((S'.V_spec x _).mpr ⟨S.V_fst (h.box x), ?_, ?_⟩).symm
  · exact h.2 x (h.box x).prop _ (S.V_sub_in_S _) hxV x.prop
  · exact fun h' => S.V_not_in_S _ (h.1 h')

lemma lel.u_eq (h : S' ≤L S) (x : S') : S'.u x = S.u (h.box x) := by
  rw [SkewShape.u, SkewShape.u, h.U_eq]

lemma lel.v_eq (h : S' ≤L S) (x : S') : S'.v x = S.v (h.box x) := by
  rw [SkewShape.v, SkewShape.v, h.V_eq]

/-- A box $x$ of $S$ lies in $S' \le_L S$ exactly when its pair $(u(x), v(x))$ lies in
$I(S')$. -/
lemma lel.mem_iff (h : S' ≤L S) (x : S) : x.val ∈ S' ↔ (S.u x, S.v x) ∈ S'.I := by
  -- Proof written by Claude Opus 5.5.
  rw [SkewShape.mem_I]
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, h.u_eq ⟨x, hx⟩, h.v_eq ⟨x, hx⟩⟩
  · rintro ⟨y, hu, hv⟩
    rw [h.u_eq] at hu
    rw [h.v_eq] at hv
    rw [← S.eq_of_u_eq_of_v_eq hu hv]
    exact y.prop

lemma lel.I_subset (h : S' ≤L S) : S'.I ⊆ S.I := by
  rintro _ ⟨x, rfl⟩
  exact ⟨h.box x, by rw [h.u_eq, h.v_eq]⟩

lemma lel.σ_lel (h : S' ≤L S) : S'.σ ≤L S.σ := by
  intro p hp
  rw [SkewShape.σ_invSet] at hp ⊢
  exact h.I_subset hp

/-- Two shapes below $S$ in left weak order with the same $\sigma$ are equal. -/
lemma lel.eq_of_σ_eq {S'' : SkewShape} (h' : S' ≤L S) (h'' : S'' ≤L S) (hσ : S'.σ = S''.σ) :
    S' = S'' := by
  -- Proof written by Claude Opus 5.5.
  have hI : S'.I = S''.I := by rw [← SkewShape.σ_invSet, hσ, SkewShape.σ_invSet]
  apply SetLike.coe_injective
  ext p
  constructor
  · intro hp
    have := (h'.mem_iff ⟨p, h'.1 hp⟩).mp hp
    rw [hI] at this
    exact (h''.mem_iff ⟨p, h'.1 hp⟩).mpr this
  · intro hp
    have := (h''.mem_iff ⟨p, h''.1 hp⟩).mp hp
    rw [← hI] at this
    exact (h'.mem_iff ⟨p, h''.1 hp⟩).mpr this

lemma restrict_lel {P : S → Prop} {hP : ∀ x y : S, x.val ≤ y.val → P x → P y} :
    S.restrict P hP ≤L S := by
  refine ⟨fun _ ⟨x, _, hx⟩ => hx ▸ x.prop, ?_⟩
  rintro x hx y hy hxy ⟨x', hx', rfl⟩
  exact ⟨⟨y, hy⟩, hP x' ⟨y, hy⟩ hxy hx', rfl⟩

/-- Every shift-$0$ permutation below $\sigma_S$ in left weak order is $\sigma_{S'}$ for some
$S' \le_L S$. -/
lemma exists_lel_of_lel {τ : AspPerm} (hχ : τ.χ = 0) (hle : τ ≤L S.σ) :
    ∃ S' : SkewShape, S' ≤L S ∧ S'.σ = τ := by
  -- Proof written by Claude Opus 5.5.
  set S' := S.restrict (fun x => (S.u x, S.v x) ∈ inv_set τ)
    (fun _ _ hxy hx => S.inv_up_closed hle hxy hx)
  have h : S' ≤L S := restrict_lel
  refine ⟨S', h, AspPerm.eq_of_inv_set_eq_of_chi_eq _ _ ?_ (by rw [SkewShape.σ_shift, hχ])⟩
  rw [SkewShape.σ_invSet]
  ext ⟨a, b⟩
  constructor
  · rintro ⟨x, hx⟩
    rw [← hx, h.u_eq, h.v_eq]
    exact (S.mem_restrict (h.box x)).mp x.prop
  · intro hab
    obtain ⟨x, rfl, rfl⟩ := S.mem_I.mp (S.σ_invSet ▸ hle hab)
    exact (h.mem_iff x).mp ((S.mem_restrict x).mpr hab)

/-- The skew shapes below $S$ in left weak order correspond bijectively, via
$S' \mapsto \sigma_{S'}$, to the shift-$0$ ASP permutations below $\sigma_S$ in left weak
order. -/
noncomputable def lelEquiv (S : SkewShape) :
    {S' : SkewShape // S' ≤L S} ≃ {τ : AspPerm // τ.χ = 0 ∧ τ ≤L S.σ} :=
  Equiv.ofBijective (fun S' => ⟨S'.1.σ, S'.1.σ_shift, S'.2.σ_lel⟩)
    ⟨fun S' S'' h => Subtype.ext (S'.2.eq_of_σ_eq S''.2 (congrArg Subtype.val h)),
      fun τ =>
        let ⟨S', h, hσ⟩ := exists_lel_of_lel τ.2.1 τ.2.2
        ⟨⟨S', h⟩, Subtype.ext hσ⟩⟩

@[simp] lemma lelEquiv_apply (S' : {S' : SkewShape // S' ≤L S}) :
    (lelEquiv S S' : AspPerm) = S'.1.σ := rfl

lemma lelEquiv_symm_σ (h : S' ≤L S) (h' : S'.σ.χ = 0 ∧ S'.σ ≤L S.σ) :
    ((lelEquiv S).symm ⟨S'.σ, h'⟩).1 = S' := by
  have : (lelEquiv S).symm ⟨S'.σ, h'⟩ = ⟨S', h⟩ :=
    (lelEquiv S).symm_apply_eq.mpr (Subtype.ext (lelEquiv_apply ⟨S', h⟩).symm)
  rw [this]

/-! ### The right weak order, by reflection -/

lemma ler.flip_lel (h : S' ≤R S) : S'.flip ≤L S.flip := by
  -- Proof written by Claude Opus 5.5.
  refine ⟨Set.image_mono h.1, fun x hx y hy hxy (hx' : x ∈ S'.flip) => ?_⟩
  change y ∈ S'.flip
  rw [SkewShape.mem_flip] at hx hy hx' ⊢
  exact h.2 _ hy _ hx (flip_le_flip.mpr hxy) hx'

lemma lel.flip_ler (h : S' ≤L S) : S'.flip ≤R S.flip := by
  -- Proof written by Claude Opus 5.5.
  refine ⟨Set.image_mono h.1, fun x hx y hy hxy (hy' : y ∈ S'.flip) => ?_⟩
  change x ∈ S'.flip
  rw [SkewShape.mem_flip] at hx hy hy' ⊢
  exact h.2 _ hy _ hx (flip_le_flip.mpr hxy) hy'

lemma lelSet_self (S : SkewShape) : lelSet S.boxes S := ⟨subset_rfl, fun _ _ _ hy _ _ => hy⟩

lemma lelSet_empty (S : SkewShape) : lelSet ∅ S :=
  ⟨Set.empty_subset _, fun _ _ _ _ _ h => (Set.notMem_empty _ h).elim⟩

lemma lerSet_empty (S : SkewShape) : lerSet ∅ S :=
  ⟨Set.empty_subset _, fun _ _ _ _ _ h => (Set.notMem_empty _ h).elim⟩

lemma lelSet.of_subset {P : Set (ℤ × ℤ)} {T : SkewShape} (h : lelSet P T)
    (hT : S.boxes ⊆ T.boxes) (hP : P ⊆ S.boxes) : lelSet P S :=
  ⟨hP, fun x hx y hy hxy hxP => h.2 x (hT hx) y (hT hy) hxy hxP⟩

lemma lelSet.trans {P : Set (ℤ × ℤ)} (h : lelSet P S') (hS' : S' ≤L S) : lelSet P S :=
  ⟨h.1.trans hS'.1, fun x hx y hy hxy hxP =>
    h.2 x (h.1 hxP) y (hS'.2 x hx y hy hxy (h.1 hxP)) hxy hxP⟩

/-- A set of boxes closed to the southeast within a skew shape is itself a skew shape. -/
def ofLelSet (T : SkewShape) (P : Set (ℤ × ℤ)) (h : lelSet P T) : SkewShape where
  boxes := P
  closed x y z hxy hyz hx hz :=
    h.2 x (h.1 hx) y (T.closed x y z hxy hyz (h.1 hx) (h.1 hz)) hxy hx
  finite_below x hx :=
    have := T.finite_below x (h.1 hx)
    Finite.Set.subset {y ∈ T.boxes | y ≤ x} fun _ hy => ⟨h.1 hy.1, hy.2⟩
  finite_above x hx :=
    have := T.finite_above x (h.1 hx)
    Finite.Set.subset {y ∈ T.boxes | x ≤ y} fun _ hy => ⟨h.1 hy.1, hy.2⟩

lemma ofLelSet_lel {T : SkewShape} {P : Set (ℤ × ℤ)} (h : lelSet P T) : ofLelSet T P h ≤L T :=
  h

lemma ler.σ_ler (h : S' ≤R S) : S'.σ ≤R S.σ := by
  have := h.flip_lel.σ_lel
  rw [SkewShape.flip_σ, SkewShape.flip_σ] at this
  exact this

/-- For $S' \le_L S$, the inversions of $\sigma_{S'}$ are the pairs of the boxes of $S'$. -/
lemma lel.inv_set_σ (h : S' ≤L S) : inv_set S'.σ = S.pair '' {x | x.val ∈ S'} := by
  -- Proof written by Claude Opus 5.5.
  rw [SkewShape.σ_invSet]
  ext p
  constructor
  · intro hp
    obtain ⟨x, rfl⟩ := h.I_subset hp
    exact ⟨x, (h.mem_iff x).mpr hp, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (h.mem_iff x).mp hx

/-- For $S' \le_R S$, the inversions of $\sigma_{S'}$, slid into $\sigma_S$, are the pairs of
the boxes of $S'$. -/
lemma ler.sr_image (h : S' ≤R S) :
    (S.σ.sr S'.σ) '' inv_set S'.σ = S.pair '' {x | x.val ∈ S'} := by
  -- Proof written by Claude Opus 5.5.
  -- Membership of $x$ in $S'$ is detected by the reflection of $S'$.
  have key (x : S) : (S.σ (S.v x), S.σ (S.u x)) ∈ inv_set S'.σ⁻¹.func ↔ x.val ∈ S' := by
    rw [S.σ_of_u, S.σ_of_v, ← S'.flip_σ, SkewShape.σ_invSet, S.u'_eq_flip_u, S.v'_eq_flip_v,
      ← h.flip_lel.mem_iff]
    exact S'.flip_mem_flip
  ext p
  constructor
  · intro hp
    have hpS : p ∈ S.I := S.σ_invSet ▸ AspPerm.sr_subset _ _ h.σ_ler hp
    obtain ⟨x, rfl⟩ := hpS
    exact ⟨x, (key x).mp ((S.σ.sr_crit S'.σ _ _).mp hp), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (S.σ.sr_crit S'.σ _ _).mpr ((key x).mpr hx)

/-- Reflection matches the shapes below $S$ in right weak order with the shapes below the
reflection of $S$ in left weak order. -/
def lerEquivFlip (S : SkewShape) :
    {S' : SkewShape // S' ≤R S} ≃ {S'' : SkewShape // S'' ≤L S.flip} where
  toFun S' := ⟨S'.1.flip, S'.2.flip_lel⟩
  invFun S'' := ⟨S''.1.flip, by have := S''.2.flip_ler; rwa [S.flip_flip] at this⟩
  left_inv S' := Subtype.ext S'.1.flip_flip
  right_inv S'' := Subtype.ext S''.1.flip_flip

/-- The skew shapes below $S$ in right weak order correspond bijectively, via
$S' \mapsto \sigma_{S'}$, to the shift-$0$ ASP permutations below $\sigma_S$ in right weak
order. -/
noncomputable def lerEquiv (S : SkewShape) :
    {S' : SkewShape // S' ≤R S} ≃ {τ : AspPerm // τ.χ = 0 ∧ τ ≤R S.σ} :=
  (lerEquivFlip S).trans <| (lelEquiv S.flip).trans <|
    Equiv.subtypeEquiv (Equiv.inv AspPerm) fun τ => by
      rw [S.flip_σ, Equiv.inv_apply, AspPerm.chi_dual, neg_eq_zero]
      exact and_congr_right' (by rw [show τ⁻¹ ≤R S.σ ↔ τ⁻¹⁻¹ ≤L S.σ⁻¹ from Iff.rfl, inv_inv])

@[simp] lemma lerEquiv_apply (S' : {S' : SkewShape // S' ≤R S}) :
    (lerEquiv S S' : AspPerm) = S'.1.σ := by
  change (S'.1.flip.σ)⁻¹ = S'.1.σ
  rw [SkewShape.flip_σ, inv_inv]

lemma lerEquiv_symm_σ (h : S' ≤R S) (h' : S'.σ.χ = 0 ∧ S'.σ ≤R S.σ) :
    ((lerEquiv S).symm ⟨S'.σ, h'⟩).1 = S' := by
  have : (lerEquiv S).symm ⟨S'.σ, h'⟩ = ⟨S', h⟩ :=
    (lerEquiv S).symm_apply_eq.mpr (Subtype.ext (lerEquiv_apply ⟨S', h⟩).symm)
  rw [this]

/-- Two shapes below $S$ in right weak order with the same $\sigma$ are equal. -/
lemma ler.eq_of_σ_eq {S'' : SkewShape} (h' : S' ≤R S) (h'' : S'' ≤R S) (hσ : S'.σ = S''.σ) :
    S' = S'' := by
  have : lerEquiv S ⟨S', h'⟩ = lerEquiv S ⟨S'', h''⟩ :=
    Subtype.ext (by rw [lerEquiv_apply, lerEquiv_apply, hσ])
  exact congrArg Subtype.val ((lerEquiv S).injective this)

/-
  # Demazure factorizations
  -/

/-- A set of boxes is nonattacking if no two of its boxes share a row or a column. -/
def nonattacking (C : Set (ℤ × ℤ)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, (x.1 = y.1 ∨ x.2 = y.2) → x = y

/-- The pairs of boxes in $A$ and $B$ make up $I(S)$ exactly when $A \cup B = S$. -/
private lemma union_pair_iff {A B : SkewShape} (hA : A.boxes ⊆ S.boxes) (hB : B.boxes ⊆ S.boxes) :
    S.I = S.pair '' {x | x.val ∈ A} ∪ S.pair '' {x | x.val ∈ B} ↔
      A.boxes ∪ B.boxes = S.boxes := by
  -- Proof written by Claude Opus 5.5.
  rw [S.I_eq_range_pair, ← Set.image_union, ← Set.image_univ,
    S.pair_injective.image_injective.eq_iff]
  constructor
  · intro h
    refine Set.Subset.antisymm (Set.union_subset hA hB) fun p hp => ?_
    have : (⟨p, hp⟩ : S) ∈ ({x | x.val ∈ A} ∪ {x | x.val ∈ B} : Set S) := h ▸ Set.mem_univ _
    exact this
  · intro h
    refine (Set.eq_univ_of_forall fun x => ?_).symm
    have : x.val ∈ A.boxes ∪ B.boxes := h ▸ x.prop
    exact this

lemma nonattacking.mono {C D : Set (ℤ × ℤ)} (h : nonattacking C) (hD : D ⊆ C) :
    nonattacking D :=
  fun x hx y hy => h x (hD hx) y (hD hy)

lemma nonattacking_empty : nonattacking ∅ := fun _ h => (Set.notMem_empty _ h).elim

/-- Two boxes in the same row or the same column are comparable. -/
lemma le_or_le_of_row_or_col {x y : ℤ × ℤ} (h : x.1 = y.1 ∨ x.2 = y.2) : x ≤ y ∨ y ≤ x := by
  rcases h with h | h
  · rcases le_total x.2 y.2 with h' | h'
    · exact .inl (Prod.le_def.mpr ⟨h.le, h'⟩)
    · exact .inr (Prod.le_def.mpr ⟨h.ge, h'⟩)
  · rcases le_total x.1 y.1 with h' | h'
    · exact .inl (Prod.le_def.mpr ⟨h', h.le⟩)
    · exact .inr (Prod.le_def.mpr ⟨h', h.ge⟩)

/-- If $P$ is closed to the northwest and $Q$ to the southeast within $S$, and $P \cap Q$ is
nonattacking, then $P \cap Q$ is an antichain. -/
lemma eq_of_le_of_mem_inter {P Q : Set (ℤ × ℤ)} (hP : lerSet P S) (hQ : lelSet Q S)
    (hna : nonattacking (P ∩ Q)) {x y : ℤ × ℤ} (hx : x ∈ P ∩ Q) (hy : y ∈ P ∩ Q)
    (hxy : x ≤ y) : x = y := by
  -- Proof written by Claude Opus 5.5.
  -- The box $z$ in the row of $x$ and the column of $y$ also lies in $P \cap Q$.
  obtain ⟨h1, h2⟩ := Prod.le_def.mp hxy
  set z : ℤ × ℤ := (x.1, y.2)
  have hxz : x ≤ z := Prod.le_def.mpr ⟨le_rfl, h2⟩
  have hzy : z ≤ y := Prod.le_def.mpr ⟨h1, le_rfl⟩
  have hzS : z ∈ S := S.closed x z y hxz hzy (hP.1 hx.1) (hP.1 hy.1)
  have hz : z ∈ P ∩ Q := ⟨hP.2 z hzS y (hP.1 hy.1) hzy hy.1, hQ.2 x (hQ.1 hx.2) z hzS hxz hx.2⟩
  exact (hna z hz x hx (.inl rfl)).symm.trans (hna z hz y hy (.inr rfl))

/-- For $A \le_R S$ and $B \le_L S$, the pairs of boxes common to $A$ and $B$ form an
isolated set exactly when the common boxes are nonattacking. -/
private lemma isolated_pair_iff {A B : SkewShape} (hA : A ≤R S) (hB : B ≤L S) :
    isolated (S.pair '' {x | x.val ∈ A} ∩ S.pair '' {x | x.val ∈ B}) ↔
      nonattacking (A.boxes ∩ B.boxes) := by
  -- Proof written by Claude Opus 5.5.
  rw [← Set.image_inter S.pair_injective]
  constructor
  · intro hiso x hx y hy hxy
    -- Isolatedness says that $A \cap B$ is an antichain.
    have key (a b : ℤ × ℤ) (ha : a ∈ A.boxes ∩ B.boxes) (hb : b ∈ A.boxes ∩ B.boxes)
        (hle : b ≤ a) : a = b :=
      congrArg Subtype.val <| S.pair_injective (a₁ := ⟨a, hA.1 ha.1⟩) (a₂ := ⟨b, hA.1 hb.1⟩)
        (hiso _ ⟨_, ha, rfl⟩ _ ⟨_, hb, rfl⟩ ((S.pair_prec_iff _ _).mpr hle))
    rcases le_or_le_of_row_or_col hxy with h | h
    · exact (key y x hy hx h).symm
    · exact key x y hx hy h
  · rintro hna _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hprec
    rw [S.pair_prec_iff] at hprec
    rw [Subtype.ext (eq_of_le_of_mem_inter hA hB hna hy hx hprec).symm]

/-- For $A \le_R S$ and $B \le_L S$, we have $\sigma_A \star \sigma_B = \sigma_S$ exactly when
$A \cup B = S$ and no two boxes of $A \cap B$ share a row or a column. -/
theorem dprod_iff {A B : SkewShape} (hA : A ≤R S) (hB : B ≤L S) :
    A.σ ⋆ B.σ = S.σ ↔ A.boxes ∪ B.boxes = S.boxes ∧ nonattacking (A.boxes ∩ B.boxes) := by
  -- Proof written by Claude Opus 5.5.
  rw [eq_comm, dprod_eq_iff S.σ_321a, hA.sr_image, hB.inv_set_σ, S.σ_invSet, A.σ_shift,
    B.σ_shift, S.σ_shift, add_zero, eq_self_iff_true, true_and, union_pair_iff hA.1 hB.1,
    isolated_pair_iff hA hB]

/-- A factorization of a skew shape $S$: shapes $A \le_R S$ and $B \le_L S$ with
$A \cup B = S$ and no two boxes of $A \cap B$ in the same row or column. -/
@[ext] structure ShapeFactorization (S : SkewShape) where
  A : SkewShape
  B : SkewShape
  hA : A ≤R S
  hB : B ≤L S
  union_eq : A.boxes ∪ B.boxes = S.boxes
  inter_nonattacking : nonattacking (A.boxes ∩ B.boxes)

/-- Demazure factorizations $\sigma_S = \alpha \star \beta$ into two shift-$0$ factors. -/
abbrev DemazureFactorization (S : SkewShape) : Type :=
  {p : AspPerm × AspPerm // p.1.χ = 0 ∧ p.2.χ = 0 ∧ p.1 ⋆ p.2 = S.σ}

/-- The factorization of $S$ attached to a Demazure factorization of $\sigma_S$: its pieces
are the shapes whose permutations are the two factors. -/
noncomputable def ShapeFactorization.ofDprod (p : DemazureFactorization S) :
    ShapeFactorization S :=
  have hα : p.1.1 ≤R S.σ := by
    have := Submodular.ler_of_dprod p.1.1 p.1.2
    rwa [p.2.2.2] at this
  have hβ : p.1.2 ≤L S.σ := by
    have := Submodular.lel_of_dprod p.1.1 p.1.2
    rwa [p.2.2.2] at this
  let A := (lerEquiv S).symm ⟨p.1.1, p.2.1, hα⟩
  let B := (lelEquiv S).symm ⟨p.1.2, p.2.2.1, hβ⟩
  have hdprod : A.1.σ ⋆ B.1.σ = S.σ := by
    rw [← lerEquiv_apply A, ← lelEquiv_apply B, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact p.2.2.2
  ⟨A.1, B.1, A.2, B.2, ((dprod_iff A.2 B.2).mp hdprod).1, ((dprod_iff A.2 B.2).mp hdprod).2⟩

lemma ShapeFactorization.ofDprod_A_σ (p : DemazureFactorization S) :
    (ofDprod p).A.σ = p.1.1 := by
  change ((lerEquiv S).symm ⟨p.1.1, _⟩).1.σ = p.1.1
  rw [← lerEquiv_apply, Equiv.apply_symm_apply]

lemma ShapeFactorization.ofDprod_B_σ (p : DemazureFactorization S) :
    (ofDprod p).B.σ = p.1.2 := by
  change ((lelEquiv S).symm ⟨p.1.2, _⟩).1.σ = p.1.2
  rw [← lelEquiv_apply, Equiv.apply_symm_apply]

/-- Factorizations of the skew shape $S$ correspond bijectively, via
$(A, B) \mapsto (\sigma_A, \sigma_B)$, to Demazure factorizations of $\sigma_S$ into two
shift-$0$ factors. -/
noncomputable def shapeFactorizationEquiv (S : SkewShape) :
    ShapeFactorization S ≃ DemazureFactorization S where
  toFun F := ⟨(F.A.σ, F.B.σ), F.A.σ_shift, F.B.σ_shift,
    (dprod_iff F.hA F.hB).mpr ⟨F.union_eq, F.inter_nonattacking⟩⟩
  invFun := ShapeFactorization.ofDprod
  left_inv F := by
    ext1
    · exact lerEquiv_symm_σ F.hA _
    · exact lelEquiv_symm_σ F.hB _
  right_inv p := Subtype.ext (Prod.ext (ShapeFactorization.ofDprod_A_σ p)
    (ShapeFactorization.ofDprod_B_σ p))

@[simp] lemma shapeFactorizationEquiv_apply (F : ShapeFactorization S) :
    (shapeFactorizationEquiv S F : AspPerm × AspPerm) = (F.A.σ, F.B.σ) := rfl

end SkewShapes
