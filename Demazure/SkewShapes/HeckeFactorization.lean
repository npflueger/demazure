/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import Demazure.SkewShapes.TwoTermFactorization

/-!
# Hecke factorizations and shape chains

This file classifies the Hecke factorizations $\sigma_S = \alpha_1 \star \dots \star \alpha_n$
into shift-$0$ factors. They correspond, via $(A_1, \dots, A_n) \mapsto
(\sigma_{A_1}, \dots, \sigma_{A_n})$, to shape chains: lists of skew shapes covering $S$ such
that each prefix union is closed to the northwest within $S$, each suffix union is closed to the
southeast, and each prefix union meets the matching suffix union in a nonattacking set.

The first draft of this file was written by Claude Opus 5.5, following a design by
Nathan Pflueger.
-/

@[expose] public section

namespace SkewShapes

open ASP321a

variable {S : SkewShape}

/-- The boxes lying in some shape of a list. -/
def boxUnion : List SkewShape → Set (ℤ × ℤ)
  | [] => ∅
  | A :: L => A.boxes ∪ boxUnion L

@[simp] lemma boxUnion_nil : boxUnion [] = ∅ := rfl

@[simp] lemma boxUnion_cons (A : SkewShape) (L : List SkewShape) :
    boxUnion (A :: L) = A.boxes ∪ boxUnion L := rfl

lemma boxUnion_append (L₁ L₂ : List SkewShape) :
    boxUnion (L₁ ++ L₂) = boxUnion L₁ ∪ boxUnion L₂ := by
  induction L₁ with
  | nil => rw [List.nil_append, boxUnion_nil, Set.empty_union]
  | cons A L ih => rw [List.cons_append, boxUnion_cons, boxUnion_cons, ih, Set.union_assoc]

lemma boxUnion_take_union_drop (L : List SkewShape) (k : ℕ) :
    boxUnion (L.take k) ∪ boxUnion (L.drop k) = boxUnion L := by
  rw [← boxUnion_append, List.take_append_drop]

lemma boxUnion_take_subset (L : List SkewShape) (k : ℕ) : boxUnion (L.take k) ⊆ boxUnion L := by
  rw [← boxUnion_take_union_drop L k]
  exact Set.subset_union_left

lemma boxUnion_drop_subset (L : List SkewShape) (k : ℕ) : boxUnion (L.drop k) ⊆ boxUnion L := by
  rw [← boxUnion_take_union_drop L k]
  exact Set.subset_union_right

/-- A list of skew shapes $A_1, \dots, A_n$ is a shape chain for $S$ if the $A_i$ cover $S$
and, for each $k$, the prefix union $P_k = A_1 \cup \dots \cup A_k$ is closed to the northwest
within $S$, the suffix union $Q_k = A_{k+1} \cup \dots \cup A_n$ is closed to the southeast
within $S$, and $P_k \cap Q_k$ is nonattacking. -/
structure IsShapeChain (S : SkewShape) (L : List SkewShape) : Prop where
  union_eq : boxUnion L = S.boxes
  take_ler : ∀ k, lerSet (boxUnion (L.take k)) S
  drop_lel : ∀ k, lelSet (boxUnion (L.drop k)) S
  inter_nonattacking : ∀ k, nonattacking (boxUnion (L.take k) ∩ boxUnion (L.drop k))

namespace IsShapeChain

variable {A : SkewShape} {L : List SkewShape}

lemma nil (h : S.boxes = ∅) : IsShapeChain S [] where
  union_eq := h.symm
  take_ler _ := by
    rw [List.take_nil, boxUnion_nil]
    exact lerSet_empty S
  drop_lel _ := by
    rw [List.drop_nil, boxUnion_nil]
    exact lelSet_empty S
  inter_nonattacking _ := by
    rw [List.take_nil, boxUnion_nil, Set.empty_inter]
    exact nonattacking_empty

lemma head_ler (h : IsShapeChain S (A :: L)) : A ≤R S := by
  have := h.take_ler 1
  rwa [show (A :: L).take 1 = [A] from rfl, boxUnion_cons, boxUnion_nil, Set.union_empty] at this

lemma tail_lelSet (h : IsShapeChain S (A :: L)) : lelSet (boxUnion L) S := h.drop_lel 1

lemma head_union (h : IsShapeChain S (A :: L)) : A.boxes ∪ boxUnion L = S.boxes := h.union_eq

lemma head_nonattacking (h : IsShapeChain S (A :: L)) :
    nonattacking (A.boxes ∩ boxUnion L) := by
  have := h.inter_nonattacking 1
  rwa [show (A :: L).take 1 = [A] from rfl, show (A :: L).drop 1 = L from rfl, boxUnion_cons,
    boxUnion_nil, Set.union_empty] at this

/-- The tail of a shape chain is a shape chain for the union of its shapes. -/
lemma tail (h : IsShapeChain S (A :: L)) :
    IsShapeChain (ofLelSet S (boxUnion L) h.tail_lelSet) L where
  -- Proof written by Claude Opus 5.5.
  union_eq := rfl
  take_ler k := by
    have hP : lerSet (A.boxes ∪ boxUnion (L.take k)) S := h.take_ler (k + 1)
    have hQ : lelSet (boxUnion (L.drop k)) S := h.drop_lel (k + 1)
    have hna : nonattacking ((A.boxes ∪ boxUnion (L.take k)) ∩ boxUnion (L.drop k)) :=
      h.inter_nonattacking (k + 1)
    refine ⟨boxUnion_take_subset L k, fun x hx y hy hxy hyP => ?_⟩
    have hxS : x ∈ S := h.tail_lelSet.1 hx
    have hyS : y ∈ S := h.tail_lelSet.1 hy
    rcases hP.2 x hxS y hyS hxy (.inr hyP) with hxA | hxP
    · -- If $x \in A$ but $x \notin P_k$, then $x \le y$ both lie in $P_{k+1} \cap Q_{k+1}$.
      by_contra hxP
      have hxQ : x ∈ boxUnion (L.drop k) := by
        have : x ∈ boxUnion (L.take k) ∪ boxUnion (L.drop k) :=
          (boxUnion_take_union_drop L k).symm ▸ hx
        exact this.resolve_left hxP
      have hyQ : y ∈ boxUnion (L.drop k) := hQ.2 x hxS y hyS hxy hxQ
      have hxy' := eq_of_le_of_mem_inter hP hQ hna ⟨.inl hxA, hxQ⟩ ⟨.inr hyP, hyQ⟩ hxy
      exact hxP (hxy' ▸ hyP)
    · exact hxP
  drop_lel k := (h.drop_lel (k + 1)).of_subset h.tail_lelSet.1 (boxUnion_drop_subset L k)
  inter_nonattacking k := by
    have hna : nonattacking ((A.boxes ∪ boxUnion (L.take k)) ∩ boxUnion (L.drop k)) :=
      h.inter_nonattacking (k + 1)
    exact hna.mono (Set.inter_subset_inter_left _ Set.subset_union_right)

/-- Prepending a shape to a shape chain of a piece of a two-factor decomposition of $S$ gives
a shape chain of $S$. -/
lemma cons {Q : SkewShape} (hA : A ≤R S) (hQ : Q ≤L S) (hu : A.boxes ∪ Q.boxes = S.boxes)
    (hna : nonattacking (A.boxes ∩ Q.boxes)) (hL : IsShapeChain Q L) :
    IsShapeChain S (A :: L) where
  -- Proof written by Claude Opus 5.5.
  union_eq := by rw [boxUnion_cons, hL.union_eq, hu]
  take_ler k := by
    cases k with
    | zero => exact lerSet_empty S
    | succ k =>
      change lerSet (A.boxes ∪ boxUnion (L.take k)) S
      have hP := hL.take_ler k
      refine ⟨Set.union_subset hA.1 (hP.1.trans hQ.1), fun x hx y hy hxy hyP => ?_⟩
      rcases hyP with hyA | hyP
      · exact .inl (hA.2 x hx y hy hxy hyA)
      · by_cases hxA : x ∈ A.boxes
        · exact .inl hxA
        · have hxQ : x ∈ Q.boxes := by
            have : x ∈ A.boxes ∪ Q.boxes := hu ▸ hx
            exact this.resolve_left hxA
          exact .inr (hP.2 x hxQ y (hP.1 hyP) hxy hyP)
  drop_lel k := by
    cases k with
    | zero =>
      change lelSet (A.boxes ∪ boxUnion L) S
      rw [hL.union_eq, hu]
      exact lelSet_self S
    | succ k => exact (hL.drop_lel k).trans hQ
  inter_nonattacking k := by
    cases k with
    | zero =>
      change nonattacking (∅ ∩ _)
      rw [Set.empty_inter]
      exact nonattacking_empty
    | succ k =>
      change nonattacking ((A.boxes ∪ boxUnion (L.take k)) ∩ boxUnion (L.drop k))
      have hP := hL.take_ler k
      have hQ' := hL.drop_lel k
      have hnaL := hL.inter_nonattacking k
      -- A box of $A \cap Q_k$ and a box of $P_k \cap Q_k$ in the same row or column agree.
      have key (x y : ℤ × ℤ) (hx : x ∈ A.boxes ∩ boxUnion (L.drop k))
          (hy : y ∈ boxUnion (L.take k) ∩ boxUnion (L.drop k)) (hxy : x.1 = y.1 ∨ x.2 = y.2) :
          x = y := by
        have hxQ : x ∈ Q.boxes := hQ'.1 hx.2
        have hyQ : y ∈ Q.boxes := hQ'.1 hy.2
        rcases le_or_le_of_row_or_col hxy with h | h
        · exact hnaL x ⟨hP.2 x hxQ y hyQ h hy.1, hx.2⟩ y hy hxy
        · exact hna x ⟨hx.1, hxQ⟩ y ⟨hA.2 y (hQ.1 hyQ) x (hQ.1 hxQ) h hx.1, hyQ⟩ hxy
      intro x hx y hy hxy
      rcases hx.1 with hxA | hxP <;> rcases hy.1 with hyA | hyP
      · exact hna x ⟨hxA, hQ'.1 hx.2⟩ y ⟨hyA, hQ'.1 hy.2⟩ hxy
      · exact key x y ⟨hxA, hx.2⟩ ⟨hyP, hy.2⟩ hxy
      · exact (key y x ⟨hyA, hy.2⟩ ⟨hxP, hx.2⟩ (hxy.imp Eq.symm Eq.symm)).symm
      · exact hnaL x ⟨hxP, hx.2⟩ y ⟨hyP, hy.2⟩ hxy

/-- The permutations of a shape chain multiply to $\sigma_S$. -/
theorem dprod (h : IsShapeChain S L) : AspPerm.DProd (L.map SkewShape.σ) = S.σ := by
  -- Proof written by Claude Opus 5.5.
  induction L generalizing S with
  | nil => rw [List.map_nil, AspPerm.DProd_nil, S.σ_eq_id_of_boxes_eq_empty h.union_eq.symm]
  | cons A L ih =>
    rw [List.map_cons, AspPerm.DProd_cons, ih h.tail]
    exact (dprod_iff h.head_ler (ofLelSet_lel h.tail_lelSet)).mpr
      ⟨h.head_union, h.head_nonattacking⟩

/-- A shape chain of $S$ is determined by the permutations of its shapes. -/
theorem eq_of_map_σ_eq {L' : List SkewShape} (h : IsShapeChain S L) (h' : IsShapeChain S L')
    (hσ : L.map SkewShape.σ = L'.map SkewShape.σ) : L = L' := by
  -- Proof written by Claude Opus 5.5.
  induction L generalizing S L' with
  | nil =>
    cases L' with
    | nil => rfl
    | cons _ _ =>
      rw [List.map_nil, List.map_cons] at hσ
      cases hσ
  | cons A L ih =>
    cases L' with
    | nil =>
      rw [List.map_nil, List.map_cons] at hσ
      cases hσ
    | cons A' L' =>
      rw [List.map_cons, List.map_cons, List.cons.injEq] at hσ
      have hQ : ofLelSet S (boxUnion L) h.tail_lelSet = ofLelSet S (boxUnion L') h'.tail_lelSet :=
        lel.eq_of_σ_eq (ofLelSet_lel _) (ofLelSet_lel _)
          (by rw [← h.tail.dprod, ← h'.tail.dprod, hσ.2])
      have hA : A = A' := ler.eq_of_σ_eq h.head_ler h'.head_ler hσ.1
      have hL : L = L' := ih h.tail (hQ ▸ h'.tail) hσ.2
      rw [hA, hL]

end IsShapeChain

/-- Every Hecke factorization of $\sigma_S$ into shift-$0$ factors comes from a shape chain. -/
theorem exists_isShapeChain (M : List AspPerm) (hχ : ∀ α ∈ M, α.χ = 0)
    (hM : AspPerm.DProd M = S.σ) : ∃ L, IsShapeChain S L ∧ L.map SkewShape.σ = M := by
  -- Proof written by Claude Opus 5.5.
  induction M generalizing S with
  | nil =>
    refine ⟨[], IsShapeChain.nil (S.boxes_eq_empty_of_σ_eq_id ?_), rfl⟩
    rw [← hM, AspPerm.DProd_nil]
  | cons α M ih =>
    have hχM : (AspPerm.DProd M).χ = 0 := by
      rw [AspPerm.chi_DProd]
      refine List.sum_eq_zero fun a ha => ?_
      obtain ⟨β, hβ, rfl⟩ := List.mem_map.mp ha
      exact hχ β (List.mem_cons.mpr (.inr hβ))
    -- Split off the first factor, then factor the second piece.
    let p : DemazureFactorization S :=
      ⟨(α, AspPerm.DProd M), hχ α (List.mem_cons.mpr (.inl rfl)), hχM, hM⟩
    let F := ShapeFactorization.ofDprod p
    obtain ⟨L, hL, hLM⟩ := ih (S := F.B) (fun β hβ => hχ β (List.mem_cons.mpr (.inr hβ)))
      (ShapeFactorization.ofDprod_B_σ p).symm
    refine ⟨F.A :: L, IsShapeChain.cons F.hA F.hB F.union_eq F.inter_nonattacking hL, ?_⟩
    rw [List.map_cons, hLM, ShapeFactorization.ofDprod_A_σ]

/-- Hecke factorizations $\sigma_S = \alpha_1 \star \dots \star \alpha_n$ into shift-$0$
factors. -/
abbrev HeckeFactorization (S : SkewShape) : Type :=
  {M : List AspPerm // (∀ α ∈ M, α.χ = 0) ∧ AspPerm.DProd M = S.σ}

/-- Shape chains of $S$. -/
abbrev ShapeChain (S : SkewShape) : Type := {L : List SkewShape // IsShapeChain S L}

/-- Shape chains of $S$ correspond bijectively, via $(A_1, \dots, A_n) \mapsto
(\sigma_{A_1}, \dots, \sigma_{A_n})$, to Hecke factorizations of $\sigma_S$ into shift-$0$
factors. -/
noncomputable def shapeChainEquiv (S : SkewShape) : ShapeChain S ≃ HeckeFactorization S :=
  Equiv.ofBijective
    (fun L => ⟨L.1.map SkewShape.σ, fun α hα => by
        obtain ⟨A, -, rfl⟩ := List.mem_map.mp hα
        exact A.σ_shift, L.2.dprod⟩)
    ⟨fun L L' hLL' => Subtype.ext (L.2.eq_of_map_σ_eq L'.2 (congrArg Subtype.val hLL')),
      fun M =>
        let ⟨L, hL, hLM⟩ := exists_isShapeChain M.1 M.2.1 M.2.2
        ⟨⟨L, hL⟩, Subtype.ext hLM⟩⟩

@[simp] lemma shapeChainEquiv_apply (L : ShapeChain S) :
    (shapeChainEquiv S L : List AspPerm) = L.1.map SkewShape.σ := rfl

/-- Shape chains of $S$ of length $n$ correspond bijectively to Hecke factorizations of
$\sigma_S$ into $n$ shift-$0$ factors. -/
noncomputable def shapeChainEquivOfLength (S : SkewShape) (n : ℕ) :
    {L : ShapeChain S // L.1.length = n} ≃ {M : HeckeFactorization S // M.1.length = n} :=
  (shapeChainEquiv S).subtypeEquiv fun L => by rw [shapeChainEquiv_apply, List.length_map]

end SkewShapes
