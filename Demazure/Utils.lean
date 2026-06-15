/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith

/-!
# Auxiliary Utilities

This file contains small helper lemmas. These are all generic -- they are not specific to this
repository's main objects, so they are collected separately here.
-/

/-! ### Small Finset and Set Helpers

This namespace contains auxiliary lemmas used across the development but not
specific to ASP permutations or Demazure product. -/

namespace Utils

/-- The integer-valued indicator of a proposition: `1` when `P` holds and
`0` otherwise. This is the paper's notation `δ[P]`. -/
noncomputable abbrev oneIf (P : Prop) : ℤ := by
  classical
  exact if P then 1 else 0

/-- The indicator `δ[P]` depends only on the truth value of `P`. -/
lemma oneIf_congr {P Q : Prop} (h : P ↔ Q) :
    oneIf P = oneIf Q := by
  -- Proof written by GPT 5.5.
  by_cases hP : P
  · have hQ : Q := h.mp hP
    simp only [oneIf, hP, hQ, if_true]
  · have hQ : ¬ Q := fun hQ => hP (h.mpr hQ)
    simp only [oneIf, hP, hQ, if_false]

/-- On an integer interval, membership is the difference of two initial
segments. -/
lemma oneIf_Ico_eq_sub (m n : ℤ) (m_le_n : m ≤ n) (k : ℤ) :
    oneIf (k ∈ Finset.Ico m n) = oneIf (k < n) - oneIf (k < m) := by
  -- Proof written by GPT 5.5.
  by_cases k_lt_m : k < m <;> by_cases k_lt_n : k < n
  <;> simp only [oneIf, Finset.mem_Ico] <;> split_ifs <;> omega

/-- Summing the indicator of membership in `A` over any finite superset `U`
counts `A`. -/
lemma sum_oneIf_mem_of_subset {ι : Type*} {A U : Finset ι} (hAU : A ⊆ U) :
    (∑ k ∈ U, oneIf (k ∈ A)) = (A.card : ℤ) := by
  -- Proof written by GPT 5.5.
  classical
  have hfilter : U.filter (fun k => k ∈ A) = A := by
    ext k
    simp only [Finset.mem_filter]
    exact ⟨fun hk => hk.2, fun hk => ⟨hAU hk, hk⟩⟩
  have hsum_eq :
      (∑ k ∈ U, oneIf (k ∈ A)) = ∑ k ∈ U, if k ∈ A then (1 : ℤ) else 0 := by
    apply Finset.sum_congr rfl
    intro k _
    by_cases hkA : k ∈ A
    · simp only [oneIf, hkA, if_true]
    · simp only [oneIf, hkA, if_false]
  rw [hsum_eq, Finset.sum_boole, hfilter]

/-- The difference of the cardinalities of two finite sets is equal to the
difference of the cardinalities of their set-theoretic differences. -/
lemma sub_card_eq_sub_card_diff (S T : Finset ℤ) :
  (↑S.card : ℤ) - ↑T.card = ↑(S \ T).card - ↑(T \ S).card := by
  have h1 := Finset.card_sdiff_add_card_inter S T
  have h2 := Finset.card_sdiff_add_card_inter T S
  rw [Finset.inter_comm] at h2
  omega

lemma card_filter_helper (S : Finset ℤ) (f : ℤ → ℤ) (c : ℤ) :
  (S.filter (f · ≥ c)).card + (S.filter (f · < c)).card = S.card := by
  simpa [not_le] using
    (Finset.card_filter_add_card_filter_not (s := S) (p := fun x => f x ≥ c))

def min_helper {m n : ℤ} (m_pos : m ≥ 1) (n_pos : n ≥ 1)
    {S : Set (ℤ × ℤ)} (mem : ⟨m, n⟩ ∈ S) (nmem : ⟨1, 1⟩ ∉ S) :
  ∃ m' n', m' ≥ 1 ∧ n' ≥ 1 ∧ ⟨m', n'⟩ ∈ S
  ∧ ( ⟨m'-1,n'⟩ ∉ S ∧ m' ≥ 2 ∨ ⟨m', n'-1⟩ ∉ S ∧ n' ≥ 2)
  := by
  by_cases h : ⟨m-1, n⟩ ∉ S ∧ m ≥ 2 ∨ ⟨m, n-1⟩ ∉ S ∧ n ≥ 2
  · use m, n
  push Not at h
  by_cases m_ge_2 : m ≥ 2
  · have mem_m_dec : ⟨m-1, n⟩ ∈ S := by
      by_contra! h1
      linarith [h.1 h1]
    exact min_helper (m := m-1) (m_pos := by omega) n_pos mem_m_dec nmem
  have m_one : m = 1 := le_antisymm (by omega) m_pos
  subst m_one
  let h := h.2
  by_cases n_ge_2 : n ≥ 2
  · have mem_n_dec : ⟨1, n-1⟩ ∈ S:= by
      by_contra! h1
      linarith [h h1]
    exact min_helper m_pos (n := n-1) (n_pos := by omega) mem_n_dec nmem
  have n_one : n = 1 := le_antisymm (by omega) n_pos
  subst n_one
  exfalso; exact nmem mem
termination_by (m+n).toNat
decreasing_by
  all_goals
    simp_wf
    omega


end Utils
