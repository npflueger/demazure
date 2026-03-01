import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
namespace Utils

/-
  The difference between cardinalities of two finite sets is equal to the
  difference of cardinalities of their difference sets. This is a general
  fact that does not appear to yet be in Mathlib.
-/
lemma sub_card_eq_sub_card_diff (S T : Finset ℤ) :
  (↑S.card : ℤ) - ↑T.card = ↑(S \ T).card - ↑(T \ S).card := by
  have h1 := Finset.card_sdiff_add_card_inter S T
  have h2 := Finset.card_sdiff_add_card_inter T S
  rw [Finset.inter_comm] at h2
  omega

lemma card_filter_helper (S : Finset ℤ) (f : ℤ → ℤ) (c : ℤ) :
  (S.filter (f · ≥ c)).card + (S.filter (f · < c)).card = S.card := by
  have h : (S.filter (f · ≥ c)).card + (S.filter (fun x => ¬ f x ≥ c)).card = S.card :=
    Finset.filter_card_add_filter_neg_card_eq_card _
  simp only [not_le] at h
  omega

def min_helper {m n : ℤ} (m_pos : m ≥ 1) (n_pos : n ≥ 1)
    {S : Set (ℤ × ℤ)} (mem : ⟨m, n⟩ ∈ S) (nmem : ⟨1, 1⟩ ∉ S) :
  ∃ m' n', m' ≥ 1 ∧ n' ≥ 1 ∧ ⟨m', n'⟩ ∈ S
  ∧ ( ⟨m'-1,n'⟩ ∉ S ∧ m' ≥ 2 ∨ ⟨m', n'-1⟩ ∉ S ∧ n' ≥ 2)
  := by
  by_cases h : ⟨m-1, n⟩ ∉ S ∧ m ≥ 2 ∨ ⟨m, n-1⟩ ∉ S ∧ n ≥ 2
  · use m, n
  push_neg at h
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
