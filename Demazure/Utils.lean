import Mathlib

namespace Utils

/-
  The difference between cardinalities of two finite sets is equal to the
  difference of cardinalities of their difference sets. This is a general
  fact that does not appear to yet be in Mathlib.
-/
lemma sub_card_eq_sub_card_diff (S T : Finset ℤ) :
  (↑S.card : ℤ) - ↑T.card = ↑(S \ T).card - ↑(T \ S).card := by
  rw [sub_eq_sub_iff_add_eq_add]
  have h' (S T : Finset ℤ) : (↑S.card : ℤ) + (T \ S).card  = (S ∪ T).card := by
    have : Disjoint S (T \ S) := by
      rw [Finset.disjoint_iff_ne]
      rintro a as b hb
      apply (Finset.mem_sdiff).mp at hb
      intro hab
      rw [hab] at as
      exact hb.2 as
    rw [← Nat.cast_add, ← Finset.card_union_of_disjoint this]
    suffices S ∪ (T \ S) = S ∪ T by rw[this]
    ext x
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hx
      rcases hx with (hx | hx)
      · left; exact hx
      · right; exact hx.1
    · intro hx
      by_cases h : x ∈ S
      · left; exact h
      · right
        have : x ∈ T := by
          contrapose! hx; exact ⟨h,hx⟩
        exact ⟨this, h⟩
  rw [h' S T]
  rw [add_comm, h' T S, Finset.union_comm]

-- [TODO] see if this helper is in Mathlib somewhere, or has a simpler proof.
lemma card_filter_helper (S : Finset ℤ) (f : ℤ → ℤ) (c : ℤ) :
  (S.filter (f · ≥ c)).card + (S.filter (f · < c)).card = S.card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_eq_sum_ones]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hn
  by_cases ineq : f x ≥ c <;> simp [ineq]

end Utils
