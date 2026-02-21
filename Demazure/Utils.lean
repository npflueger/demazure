import Mathlib
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
  linarith

end Utils
