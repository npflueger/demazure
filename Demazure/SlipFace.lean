import Mathlib
import Demazure.Valley

/-- Definition 3.1 -/
structure SlipFace where
  s : ℤ → ℤ → ℤ
  χ : ℤ
  a_step : ∀ a b : ℤ, s a b ≤ s (a+1) b ∧ s (a+1) b ≤ s a b + 1
  b_step : ∀ a b : ℤ, s a (b+1) ≤ s a b ∧ s a b ≤ s a (b+1) + 1
  nonneg : ∀ a b, s a b ≥ 0
  ge_diff : ∀ a b, s a b ≥ a - b + χ
  small_a : ∀ b, ∃ A, ∀ a ≤ A, s a b  = 0
  large_a : ∀ b, ∃ A, ∀ a ≥ A, s a b = a - b + χ
  small_b : ∀ a, ∃ B, ∀ b ≤ B, s a b = a - b + χ
  large_b : ∀ a, ∃ B, ∀ b ≥ B, s a b = 0

instance : CoeFun SlipFace (fun _ => ℤ → ℤ → ℤ) :=
  ⟨SlipFace.s⟩


namespace SlipFace
variable (sf : SlipFace)

/-- Definition 3.4 -/
def dual : SlipFace := {
  s := fun b a => sf a b - a + b - sf.χ
  χ := -sf.χ,
  a_step := by
    rintro b a
    have step := sf.b_step a b
    constructor <;> omega
  b_step := by
    rintro b a
    have step := sf.a_step a b
    constructor <;> omega
  nonneg := by
    rintro b a
    linarith [sf.ge_diff a b]
  ge_diff := by
    rintro b a
    linarith [sf.nonneg a b]
  small_a := by
    rintro b
    obtain ⟨A, hA⟩ := sf.small_b b
    use A
    rintro a ha
    rw [hA a ha]
    omega
  large_a := by
    rintro b
    obtain ⟨A, hA⟩ := sf.large_b b
    use A
    rintro a ha
    rw [hA a ha]
    omega
  small_b := by
    rintro a
    obtain ⟨B, hB⟩ := sf.small_a a
    use B
    rintro b hb
    rw [hB b hb]
    omega
  large_b := by
    rintro a
    obtain ⟨B, hB⟩ := sf.large_a a
    use B
    rintro b hb
    rw [hB b hb]
    omega
}

lemma duality (a b : ℤ) : sf a b - sf.dual b a = a - b + sf.χ := by
  dsimp [SlipFace.dual]
  omega

/-- Properties D1 and D2 -/
structure D_props (f : ℤ → ℤ → ℤ) : Prop where
  a_step : ∀ a b : ℤ, f (a+1) b ≥ f a b
  b_step : ∀ a b : ℤ, f a (b+1) ≤ f a b
  large_b : ∀ a, ∃ B, ∀ b ≥ B, f a b = 0
  small_a : ∀ b, ∃ A, ∀ a ≤ A, f a b = 0

lemma mono_a_of_D_props (f : ℤ → ℤ → ℤ) (h : D_props f) : ∀ a a' b, a ≤ a' → f a' b ≥ f a b := by
  intro a a' b ha
  let n : ℕ := (a' - a).toNat
  have a'_eq : a' = a + n := by
    omega
  rw [a'_eq]
  induction n with
  | zero => simp
  | succ n ih =>
    apply le_trans ih
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc]
    exact h.a_step (a + n) b

lemma mono_b_of_D_props (f : ℤ → ℤ → ℤ) (h : D_props f) : ∀ a b b', b ≤ b' → f a b' ≤ f a b := by
  intro a b b' hb
  let n : ℕ := (b' - b).toNat
  have b'_eq : b' = b + n := by
    omega
  rw [b'_eq]
  induction n with
  | zero => simp
  | succ n ih =>
    apply le_trans _ ih
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc]
    exact h.b_step a (b + n)

/-- Lemma 3.6 -/
lemma sf_of_D_props {s t : ℤ → ℤ → ℤ} {χ : ℤ} (h : ∀ a b, s a b - t b a = a - b + χ) :
  D_props s ∧ D_props t →
  ∃ sf : SlipFace, (sf.s = s ∧ sf.χ = χ) ∧ sf.dual.s = t := by
  rintro ⟨sp, tp⟩
  let sf : SlipFace := {
    s := s,
    χ := χ,
    a_step := by
      intro a b
      have step0 := sp.a_step a b
      have step1 := tp.b_step b a
      constructor <;> linarith [h (a+1) b, h a (b+1), h a b]
    b_step := by
      intro a b
      have step0 := sp.b_step a b
      have step1 := tp.a_step b a
      constructor <;> linarith [h a (b+1), h (a+1) b, h a b]
    nonneg := by
      intro a b
      obtain ⟨A, hA⟩ := sp.small_a b
      by_cases ha : a ≤ A
      · exact le_of_eq <| (Eq.symm <| hA a ha)
      · have ha : A ≤ a := by omega
        rw [← hA A (le_refl A)]
        exact mono_a_of_D_props s sp A a b ha
    ge_diff := by
      intro a b
      rw [← h a b]
      suffices t b a ≥ 0 by omega
      obtain ⟨B, hB⟩ := tp.small_a a
      by_cases hb : b ≤ B
      · exact le_of_eq <| (Eq.symm <| hB b hb)
      · have hb : B ≤ b := by omega
        rw [← hB B (le_refl B)]
        exact mono_a_of_D_props t tp B b a hb
    small_a := by
      intro b
      obtain ⟨A, hA⟩ := sp.small_a b
      use A
    large_a := by
      intro b
      obtain ⟨A, hA⟩ := tp.large_b b
      use A
      intro a ha
      specialize hA a ha
      specialize h a b
      rwa [hA, sub_zero] at h
    small_b := by
      intro a
      obtain ⟨B, hB⟩ := tp.small_a a
      use B
      intro b hb
      specialize hB b hb
      specialize h a b
      rwa [hB, sub_zero] at h
    large_b := by
      intro a
      obtain ⟨B, hB⟩ := sp.large_b a
      use B
  }
  use sf
  constructor
  · constructor <;> rfl
  · ext a b
    dsimp [SlipFace.dual]
    linarith [h b a]

lemma D_props_of_sf (sf : SlipFace) : D_props sf.s ∧ D_props sf.dual.s := by
  constructor
  · constructor
    · intro a b
      exact (sf.a_step a b).1
    · intro a b
      exact (sf.b_step a b).1
    · intro a
      exact sf.large_b a
    · intro b
      exact sf.small_a b
  · constructor
    · intro a b
      exact (sf.dual.a_step a b).1
    · intro a b
      exact (sf.dual.b_step a b).1
    · intro a
      exact sf.dual.large_b a
    · intro b
      exact sf.dual.small_a b

end SlipFace
