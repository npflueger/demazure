import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star

/-- Function f satisfying the hypotheses of Lemma 4.6. -/
structure Valley where
  f : ℤ → ℤ
  rises : ∀ m : ℤ, {n : ℤ | f n ≤ m}.Finite

instance : CoeFun Valley (fun _ => ℤ → ℤ) :=
  ⟨Valley.f⟩


namespace Valley
variable (v : Valley)

noncomputable def floor (m : ℤ) : Finset ℤ := Set.Finite.toFinset (v.rises m)

@[simp] lemma mem_floor (m n : ℤ) : n ∈ v.floor m ↔ v.f n ≤ m := by
  simp [Valley.floor]

lemma floor_image_nonempty (n : ℤ) : (Finset.image v.f <| v.floor (v.f n)).Nonempty := by
  refine ⟨v.f n, ?_⟩
  exact Finset.mem_image.mpr ⟨n, by simp, rfl⟩

noncomputable def min : ℤ := Finset.min' (Finset.image v.f (v.floor (v.f 0)))
  (v.floor_image_nonempty 0)

lemma min_mem : ∃ a ∈ {n | v.f n ≤ v.f 0}, v.f a = v.min := by
  simpa [Finset.mem_image] using
    Finset.min'_mem (Finset.image v.f (v.floor (v.f 0))) (v.floor_image_nonempty 0)

lemma min_spec : ∀ n : ℤ, v.f n ≥ v.min := by
  intro n
  by_cases h : v.f n > v.f 0
  · rcases v.min_mem with ⟨m, hm⟩
    have := le_trans (hm.1) (le_of_lt h)
    rwa [hm.2] at this
  have mem_floor : n ∈ v.floor (v.f 0) := by
    simpa using le_of_not_gt h
  have mem_image_floor : v.f n ∈ Finset.image v.f (v.floor (v.f 0)) := by
    exact Finset.mem_image.mpr ⟨n, mem_floor, rfl⟩
  exact Finset.min'_le (Finset.image v.f (v.floor (v.f 0))) (v.f n) mem_image_floor

lemma argmin_set_nonempty : (v.floor v.min).Nonempty := by
  rcases v.min_mem with ⟨m, -, hm⟩
  exact ⟨m, by simp [hm]⟩

/-- The *maximum* preimage of the minimum value of f. -/
noncomputable def M : ℤ := Finset.max' (v.floor v.min) v.argmin_set_nonempty

lemma f_M : v.f v.M = v.min := by
  have ge : v.f v.M ≥ v.min := v.min_spec v.M
  have le : v.f v.M ≤ v.min := by
    have : v.M ∈ v.floor v.min := Finset.max'_mem (v.floor v.min) v.argmin_set_nonempty
    simpa using this
  exact le_antisymm le ge

lemma M_spec : ∀ n : ℤ, v.f n ≥ v.f v.M ∧ (n > v.M → v.f n > v.f v.M) := by
  intro n
  constructor
  · have := v.min_spec n
    rwa [v.f_M]
  · intro n_gt_vM
    contrapose! n_gt_vM with fn_le_fM
    have : n ∈ v.floor v.min := by
      simpa [v.f_M] using fn_le_fM
    simpa using Finset.le_max' (v.floor v.min) n this

def shift_down (k : ℤ) : Valley where
  f := fun n => v.f n - k
  rises := by
    intro m
    have : {n : ℤ | v.f n - k ≤ m} = {n : ℤ | v.f n ≤ m + k} := by
      ext n
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h; linarith
      · intro h; linarith
    rw [this]
    apply v.rises

lemma shift_down_M (k : ℤ) : (v.shift_down k).M = v.M := by
  let v' := v.shift_down k
  suffices v.M = v'.M by rw [this]
  have ge : v.f v'.M ≥ v.f v.M := (v.M_spec v'.M).1
  have le : v'.f v'.M ≤ v'.f v.M := by
    exact ((v.shift_down k).M_spec v.M).1
  have f_eq : v.f v.M = v.f v'.M := by
    subst v'
    unfold Valley.shift_down at le ge ⊢
    simp at le
    omega
  have f'_eq : v'.f v.M = v'.f v'.M := by
    subst v'
    unfold Valley.shift_down at le ge ⊢
    simp at le ⊢
    omega

  have M_le_M' : v.M ≤ v'.M := by
    have := (v'.M_spec v.M).2
    contrapose! ge with h
    have := this h
    rw [f'_eq] at this
    exfalso; apply lt_irrefl (v'.f v'.M) this
  have M'_le_M : v'.M ≤ v.M := by
    have := (v.M_spec v'.M).2
    contrapose! le with h
    have := this h
    rw [f_eq] at this
    exfalso; apply lt_irrefl (v.f v'.M) this
  exact le_antisymm M_le_M' M'_le_M

lemma shift_down_min (k : ℤ) : (v.shift_down k).min = v.min - k := by
  let v' := v.shift_down k
  rw [← v'.f_M, ← v.f_M, v.shift_down_M k]
  subst v'
  unfold Valley.shift_down
  simp

end Valley
