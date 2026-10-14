/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import Demazure.SkewShapes.Basic
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Order.SuccPred.Int

/-!
# Skew shapes from 321-avoiding permutations

Every shift-$0$ ASP permutation $\tau$ whose sources and sinks can be separated by a set
$U \subseteq \mathbb{Z}$ (equivalently, every shift-$0$ 321-avoiding ASP permutation) is
$\sigma_S$ for a skew shape $S$. Given a lattice path whose step $n$ goes east exactly when
$n \in U$, the shape has one box $(i(v), j(u))$ for each inversion $(u, v)$ of $\tau$, where
$(i(n), j(n))$ is the $n$th vertex of the path. Conversely, every skew shape arises this way from
its own boundary path.

The first draft of this file was written by Claude Opus 5.5, following a design by
Nathan Pflueger.
-/

@[expose] public section

namespace SkewShapes

variable {S : SkewShape}

/-- A lattice path through $\mathbb{Z} \times \mathbb{Z}$, recorded by the column $c(n)$ of
its $n$th vertex. Each step goes east ($c(n+1) = c(n) + 1$) or north ($c(n+1) = c(n)$), and the
$n$th vertex is $(c(n) - n, c(n))$, of content $n$. -/
@[ext] structure LatticePath where
  col : ℤ → ℤ
  col_succ : ∀ n, col (n + 1) = col n ∨ col (n + 1) = col n + 1

namespace LatticePath

variable (p : LatticePath)

/-- The row $c(n) - n$ of the $n$th vertex. -/
def row (n : ℤ) : ℤ := p.col n - n

/-- Step $n$ of the path goes east. -/
def East (n : ℤ) : Prop := p.col (n + 1) = p.col n + 1

variable {p}

lemma col_succ_of_not_east {n : ℤ} (h : ¬ p.East n) : p.col (n + 1) = p.col n :=
  (p.col_succ n).resolve_right h

lemma col_mono {a b : ℤ} (h : a ≤ b) : p.col a ≤ p.col b := by
  induction b, h using Int.leInduction with
  | base => exact le_rfl
  | succ n _ ih => rcases p.col_succ n with h | h <;> omega

lemma col_le_add {a b : ℤ} (h : a ≤ b) : p.col b ≤ p.col a + (b - a) := by
  induction b, h using Int.leInduction with
  | base => omega
  | succ n _ ih => rcases p.col_succ n with h | h <;> omega

lemma row_anti {a b : ℤ} (h : a ≤ b) : p.row b ≤ p.row a := by
  have := col_le_add (p := p) h
  simp only [row]
  omega

lemma col_lt_of_east {a b : ℤ} (hab : a < b) (ha : p.East a) : p.col a < p.col b := by
  have := col_mono (p := p) (show a + 1 ≤ b by omega)
  rw [East] at ha
  omega

lemma row_lt_of_not_east {a b : ℤ} (hab : a < b) (ha : ¬ p.East a) : p.row b < p.row a := by
  have h1 := row_anti (p := p) (show a + 1 ≤ b by omega)
  have h2 := col_succ_of_not_east ha
  simp only [row] at *
  omega

lemma le_of_col_le {a b : ℤ} (hb : p.East b) (h : p.col a ≤ p.col b) : a ≤ b := by
  by_contra! hba
  exact (col_lt_of_east hba hb).not_ge h

lemma le_of_row_le {a b : ℤ} (ha : ¬ p.East a) (h : p.row a ≤ p.row b) : b ≤ a := by
  by_contra! hab
  exact (row_lt_of_not_east hab ha).not_ge h

lemma eq_of_col_eq {a b : ℤ} (ha : p.East a) (hb : p.East b) (h : p.col a = p.col b) : a = b :=
  le_antisymm (le_of_col_le hb h.le) (le_of_col_le ha h.ge)

lemma eq_of_row_eq {a b : ℤ} (ha : ¬ p.East a) (hb : ¬ p.East b) (h : p.row a = p.row b) :
    a = b :=
  le_antisymm (le_of_row_le hb h.ge) (le_of_row_le ha h.le)

/-- Along a run of east steps, the column increases by one at each step. -/
lemma col_eq_of_east {a b : ℤ} (hab : a ≤ b) (h : ∀ n, a ≤ n → n < b → p.East n) :
    p.col b = p.col a + (b - a) := by
  induction b, hab using Int.leInduction with
  | base => omega
  | succ n hn ih =>
    have := h n hn (by omega)
    rw [East] at this
    rw [this, ih fun m hm hm' => h m hm (by omega)]
    ring

/-- Along a run of north steps, the column is constant. -/
lemma col_eq_of_not_east {a b : ℤ} (hab : a ≤ b) (h : ∀ n, a ≤ n → n < b → ¬ p.East n) :
    p.col b = p.col a := by
  induction b, hab using Int.leInduction with
  | base => rfl
  | succ n hn ih =>
    rw [col_succ_of_not_east (h n hn (by omega)), ih fun m hm hm' => h m hm (by omega)]

/-- The column takes every value between $c(a)$ and $c(b)$, at the start of an east step or
at $b$. -/
lemma exists_col_eq {a b c : ℤ} (hab : a ≤ b) (h1 : p.col a ≤ c) (h2 : c ≤ p.col b) :
    ∃ n, a ≤ n ∧ n ≤ b ∧ p.col n = c ∧ (n = b ∨ p.East n) := by
  -- Proof written by Claude Opus 5.5.
  induction b, hab using Int.leInduction with
  | base => exact ⟨a, le_rfl, le_rfl, by omega, .inl rfl⟩
  | succ n hn ih =>
    by_cases hc : c ≤ p.col n
    · obtain ⟨m, ham, hmn, hm, hm'⟩ := ih hc
      rcases hm' with rfl | he
      · by_cases he : p.East m
        · exact ⟨m, ham, by omega, hm, .inr he⟩
        · exact ⟨m + 1, by omega, le_rfl, by rw [col_succ_of_not_east he, hm], .inl rfl⟩
      · exact ⟨m, ham, by omega, hm, .inr he⟩
    · rcases p.col_succ n with h | h
      · omega
      · exact ⟨n + 1, by omega, le_rfl, by omega, .inl rfl⟩

/-- The row takes every value between $r(b)$ and $r(a)$, at the start of a north step or at
$b$. -/
lemma exists_row_eq {a b r : ℤ} (hab : a ≤ b) (h1 : p.row b ≤ r) (h2 : r ≤ p.row a) :
    ∃ n, a ≤ n ∧ n ≤ b ∧ p.row n = r ∧ (n = b ∨ ¬ p.East n) := by
  -- Proof written by Claude Opus 5.5.
  induction b, hab using Int.leInduction with
  | base => exact ⟨a, le_rfl, le_rfl, by omega, .inl rfl⟩
  | succ n hn ih =>
    by_cases hr : p.row n ≤ r
    · obtain ⟨m, ham, hmn, hm, hm'⟩ := ih hr
      rcases hm' with rfl | he
      · by_cases he : p.East m
        · refine ⟨m + 1, by omega, le_rfl, ?_, .inl rfl⟩
          rw [East] at he
          simp only [row] at hm ⊢
          omega
        · exact ⟨m, ham, by omega, hm, .inr he⟩
      · exact ⟨m, ham, by omega, hm, .inr he⟩
    · have := row_anti (p := p) (show n ≤ n + 1 by omega)
      rcases p.col_succ n with h | h
      · exact ⟨n + 1, by omega, le_rfl, by simp only [row] at *; omega, .inl rfl⟩
      · simp only [row] at *
        omega

/-- A path is compatible with $\tau$ if the step at each source of an inversion goes east and
the step at each sink goes north. -/
structure Compatible (p : LatticePath) (τ : AspPerm) : Prop where
  east : ∀ u v, (u, v) ∈ inv_set τ → p.East u
  not_east : ∀ u v, (u, v) ∈ inv_set τ → ¬ p.East v

variable {τ : AspPerm}

/-- For a compatible path, $\tau$ increases from any position to a later east step. -/
lemma Compatible.le_of_east (hc : p.Compatible τ) {u u' : ℤ} (hu : u ≤ u') (he : p.East u') :
    τ u ≤ τ u' := by
  rcases hu.lt_or_eq with hlt | rfl
  · by_contra! hτ
    exact hc.not_east u u' ⟨hlt, hτ⟩ he
  · exact le_rfl

/-- For a compatible path, $\tau$ increases from a north step to any later position. -/
lemma Compatible.le_of_not_east (hc : p.Compatible τ) {v v' : ℤ} (hv : v' ≤ v)
    (he : ¬ p.East v') : τ v' ≤ τ v := by
  rcases hv.lt_or_eq with hlt | rfl
  · by_contra! hτ
    exact he (hc.east v' v ⟨hlt, hτ⟩)
  · exact le_rfl

/-- An east step and a later north step nested inside an inversion form an inversion. -/
lemma Compatible.inv_of_nested (hc : p.Compatible τ) {u₁ v₁ u v : ℤ} (h : (u₁, v₁) ∈ inv_set τ)
    (hu : u₁ ≤ u) (hv : v ≤ v₁) (huv : u < v) (hue : p.East u) (hve : ¬ p.East v) :
    (u, v) ∈ inv_set τ :=
  ⟨huv, lt_of_le_of_lt (hc.le_of_not_east hv hve) (lt_of_lt_of_le h.2 (hc.le_of_east hu hue))⟩

/-- The box $(r(v), c(u))$ attached to an inversion $(u, v)$. -/
def box (p : LatticePath) (q : ℤ × ℤ) : ℤ × ℤ := (p.row q.2, p.col q.1)

/-- The skew shape whose boxes are $(r(v), c(u))$ for the inversions $(u, v)$ of $\tau$. -/
def shape (p : LatticePath) (τ : AspPerm) (hc : p.Compatible τ) : SkewShape where
  boxes := p.box '' inv_set τ
  closed := by
    -- Proof written by Claude Opus 5.5.
    rintro x ⟨r, c⟩ z hxy hyz ⟨⟨u₁, v₁⟩, h₁, rfl⟩ ⟨⟨u₂, v₂⟩, h₂, rfl⟩
    obtain ⟨hr₁, hc₁⟩ := Prod.le_def.mp hxy
    obtain ⟨hr₂, hc₂⟩ := Prod.le_def.mp hyz
    simp only [box] at hr₁ hc₁ hr₂ hc₂
    have hu : u₁ ≤ u₂ := le_of_col_le (hc.east _ _ h₂) (hc₁.trans hc₂)
    have hv : v₂ ≤ v₁ := le_of_row_le (hc.not_east _ _ h₁) (hr₁.trans hr₂)
    obtain ⟨n, hn₁, hn₂, hcol, hn⟩ := exists_col_eq hu hc₁ hc₂
    obtain ⟨m, hm₁, hm₂, hrow, hm⟩ := exists_row_eq hv hr₁ hr₂
    have hne : p.East n := hn.elim (fun h => h ▸ hc.east _ _ h₂) id
    have hme : ¬ p.East m := hm.elim (fun h => h ▸ hc.not_east _ _ h₁) id
    have hnm : n < m := lt_of_le_of_lt hn₂ (lt_of_lt_of_le h₂.1 hm₁)
    exact ⟨(n, m), hc.inv_of_nested h₁ hn₁ hm₂ hnm hne hme, by rw [box, hrow, hcol]⟩
  finite_below := by
    -- Proof written by Claude Opus 5.5.
    -- Boxes northwest of $(r(v_1), c(u_1))$ come from inversions $(u, v)$ with $u \le u_1$ and
    -- $v_1 \le v$, which are finite in number.
    rintro _ ⟨⟨u₁, v₁⟩, h₁, rfl⟩
    refine (((τ.nw_finite (τ v₁) (u₁ + 1)).prod (τ.se_finite (τ u₁) v₁)).image p.box).subset
      ?_ |>.to_subtype
    rintro _ ⟨⟨⟨u, v⟩, h, rfl⟩, hle⟩
    obtain ⟨hr, hcol⟩ := Prod.le_def.mp hle
    simp only [box] at hr hcol
    have hu : u ≤ u₁ := le_of_col_le (hc.east _ _ h₁) hcol
    have hv : v₁ ≤ v := le_of_row_le (hc.not_east _ _ h) hr
    have hτu : τ u ≤ τ u₁ := hc.le_of_east hu (hc.east _ _ h₁)
    have hτv : τ v₁ ≤ τ v := hc.le_of_not_east hv (hc.not_east _ _ h₁)
    exact ⟨(u, v), ⟨⟨by omega, by linarith [h.2]⟩, ⟨hv, by linarith [h.2]⟩⟩, rfl⟩
  finite_above := by
    -- Proof written by Claude Opus 5.5.
    rintro _ ⟨⟨u₁, v₁⟩, h₁, rfl⟩
    refine (((Set.finite_Icc u₁ v₁).prod (Set.finite_Icc u₁ v₁)).image p.box).subset
      ?_ |>.to_subtype
    rintro _ ⟨⟨⟨u, v⟩, h, rfl⟩, hle⟩
    obtain ⟨hr, hcol⟩ := Prod.le_def.mp hle
    simp only [box] at hr hcol
    have hu : u₁ ≤ u := le_of_col_le (hc.east _ _ h) hcol
    have hv : v ≤ v₁ := le_of_row_le (hc.not_east _ _ h₁) hr
    have := h.1
    exact ⟨(u, v), ⟨⟨hu, by omega⟩, ⟨by omega, hv⟩⟩, rfl⟩

/-- The box of `p.shape τ hc` attached to an inversion $(u, v)$ of $\tau$. -/
def shapeBox (hc : p.Compatible τ) {u v : ℤ} (h : (u, v) ∈ inv_set τ) : p.shape τ hc :=
  ⟨p.box (u, v), (u, v), h, rfl⟩

/-- The box attached to the inversion $(u, v)$ has $u$-value $u$. -/
lemma shape_u (hc : p.Compatible τ) {u v : ℤ} (h : (u, v) ∈ inv_set τ) :
    (p.shape τ hc).u (shapeBox hc h) = u := by
  -- Proof written by Claude Opus 5.5.
  -- The southernmost box in the column $c(u)$ comes from the least $v_0$ with $(u, v_0)$ an
  -- inversion, and every step from $u$ to $v_0$ goes east.
  obtain ⟨v₀, h₀, hmin⟩ := Int.exists_least_of_bdd (P := fun z => (u, z) ∈ inv_set τ)
    ⟨u, fun z hz => hz.1.le⟩ ⟨v, h⟩
  have hU : (p.shape τ hc).U (shapeBox hc h) = p.box (u, v₀) := by
    refine (((p.shape τ hc).U_spec (shapeBox hc h) (p.box (u, v₀))).mpr
      ⟨rfl, ⟨_, h₀, rfl⟩, ?_⟩).symm
    rintro ⟨⟨u', v'⟩, h', hbox⟩
    obtain ⟨hr, hcol⟩ := Prod.mk_inj.mp hbox
    simp only [box, add_zero] at hr hcol
    have hu' : u' = u := eq_of_col_eq (hc.east _ _ h') (hc.east _ _ h) hcol
    subst hu'
    have := hmin v' h'
    have := row_anti (p := p) this
    omega
  have hcol : p.col v₀ = p.col u + (v₀ - u) := by
    refine col_eq_of_east h₀.1.le fun n hn hn' => ?_
    rcases hn.lt_or_eq with hlt | rfl
    · by_contra hne
      rcases lt_or_gt_of_ne (τ.injective.ne (show n ≠ u by omega)) with hτ | hτ
      · exact (hmin n ⟨hlt, hτ⟩).not_gt hn'
      · exact hne (hc.east n v₀ ⟨hn', lt_trans h₀.2 hτ⟩)
    · exact hc.east _ _ h₀
  rw [SkewShape.u, hU, Δ_eq]
  simp only [box, row]
  omega

/-- The box attached to the inversion $(u, v)$ has $v$-value $v$. -/
lemma shape_v (hc : p.Compatible τ) {u v : ℤ} (h : (u, v) ∈ inv_set τ) :
    (p.shape τ hc).v (shapeBox hc h) = v := by
  -- Proof written by Claude Opus 5.5.
  -- The box just east of the row $r(v)$ comes from the greatest $u_0$ with $(u_0, v)$ an
  -- inversion, and every step after $u_0$ and before $v$ goes north.
  obtain ⟨u₀, h₀, hmax⟩ := Int.exists_greatest_of_bdd (P := fun z => (z, v) ∈ inv_set τ)
    ⟨v, fun z hz => hz.1.le⟩ ⟨u, h⟩
  have hV : (p.shape τ hc).V (shapeBox hc h) = (p.row v, p.col u₀ + 1) := by
    refine (((p.shape τ hc).V_spec (shapeBox hc h) (p.row v, p.col u₀ + 1)).mpr
      ⟨rfl, ⟨_, h₀, ?_⟩, ?_⟩).symm
    · simp only [box, Prod.mk_sub_mk, sub_zero, add_sub_cancel_right]
    · rintro ⟨⟨u', v'⟩, h', hbox⟩
      obtain ⟨hr, hcol⟩ := Prod.mk_inj.mp hbox
      simp only at hr hcol
      have hv' : v' = v := eq_of_row_eq (hc.not_east _ _ h') (hc.not_east _ _ h) hr
      subst hv'
      have := hmax u' h'
      have := col_mono (p := p) this
      omega
  have hcol : p.col v = p.col u₀ + 1 := by
    rw [← hc.east _ _ h₀]
    refine col_eq_of_not_east (show u₀ + 1 ≤ v by have := h₀.1; omega) fun n hn hn' hne => ?_
    rcases lt_or_gt_of_ne (τ.injective.ne (show n ≠ u₀ by omega)) with hτ | hτ
    · exact hc.not_east u₀ n ⟨by omega, hτ⟩ hne
    · exact (hmax n ⟨hn', lt_trans h₀.2 hτ⟩).not_gt (by omega)
  rw [SkewShape.v, hV, Δ_eq]
  simp only [row]
  omega

/-- The permutation of `p.shape τ hc` is $\tau$, when $\tau$ has shift $0$. -/
theorem shape_σ (hc : p.Compatible τ) (hχ : τ.χ = 0) : (p.shape τ hc).σ = τ := by
  -- Proof written by Claude Opus 5.5.
  apply AspPerm.eq_of_inv_set_eq_of_chi_eq
  · rw [SkewShape.σ_invSet]
    ext ⟨a, b⟩
    constructor
    · rintro ⟨⟨_, ⟨u, v⟩, h, rfl⟩, hx⟩
      rw [← hx]
      change ((p.shape τ hc).u (shapeBox hc h), (p.shape τ hc).v (shapeBox hc h)) ∈ inv_set τ
      rw [shape_u, shape_v]
      exact h
    · intro h
      exact ⟨shapeBox hc h, by rw [shape_u, shape_v]⟩
  · rw [SkewShape.σ_shift, hχ]

end LatticePath

open Classical in
/-- The number of elements of $U$ in $[0, n)$, or minus the number in $[n, 0)$ when $n < 0$. -/
noncomputable def signedCount (U : Set ℤ) (n : ℤ) : ℤ :=
  ((Finset.Ico 0 n).filter (· ∈ U)).card - ((Finset.Ico n 0).filter (· ∈ U)).card

@[simp] lemma signedCount_zero (U : Set ℤ) : signedCount U 0 = 0 := by
  simp only [signedCount, Finset.Ico_self, Finset.filter_empty, Finset.card_empty, sub_self]

open Classical in
lemma signedCount_succ (U : Set ℤ) (n : ℤ) :
    signedCount U (n + 1) = signedCount U n + if n ∈ U then 1 else 0 := by
  -- Proof written by Claude Opus 5.5.
  simp only [signedCount]
  rcases le_or_gt 0 n with hn | hn
  · rw [Finset.Ico_eq_empty_of_le (show 0 ≤ n + 1 by omega), Finset.Ico_eq_empty_of_le hn,
      ← Finset.insert_Ico_right_eq_Ico_add_one_of_not_isMax hn (not_isMax n),
      Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]
      push_cast
      ring
    · ring
  · rw [Finset.Ico_eq_empty_of_le (show n + 1 ≤ 0 by omega), Finset.Ico_eq_empty_of_le hn.le,
      ← Finset.insert_Ico_add_one_left_eq_Ico hn, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]
      push_cast
      ring
    · ring

lemma signedCount_add_compl (U : Set ℤ) (n : ℤ) : signedCount U n + signedCount Uᶜ n = n := by
  -- Proof written by Claude Opus 5.5.
  have step (m : ℤ) : signedCount U (m + 1) + signedCount Uᶜ (m + 1) =
      signedCount U m + signedCount Uᶜ m + 1 := by
    rw [signedCount_succ, signedCount_succ]
    by_cases h : m ∈ U <;> simp [h] <;> ring
  induction n using Int.induction_on with
  | zero => simp only [signedCount_zero, add_zero]
  | succ m ih => rw [step, ih]
  | pred m ih =>
    have := step (-(m : ℤ) - 1)
    rw [sub_add_cancel, ih] at this
    omega

namespace LatticePath

/-- The path with $c(0) = C$ whose east steps are exactly those in $U$: its $n$th vertex is
$(i(n), j(n))$ with $j(n) = C + \#\{m \in [0, n) : m \in U\}$ and
$i(n) = C - \#\{m \in [0, n) : m \notin U\}$, counted with sign when $n < 0$. -/
noncomputable def ofSet (C : ℤ) (U : Set ℤ) : LatticePath where
  col n := C + signedCount U n
  col_succ n := by
    rw [signedCount_succ]
    split_ifs
    · exact .inr (by ring)
    · exact .inl (by ring)

lemma ofSet_col (C : ℤ) (U : Set ℤ) (n : ℤ) : (ofSet C U).col n = C + signedCount U n := rfl

lemma ofSet_row (C : ℤ) (U : Set ℤ) (n : ℤ) : (ofSet C U).row n = C - signedCount Uᶜ n := by
  have := signedCount_add_compl U n
  rw [row, ofSet_col]
  omega

lemma ofSet_east_iff (C : ℤ) (U : Set ℤ) (n : ℤ) : (ofSet C U).East n ↔ n ∈ U := by
  rw [East, ofSet_col, ofSet_col, signedCount_succ]
  split_ifs with h
  · simp only [h, iff_true]
    ring
  · simp only [h, iff_false]
    omega

/-- Every lattice path is determined by $c(0)$ and its set of east steps. -/
lemma eq_ofSet (p : LatticePath) : p = ofSet (p.col 0) {n | p.East n} := by
  -- Proof written by Claude Opus 5.5.
  ext n
  rw [ofSet_col]
  have step (m : ℤ) : p.col (m + 1) - signedCount {n | p.East n} (m + 1) =
      p.col m - signedCount {n | p.East n} m := by
    rw [signedCount_succ]
    split_ifs with h
    · rw [Set.mem_ofPred_eq, East] at h
      omega
    · rw [Set.mem_ofPred_eq] at h
      rw [col_succ_of_not_east h]
      ring
  suffices p.col n - signedCount {n | p.East n} n = p.col 0 by omega
  induction n using Int.induction_on with
  | zero => rw [signedCount_zero, sub_zero]
  | succ m ih => rw [step, ih]
  | pred m ih =>
    have := step (-(m : ℤ) - 1)
    rw [sub_add_cancel, ih] at this
    exact this.symm

lemma ofSet_box (C : ℤ) (U : Set ℤ) (u v : ℤ) :
    (ofSet C U).box (u, v) = (C - signedCount Uᶜ v, C + signedCount U u) := by
  rw [box, ofSet_row, ofSet_col]

/-- The path attached to $(C, U)$ is compatible with $\tau$ when $U$ contains every source and
no sink of an inversion of $\tau$. -/
lemma ofSet_compatible {τ : AspPerm} {C : ℤ} {U : Set ℤ} (hsrc : ∀ u v, (u, v) ∈ inv_set τ → u ∈ U)
    (hsnk : ∀ u v, (u, v) ∈ inv_set τ → v ∉ U) : (ofSet C U).Compatible τ where
  east u v h := (ofSet_east_iff C U u).mpr (hsrc u v h)
  not_east u v h := fun he => hsnk u v h ((ofSet_east_iff C U v).mp he)

/-- The skew shape attached to $(\tau, C, U)$: its boxes are $(i(v), j(u))$ for the inversions
$(u, v)$ of $\tau$, where $j(n) = C + \#\{m \in [0, n) : m \in U\}$ and
$i(n) = C - \#\{m \in [0, n) : m \notin U\}$ (counted with sign when $n < 0$); it has
$\sigma = \tau$. -/
theorem ofSet_shape_σ {τ : AspPerm} {C : ℤ} {U : Set ℤ} (hsrc : ∀ u v, (u, v) ∈ inv_set τ → u ∈ U)
    (hsnk : ∀ u v, (u, v) ∈ inv_set τ → v ∉ U) (hχ : τ.χ = 0) :
    ((ofSet C U).shape τ (ofSet_compatible hsrc hsnk)).σ = τ :=
  shape_σ _ hχ

end LatticePath

open LatticePath

/-- The extended fringe box of content $n$ of a nonempty skew shape. -/
noncomputable def SkewShape.efBox (S : SkewShape) (hS : S.boxes.Nonempty) (n : ℤ) : ℤ × ℤ :=
  Classical.choose (S.exists_ext_fringe hS n)

lemma SkewShape.efBox_mem (hS : S.boxes.Nonempty) (n : ℤ) : S.efBox hS n ∈ S.ext_fringe :=
  (Classical.choose_spec (S.exists_ext_fringe hS n)).1

lemma SkewShape.Δ_efBox (hS : S.boxes.Nonempty) (n : ℤ) : Δ (S.efBox hS n) = n :=
  (Classical.choose_spec (S.exists_ext_fringe hS n)).2

lemma SkewShape.efBox_eq (hS : S.boxes.Nonempty) {x : ℤ × ℤ} (hx : x ∈ S.ext_fringe) :
    S.efBox hS (Δ x) = x :=
  S.ext_fringe_inj (S.efBox_mem hS _) hx (S.Δ_efBox hS _)

/-- The southeast boundary of a nonempty skew shape, as a lattice path: its $n$th vertex is the
extended fringe box of content $n$. -/
noncomputable def fringePath (S : SkewShape) (hS : S.boxes.Nonempty) : LatticePath where
  col n := (S.efBox hS n).2
  col_succ n := by
    -- Proof written by Claude Opus 5.5.
    have he := S.efBox_mem hS n
    have he' := S.efBox_mem hS (n + 1)
    have hΔ := S.Δ_efBox hS n
    have hΔ' := S.Δ_efBox hS (n + 1)
    rw [Δ_eq] at hΔ hΔ'
    have h1 : (S.efBox hS (n + 1)).1 ≤ (S.efBox hS n).1 := by
      by_contra! h
      exact he.2 (S.mem_down_closure_of_le he'.1
        (by simp only [Prod.le_def, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega))
    have h2 : (S.efBox hS n).1 - 1 ≤ (S.efBox hS (n + 1)).1 := by
      by_contra! h
      exact he'.2 (S.mem_down_closure_of_le he.1
        (by simp only [Prod.le_def, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; omega))
    omega

private lemma fringePath_row (hS : S.boxes.Nonempty) (n : ℤ) :
    (fringePath S hS).row n = (S.efBox hS n).1 := by
  have := S.Δ_efBox hS n
  rw [Δ_eq] at this
  simp only [row, fringePath]
  omega

private lemma fringePath_col_u (hS : S.boxes.Nonempty) (x : S) :
    (fringePath S hS).col (S.u x) = (S.U x).2 := by
  change (S.efBox hS (Δ (S.U x))).2 = _
  rw [S.efBox_eq hS (S.fringe_crit _ (S.U_fringe x))]

private lemma fringePath_row_v (hS : S.boxes.Nonempty) (x : S) :
    (fringePath S hS).row (S.v x) = (S.V x).1 := by
  rw [fringePath_row]
  change (S.efBox hS (Δ (S.V x))).1 = _
  rw [S.efBox_eq hS (S.fringe_crit _ (S.V_fringe x))]

/-- The boundary path of $S$ is compatible with $\sigma_S$. -/
lemma fringePath_compatible (hS : S.boxes.Nonempty) : (fringePath S hS).Compatible S.σ where
  -- Proof written by Claude Opus 5.5.
  east u v h := by
    rw [S.σ_invSet, S.mem_I] at h
    obtain ⟨x, rfl, -⟩ := h
    have hΔ : Δ (S.U x + (0,1)) = S.u x + 1 := Δ_add_snd _
    change (S.efBox hS (S.u x + 1)).2 = (S.efBox hS (Δ (S.U x))).2 + 1
    rw [← hΔ, S.efBox_eq hS (S.U_add_mem_ext_fringe x),
      S.efBox_eq hS (S.fringe_crit _ (S.U_fringe x)), Prod.snd_add]
  not_east u v h := by
    rw [S.σ_invSet, S.mem_I] at h
    obtain ⟨x, -, rfl⟩ := h
    have hΔ : Δ (S.V x - (1,0)) = S.v x + 1 := by
      simp only [SkewShape.v, Δ_eq, Prod.fst_sub, Prod.snd_sub]
      omega
    change (S.efBox hS (S.v x + 1)).2 ≠ (S.efBox hS (S.v x)).2 + 1
    rw [← hΔ, S.efBox_eq hS (S.V_sub_mem_ext_fringe x),
      show S.v x = Δ (S.V x) from rfl, S.efBox_eq hS (S.fringe_crit _ (S.V_fringe x))]
    simp only [Prod.snd_sub]
    omega

/-- The box attached to the pair of $x$ along the boundary path of $S$ is $x$ itself. -/
lemma fringePath_box_pair (hS : S.boxes.Nonempty) (x : S) :
    (fringePath S hS).box (S.u x, S.v x) = x := by
  rw [box, fringePath_row_v, fringePath_col_u, S.V_fst, S.U_snd]

/-- Every skew shape arises from its permutation by the construction above, using its boundary
path. -/
theorem exists_compatible_shape_eq (S : SkewShape) :
    ∃ (p : LatticePath) (hc : p.Compatible S.σ), p.shape S.σ hc = S := by
  -- Proof written by Claude Opus 5.5.
  rcases S.boxes.eq_empty_or_nonempty with hS | hS
  · have hI : inv_set S.σ = ∅ := by rw [S.σ_eq_id_of_boxes_eq_empty hS, AspPerm.inv_set_id]
    refine ⟨ofSet 0 ∅, ⟨fun u v h => by rw [hI] at h; exact h.elim,
      fun u v h => by rw [hI] at h; exact h.elim⟩, SetLike.coe_injective ?_⟩
    change (ofSet 0 ∅).box '' inv_set S.σ = S.boxes
    rw [hI, Set.image_empty, hS]
  · refine ⟨fringePath S hS, fringePath_compatible hS, SetLike.coe_injective (Set.ext fun y => ?_)⟩
    change y ∈ (fringePath S hS).box '' inv_set S.σ ↔ y ∈ S.boxes
    rw [S.σ_invSet]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      rw [fringePath_box_pair]
      exact x.prop
    · intro hy
      exact ⟨_, ⟨⟨y, hy⟩, rfl⟩, fringePath_box_pair hS ⟨y, hy⟩⟩

/-- Every skew shape $S$ is the shape attached to $(\sigma_S, C, U)$ for some $C$ and some $U$
containing every source and no sink of an inversion of $\sigma_S$. -/
theorem exists_ofSet_shape_eq (S : SkewShape) :
    ∃ (C : ℤ) (U : Set ℤ) (hc : (ofSet C U).Compatible S.σ), (ofSet C U).shape S.σ hc = S := by
  obtain ⟨p, hc, h⟩ := exists_compatible_shape_eq S
  revert hc h
  rw [p.eq_ofSet]
  exact fun hc h => ⟨_, _, hc, h⟩

end SkewShapes
