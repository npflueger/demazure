import Demazure.Avoiding321

namespace Tableaux
open ASP321a
section Link

def linked (A : Set (ℤ × ℤ)) (B : Set (ℤ × ℤ)) : Prop :=
  ∀ p ∈ A, ∀ q ∈ B, p ≼ q → p = q

structure Link where
  A : Set (ℤ × ℤ)
  B : Set (ℤ × ℤ)
  S : tfas
  χa : ℤ
  χb : ℤ
  union_eq : A ∪ B = S.I
  sep : linked A B

def link_of_sets {A B : Set (ℤ × ℤ)} (sep : linked A B) (tf : set_321a_prop (A ∪ B))
  (χa χb : ℤ) : Link :=
  ⟨A, B, ⟨⟨A ∪ B, tf.asp⟩, tf⟩, χa, χb, rfl, sep⟩

namespace Link
def chi (L : Link) : ℤ :=
  L.χa + L.χb

lemma B_subset (L : Link) : L.B ⊆ L.S.I := by
  rw [← L.union_eq]
  apply Set.subset_union_right

lemma A_subset (L : Link) : L.A ⊆ L.S.I := by
  rw [← L.union_eq]
  apply Set.subset_union_left

lemma mem_A_of_mem_inv_not_mem_B (L : Link) {p : ℤ × ℤ}
  (hpτ : p ∈ L.S.I) (hpB : p ∉ L.B) : p ∈ L.A := by
  rw [← L.union_eq] at hpτ
  rcases hpτ with (hpA | hpB')
  · exact hpA
  · exact (hpB hpB').elim

theorem ext {L₁ L₂ : Link}
    (hA : L₁.A = L₂.A) (hB : L₁.B = L₂.B)
    (hχa : L₁.χa = L₂.χa) (hχb : L₁.χb = L₂.χb) : L₁ = L₂ := by
  have hS : L₁.S = L₂.S := by
    cases hs1 : L₁.S with
    | mk S1 p1 =>
      cases hs2 : L₂.S with
      | mk S2 p2 =>
        have hI : S1.I = S2.I := by
          simpa [hs1, hs2] using (by
            rw [← L₁.union_eq, ← L₂.union_eq, hA, hB] : L₁.S.I = L₂.S.I)
        have hAsp : S1 = S2 := _root_.AspSet.ext hI
        rw [tfas.mk.injEq]
        simpa using hAsp
  cases L₁
  cases L₂
  cases hA
  cases hB
  cases hχa
  cases hχb
  simpa

lemma B_AspSet_prop (L : Link) :
  AspSet_prop L.B where
  directed := by
    intro u v huv
    exact L.S.directed u v (L.B_subset huv)
  closed := by
    intro u v w huv hvw
    exfalso
    have huvS : ⟨u, v⟩ ∈ L.S.I := L.B_subset huv
    have hvwS : ⟨v, w⟩ ∈ L.S.I := L.B_subset hvw
    rcases L.S.prop_321a.tfree u v w with (huv' | hvw')
    · exact huv' huvS
    · exact hvw' hvwS
  coclosed := by
    intro u v w u_lt_v v_lt_w huv hvw
    by_contra! huw

    have := L.S.coclosed u v w u_lt_v v_lt_w
    have h : ⟨u, v⟩ ∈ L.S.I ∨ ⟨v, w⟩ ∈ L.S.I := by
      by_contra! h'
      exact this h'.1 h'.2 (L.B_subset huw)
    rcases h with (h_uv | h_vw)
    · have huv' : ⟨u, v⟩ ∈ L.A := L.mem_A_of_mem_inv_not_mem_B h_uv huv
      have : ⟨u, v⟩ ≼ ⟨u, w⟩ := by
        constructor
        · exact le_refl u
        · exact le_of_lt v_lt_w
      have := L.sep ⟨u, v⟩ huv' ⟨u, w⟩ huw this
      have : v = w := by
        simpa
      rw [this] at v_lt_w
      exact lt_irrefl w v_lt_w
    · have hvw' : ⟨v, w⟩ ∈ L.A := L.mem_A_of_mem_inv_not_mem_B h_vw hvw
      have : ⟨v, w⟩ ≼ ⟨u, w⟩ := by
        constructor
        · exact le_of_lt u_lt_v
        · exact le_refl w
      have := L.sep ⟨v, w⟩ hvw' ⟨u, w⟩ huw this
      have : v = u := by
        simpa
      rw [this] at u_lt_v
      exact lt_irrefl u u_lt_v
  finite_outdegree := by
    intro u
    exact (L.S.finite_outdegree u).subset (by
      intro v hv
      exact L.B_subset hv)
  finite_indegree := by
    intro v
    exact (L.S.finite_indegree v).subset (by
      intro u hu
      exact L.B_subset hu)

lemma B_set_321a_prop (L : Link) : set_321a_prop L.B where
  asp := L.B_AspSet_prop
  tfree := by
    intro u v w
    rcases L.S.prop_321a.tfree u v w with (huv | hvw)
    · left
      intro huvB
      exact huv (L.B_subset huvB)
    · right
      intro hvwB
      exact hvw (L.B_subset hvwB)

def B_AspSet (L : Link) : AspSet :=
  ⟨L.B, L.B_AspSet_prop⟩

noncomputable def τ (L : Link) : AspPerm :=
  L.S.toAspPerm L.chi

@[simp]
lemma inv_set_τ (L : Link) : inv_set L.τ = L.S.I := by
  simpa [Link.τ] using (L.S.toAspSet.invSet_of_toAspPerm L.chi)

lemma is_321a_τ (L : Link) : is_321a L.τ := by
  rw [is_321a_iff_set_321a_prop L.τ L.τ.bijective]
  simpa [Link.τ] using set_321a_prop_of_func L.S L.chi

@[simp]
lemma chi_tau (L : Link) : L.τ.χ = L.chi := by
  simpa [Link.τ] using (L.S.toAspSet.chi_of_toAspPerm L.chi)

noncomputable def β (L : Link) : AspPerm :=
  L.B_AspSet.toAspPerm L.χb

@[simp]
lemma inv_set_β (L : Link) : inv_set L.β = L.B := by
  simpa [Link.β, Link.B_AspSet] using (L.B_AspSet.invSet_of_toAspPerm L.χb)

@[simp]
lemma chi_beta (L : Link) : L.β.χ = L.χb := by
  simpa [Link.β] using (L.B_AspSet.chi_of_toAspPerm L.χb)

lemma A_AspSet_prop (L : Link) :
  AspSet_prop (L.τ.rev_map '' L.A) := by
  let L' : Link := {
    A := L.τ.rev_map '' L.B
    B := L.τ.rev_map '' L.A
    S := tfas_of_perm (inv_is_321a (L.is_321a_τ))
    χa := -L.χb
    χb := -L.χa
    union_eq := by
      ext ⟨u, v⟩
      change ⟨u, v⟩ ∈ L.τ.rev_map '' L.B ∪ L.τ.rev_map '' L.A ↔
        ⟨u, v⟩ ∈ inv_set (((L.τ)⁻¹).func)
      constructor
      · intro h
        rcases h with (hB | hA)
        · rcases hB with ⟨⟨u', v'⟩, hu'v', hEq⟩
          simp [AspPerm.rev_map] at hEq
          rcases hEq with ⟨rfl, rfl⟩
          have hu'v'τ : ⟨u', v'⟩ ∈ inv_set L.τ := by
            simpa [L.inv_set_τ] using L.B_subset hu'v'
          exact (L.τ.inv_set_inverse u' v').mp hu'v'τ
        · rcases hA with ⟨⟨u', v'⟩, hu'v', hEq⟩
          simp [AspPerm.rev_map] at hEq
          rcases hEq with ⟨rfl, rfl⟩
          have hu'v'τ : ⟨u', v'⟩ ∈ inv_set L.τ := by
            simpa [L.inv_set_τ] using L.A_subset hu'v'
          exact (L.τ.inv_set_inverse u' v').mp hu'v'τ
      · intro h
        have h' : ⟨L.τ⁻¹ v, L.τ⁻¹ u⟩ ∈ inv_set L.τ := by
          have hτi :
              ⟨L.τ (L.τ⁻¹ u), L.τ (L.τ⁻¹ v)⟩ ∈ inv_set ((L.τ)⁻¹).func := by
            simpa using h
          have := (L.τ.inv_set_inverse (L.τ⁻¹ v) (L.τ⁻¹ u)).mpr hτi
          simpa using this
        have h'' : ⟨L.τ⁻¹ v, L.τ⁻¹ u⟩ ∈ L.S.I := by
          simpa [L.inv_set_τ] using h'
        rw [← L.union_eq] at h''
        rcases h'' with (hA | hB)
        · right
          refine ⟨⟨L.τ⁻¹ v, L.τ⁻¹ u⟩, hA, ?_⟩
          simp [AspPerm.rev_map]
        · left
          refine ⟨⟨L.τ⁻¹ v, L.τ⁻¹ u⟩, hB, ?_⟩
          simp [AspPerm.rev_map]
    sep := by
      intro p hp q hq hpq
      rcases hp with ⟨⟨u, v⟩, huv, rfl⟩
      rcases hq with ⟨⟨u', v'⟩, hu'v', rfl⟩
      simp [AspPerm.rev_map] at hpq
      have hpτi : ⟨L.τ v, L.τ u⟩ ∈ inv_set (((L.τ)⁻¹).func) := by
        have huvτ : ⟨u, v⟩ ∈ inv_set L.τ := by
          simpa [L.inv_set_τ] using L.B_subset huv
        exact (L.τ.inv_set_inverse u v).mp huvτ
      have hqτi : ⟨L.τ v', L.τ u'⟩ ∈ inv_set (((L.τ)⁻¹).func) := by
        have hu'v'τ : ⟨u', v'⟩ ∈ inv_set L.τ := by
          simpa [L.inv_set_τ] using L.A_subset hu'v'
        exact (L.τ.inv_set_inverse u' v').mp hu'v'τ
      have hqup : u ≤ u' := by
        have hu_snk : is_snk (L.τ⁻¹) (L.τ u) := snk_of_inv hpτi
        simpa using snk_le (inv_is_321a (L.is_321a_τ)) hu_snk hpq.2
      have hvpv : v' ≤ v := by
        have hv_src : is_src (L.τ⁻¹) (L.τ v) := src_of_inv hpτi
        simpa using src_ge (inv_is_321a (L.is_321a_τ)) hv_src hpq.1
      have hqp : ⟨u', v'⟩ ≼ ⟨u, v⟩ := by
        exact ⟨hqup, hvpv⟩
      have hEq : (u', v') = (u, v) := L.sep (u', v') hu'v' (u, v) huv hqp
      simpa [AspPerm.rev_map] using congrArg L.τ.rev_map hEq.symm
    }
  have h' := B_AspSet_prop L'
  simpa [L'] using h'

def A_AspSet (L : Link) : AspSet :=
  ⟨L.τ.rev_map '' L.A, A_AspSet_prop L⟩

noncomputable def α (L : Link) : AspPerm :=
  (L.A_AspSet.toAspPerm (-L.χa))⁻¹

@[simp]
lemma inv_set_α (L : Link) : L.A = L.τ.sr L.α '' inv_set L.α := by
  have hAinv : inv_set (((Link.α L)⁻¹).func) = L.τ.rev_map '' L.A := by
    simpa [Link.α, Link.A_AspSet] using (L.A_AspSet.invSet_of_toAspPerm (-L.χa))
  ext ⟨u, v⟩
  constructor
  · intro huv
    apply (L.τ.sr_crit L.α u v).mpr
    rw [hAinv]
    exact ⟨⟨u, v⟩, huv, by simp [AspPerm.rev_map]⟩
  · intro huv
    have hrev : ⟨L.τ v, L.τ u⟩ ∈ L.τ.rev_map '' L.A := by
      rw [← hAinv]
      exact (L.τ.sr_crit L.α u v).mp huv
    rcases hrev with ⟨⟨u', v'⟩, hu'v', hEq⟩
    simp [AspPerm.rev_map] at hEq
    rcases hEq with ⟨hv, hu⟩
    apply L.τ.injective at hv
    apply L.τ.injective at hu
    simpa [hu, hv] using hu'v'

@[simp]
lemma chi_alpha (L : Link) : L.α.χ = L.χa := by
  rw [Link.α, AspPerm.chi_dual]
  have hχ := L.A_AspSet.chi_of_toAspPerm (-L.χa)
  linarith

lemma dprod (L : Link) : L.α ⋆ L.β = L.τ := by
  have hτ : L.τ = L.α ⋆ L.β := by
    apply (dprod_eq_iff (τ := L.τ) (α := L.α) (β := L.β) (L.is_321a_τ)).mpr
    constructor
    · rw [L.chi_alpha, L.chi_beta, L.chi_tau, Link.chi]
    constructor
    · simpa [L.inv_set_τ, L.inv_set_α, L.inv_set_β] using L.union_eq.symm
    · intro p hp q hq hpq
      have hp' : p ∈ L.A ∩ L.B := by
        simpa [L.inv_set_α, L.inv_set_β] using hp
      have hq' : q ∈ L.A ∩ L.B := by
        simpa [L.inv_set_α, L.inv_set_β] using hq
      exact L.sep p hp'.1 q hq'.2 hpq
  exact hτ.symm

end Link

variable {τ : AspPerm} (h_321a : is_321a τ)
include h_321a

noncomputable def Link_of_dprod {α β : AspPerm}
  (dprod : α ⋆ β = τ) : Link where
  A := (τ.sr α) '' inv_set α
  B := inv_set β
  S := tfas_of_perm h_321a
  χa := α.χ
  χb := β.χ
  union_eq := by
    have hboxes := ((dprod_eq_iff (τ := τ) (α := α) (β := β) h_321a).mp dprod.symm).2
    exact hboxes.1.symm
  sep := by
    intro p hp q hq hpq
    have h_L : β ≤L τ := by
      rw [← dprod]
      exact Submodular.lel_of_dprod α β
    have h_R : α ≤R τ := by
      rw [← dprod]
      exact Submodular.ler_of_dprod α β
    have hp' : p ∈ inv_set β := by
      exact (inv_of_lel_iff (τ := τ) (β := β) h_321a h_L hq hpq).mpr
        ((AspPerm.sr_subset τ α h_R) hp)
    have hq' : q ∈ (τ.sr α) '' (inv_set α) := by
      exact (sr_inv_of_ler_iff (τ := τ) h_321a h_R hp hpq).mpr (h_L hq)
    have hboxes := ((dprod_eq_iff (τ := τ) (α := α) (β := β) h_321a).mp dprod.symm).2
    exact hboxes.2 p ⟨hp, hp'⟩ q ⟨hq', hq⟩ hpq

lemma rev_A_eq_inv_inv_of_Link_of_dprod {α β : AspPerm} (dprod : α ⋆ β = τ) :
  τ.rev_map '' (Link_of_dprod h_321a dprod).A = inv_set α⁻¹.func := by
  ext ⟨u, v⟩
  change
    ⟨u, v⟩ ∈ τ.rev_map '' (τ.sr α '' inv_set α.func) ↔
      ⟨u, v⟩ ∈ inv_set α⁻¹.func
  constructor
  · intro h
    rcases h with ⟨⟨u', v'⟩, hu'v', hEq⟩
    have hα : ⟨τ v', τ u'⟩ ∈ inv_set α⁻¹.func := (τ.sr_crit α u' v').mp hu'v'
    simp [AspPerm.rev_map] at hEq
    rcases hEq with ⟨hv, hu⟩
    simpa [hv, hu] using hα
  · intro huv
    have hsr : ⟨τ⁻¹ v, τ⁻¹ u⟩ ∈ τ.sr α '' inv_set α := by
      apply (τ.sr_crit α (τ⁻¹ v) (τ⁻¹ u)).mpr
      simpa using huv
    refine ⟨⟨τ⁻¹ v, τ⁻¹ u⟩, hsr, ?_⟩
    simp [AspPerm.rev_map]

noncomputable def link_equiv_dprod :
  {L : Link | L.τ = τ } ≃ {⟨α, β⟩ : AspPerm × AspPerm | α ⋆ β = τ } where
  toFun L := ⟨⟨L.val.α, L.val.β⟩, by simp; rw [L.val.dprod, L.prop]⟩
  invFun x := ⟨Link_of_dprod h_321a x.property, by
    rcases x with ⟨⟨α, β⟩, h_dprod⟩
    change α ⋆ β = τ at h_dprod
    apply AspPerm.eq_of_inv_set_eq_of_chi_eq
    · change inv_set ((tfas_of_perm h_321a).toAspPerm (α.χ + β.χ)) = inv_set τ
      simpa [Link.τ, Link.chi, Link_of_dprod] using
        (AspSet.of_AspPerm τ).invSet_of_toAspPerm (α.χ + β.χ)
    · change ((tfas_of_perm h_321a).toAspPerm (α.χ + β.χ)).χ = τ.χ
      have hχ' : ((tfas_of_perm h_321a).toAspPerm (α.χ + β.χ)).χ = α.χ + β.χ := by
        simpa using (AspSet.of_AspPerm τ).chi_of_toAspPerm (α.χ + β.χ)
      rw [hχ']
      rw [← h_dprod]
      exact (AspPerm.chi_star α β).symm⟩
  left_inv L := by
    have hdp : L.val.α ⋆ L.val.β = τ := by
      rw [L.val.dprod, L.prop]
    apply Subtype.ext
    apply Link.ext
    · dsimp [Link_of_dprod]
      have hsr : τ.sr L.val.α '' inv_set L.val.α = L.val.τ.sr L.val.α '' inv_set L.val.α := by
        simpa using congrArg (fun t => t.sr L.val.α '' inv_set L.val.α) L.prop.symm
      exact hsr.trans L.val.inv_set_α.symm
    · change inv_set L.val.β = L.val.B
      exact L.val.inv_set_β
    · change L.val.α.χ = L.val.χa
      exact L.val.chi_alpha
    · change L.val.β.χ = L.val.χb
      exact L.val.chi_beta
  right_inv x := by
    rcases x with ⟨⟨α, β⟩, h_dprod⟩
    change α ⋆ β = τ at h_dprod
    have hτL : (Link_of_dprod h_321a h_dprod).τ = τ := by
      apply AspPerm.eq_of_inv_set_eq_of_chi_eq
      · change inv_set ((tfas_of_perm h_321a).toAspPerm (α.χ + β.χ)) = inv_set τ
        simpa [Link.τ, Link.chi, Link_of_dprod] using
          (AspSet.of_AspPerm τ).invSet_of_toAspPerm (α.χ + β.χ)
      · change ((tfas_of_perm h_321a).toAspPerm (α.χ + β.χ)).χ = τ.χ
        have hχ' : ((tfas_of_perm h_321a).toAspPerm (α.χ + β.χ)).χ = α.χ + β.χ := by
          simpa using (AspSet.of_AspPerm τ).chi_of_toAspPerm (α.χ + β.χ)
        rw [hχ']
        rw [← h_dprod]
        exact (AspPerm.chi_star α β).symm
    apply Subtype.ext
    apply Prod.ext
    · dsimp
      let asps := (Link_of_dprod h_321a h_dprod).A_AspSet
      suffices asps.toAspPerm (-(Link_of_dprod h_321a h_dprod).χa) = α⁻¹ by
        calc
          (Link_of_dprod h_321a h_dprod).α
              = (asps.toAspPerm (-(Link_of_dprod h_321a h_dprod).χa))⁻¹ := by
                  rfl
          _ = (α⁻¹)⁻¹ := by rw [this]
          _ = α := by simp
      apply AspPerm.eq_of_inv_set_eq_of_chi_eq
      · rw [AspSet.invSet_of_toAspPerm]
        subst asps
        simpa [Link.A_AspSet, hτL] using
          rev_A_eq_inv_inv_of_Link_of_dprod (τ := τ) h_321a h_dprod
      · rw [AspSet.chi_of_toAspPerm]
        simp [Link_of_dprod, AspPerm.chi_dual]
    · dsimp
      let asps := (Link_of_dprod h_321a h_dprod).B_AspSet
      suffices asps.toAspPerm (Link_of_dprod h_321a h_dprod).χb = β by
        calc
          (Link_of_dprod h_321a h_dprod).β
              = asps.toAspPerm (Link_of_dprod h_321a h_dprod).χb := by
                  rfl
          _ = β := this
      apply AspPerm.eq_of_inv_set_eq_of_chi_eq
      · rw [AspSet.invSet_of_toAspPerm]
        subst asps
        change inv_set β.func = inv_set β.func
        rfl
      · rw [AspSet.chi_of_toAspPerm]
        simp [Link_of_dprod]

end Link

section Chains
variable {τ : AspPerm} (h_321a : is_321a τ)

noncomputable abbrev DProd (L : List AspPerm) : AspPerm :=
  List.foldr AspPerm.star AspPerm.id L

lemma DProd_cons (α : AspPerm) (Q : List AspPerm) :
  DProd (α :: Q) = α ⋆ DProd Q := by
  unfold DProd
  rw [List.foldr_cons]

def HeckeFactorization (τ : AspPerm) : Type :=
  {P : List AspPerm //
    DProd P = τ}

def boxUnion : List (Set (ℤ × ℤ) × ℤ) → Set (ℤ × ℤ)
  | [] => ∅
  | head :: tail => head.1 ∪ boxUnion tail

def chiSum : List (Set (ℤ × ℤ) × ℤ) → ℤ
  | [] => 0
  | head :: tail => head.2 + chiSum tail

def isChain : List (Set (ℤ × ℤ) × ℤ) → Prop
  | [] => True
  | ⟨A,_⟩ :: Q =>
      linked A (boxUnion Q)
      ∧ isChain Q

/-- Chain matching a given permutation τ in box union and shift. -/
def PChain (τ : AspPerm) : Type :=
  {C : List (Set (ℤ × ℤ) × ℤ) // isChain C ∧ boxUnion C = inv_set τ ∧ chiSum C = τ.χ}

noncomputable def LSet_of_LPerm : List AspPerm → List (Set (ℤ × ℤ) × ℤ)
  | [] => []
  | α :: L =>
    ((DProd (α :: L)).sr α '' (inv_set α), α.χ) :: LSet_of_LPerm L

lemma LSet_cons (α : AspPerm) (L : List AspPerm) :
    LSet_of_LPerm (α :: L) =
      ((DProd (α :: L)).sr α '' inv_set α, α.χ) :: LSet_of_LPerm L := by
  rfl

include h_321a

lemma LSet_chiSum (A : HeckeFactorization τ) :
  chiSum (LSet_of_LPerm A.val) = τ.χ := by
  rcases A with ⟨AL, dprodA⟩
  induction AL generalizing τ with
  | nil =>
      simp [LSet_of_LPerm, chiSum, ← dprodA]
  | cons α L ih =>
      let β := DProd L
      have h_L : β ≤L τ := by
        rw [← dprodA, DProd_cons]
        exact Submodular.lel_of_dprod α β
      have h_321a_β : is_321a β := is_321a_of_lel h_321a h_L
      have ih' := ih h_321a_β (by rfl)
      have τ_eq : α ⋆ β = τ := by
        rw [← dprodA, ← DProd_cons]
      have h_χ : τ.χ = α.χ + β.χ := by
        rw [← dprodA]
        exact (AspPerm.chi_star α β)
      rw [LSet_cons, chiSum, ih']
      linarith

lemma LSet_boxUnion (A : HeckeFactorization τ) :
  boxUnion (LSet_of_LPerm A.val) = inv_set τ := by
  rcases A with ⟨AL, dprodA⟩
  induction AL generalizing τ with
  | nil =>
      simp [LSet_of_LPerm, boxUnion, ← dprodA]
  | cons α L ih =>
      let β := DProd L
      have h_L : β ≤L τ := by
        rw [← dprodA, DProd_cons]
        exact Submodular.lel_of_dprod α β
      have h_R : α ≤R τ := by
        rw [← dprodA, DProd_cons]
        exact Submodular.ler_of_dprod α β
      have h_321a_β : is_321a β := is_321a_of_lel h_321a h_L
      have ih' := ih h_321a_β (by rfl)
      have τ_eq : α ⋆ β = τ := by
        rw [← dprodA, ← DProd_cons]
      have h_R : α ≤R τ := by
        rw [← dprodA]
        exact Submodular.ler_of_dprod α β
      have h_χ : τ.χ = α.χ + β.χ := by
        rw [← dprodA]
        exact (AspPerm.chi_star α β)
      rw [LSet_cons, boxUnion, ih']
      have := ((ASP321a.dprod_eq_iff h_321a).mp τ_eq.symm).2.1.symm
      convert this

lemma LSet_isChain (A : HeckeFactorization τ) :
  isChain (LSet_of_LPerm A.val) := by
  rcases A with ⟨AL, dprodA⟩
  induction AL generalizing τ with
  | nil =>
      simp [LSet_of_LPerm, isChain]
  | cons α L ih =>
      let β := DProd L
      have h_L : β ≤L τ := by
        rw [← dprodA, DProd_cons]
        exact Submodular.lel_of_dprod α β
      have h_R : α ≤R τ := by
        rw [← dprodA, DProd_cons]
        exact Submodular.ler_of_dprod α β
      have h_321a_β : is_321a β := is_321a_of_lel h_321a h_L
      have ih' := ih h_321a_β (by rfl)
      have τ_eq : α ⋆ β = τ := by
        rw [← dprodA, ← DProd_cons]
      rw [LSet_cons]
      constructor
      · rw [LSet_boxUnion h_321a_β ⟨L, rfl⟩]
        unfold linked
        rw [dprodA]
        intro p hp q hq hpq
        refine ((ASP321a.dprod_eq_iff h_321a).mp τ_eq.symm).2.2 p ?_ q ?_ hpq
        · suffices p ∈ inv_set β by
            exact ⟨hp, this⟩
          exact (inv_of_lel_iff (τ := τ) (β := β) h_321a h_L hq hpq).mpr
            ((AspPerm.sr_subset τ α h_R) hp)
        · suffices q ∈ τ.sr α '' inv_set α by
            exact ⟨this, hq⟩
          exact (sr_inv_of_ler_iff (τ := τ) h_321a h_R hp hpq).mpr (h_L hq)
      · exact ih'

noncomputable def PChain_of_HF (A : HeckeFactorization τ) : PChain τ :=
  ⟨LSet_of_LPerm A.val, LSet_isChain h_321a A, LSet_boxUnion h_321a A, LSet_chiSum h_321a A⟩

omit h_321a in
noncomputable def LPerm_of_Chain :
  (C : List (Set (ℤ × ℤ) × ℤ)) → isChain C → set_321a_prop (boxUnion C) → List AspPerm
  | [], _, _ => []
  | ⟨A, χ⟩ :: Q, hC, htfas =>
    let L := link_of_sets hC.1 htfas χ (chiSum Q)
    L.α :: LPerm_of_Chain Q hC.2 (by
      simpa [L] using L.B_set_321a_prop)

omit h_321a in
theorem DProd_LPerm_of_Chain :
    (C : List (Set (ℤ × ℤ) × ℤ)) → (hC : isChain C) →
      (htfas : set_321a_prop (boxUnion C)) →
        DProd (LPerm_of_Chain C hC htfas) =
          ((⟨boxUnion C, htfas.asp⟩ : AspSet).toAspPerm (chiSum C))
  | [], _, htfas => by
      let asps : AspSet := ⟨∅, htfas.asp⟩
      apply AspPerm.eq_of_inv_set_eq_of_chi_eq
      · simpa [asps, LPerm_of_Chain, DProd, boxUnion] using (asps.invSet_of_toAspPerm 0).symm
      · simpa [asps, LPerm_of_Chain, DProd, chiSum] using (asps.chi_of_toAspPerm 0).symm
  | ⟨A, χ⟩ :: Q, hC, htfas => by
      let L := link_of_sets hC.1 htfas χ (chiSum Q)
      have htfasQ : set_321a_prop (boxUnion Q) := by
        simpa [L] using L.B_set_321a_prop
      have ih := DProd_LPerm_of_Chain Q hC.2 htfasQ
      rw [LPerm_of_Chain, DProd_cons, ih]
      simpa [L] using L.dprod

noncomputable def HF_of_PChain (C : PChain τ) : HeckeFactorization τ := by
  have tfas : set_321a_prop (boxUnion C.val) := by
    simp only [C.prop.2]
    exact (is_321a_iff_set_321a_prop τ.func τ.bijective).mp h_321a
  refine ⟨LPerm_of_Chain C.val C.prop.1 tfas, ?_⟩
  let asps : AspSet := ⟨boxUnion C.val, tfas.asp⟩
  have h_asps : asps.toAspPerm (chiSum C.val) = τ := by
    apply AspPerm.eq_of_inv_set_eq_of_chi_eq
    · simpa [asps, C.prop.2.1] using (asps.invSet_of_toAspPerm (chiSum C.val))
    · simpa [asps, C.prop.2.2] using (asps.chi_of_toAspPerm (chiSum C.val))
  exact (DProd_LPerm_of_Chain C.val C.prop.1 tfas).trans h_asps

omit h_321a in
lemma LSet_of_LPerm_of_Chain :
  ∀ (C : List (Set (ℤ × ℤ) × ℤ)) (hC : isChain C) (htfas : set_321a_prop (boxUnion C)),
    LSet_of_LPerm (LPerm_of_Chain C hC htfas) = C
  | [], _, _ => by
      simp [LPerm_of_Chain, LSet_of_LPerm]
  | ⟨A, χ⟩ :: Q, hC, htfas => by
      let L := link_of_sets hC.1 htfas χ (chiSum Q)
      have htfasQ : set_321a_prop (boxUnion Q) := by
        simpa [L] using L.B_set_321a_prop
      have ih := LSet_of_LPerm_of_Chain Q hC.2 htfasQ
      have hβ : DProd (LPerm_of_Chain Q hC.2 htfasQ) = L.β := by
        simpa [L] using DProd_LPerm_of_Chain Q hC.2 htfasQ
      have hτ : DProd (L.α :: LPerm_of_Chain Q hC.2 htfasQ) = L.τ := by
        simpa [DProd_cons, hβ] using L.dprod
      have hA : (DProd (L.α :: LPerm_of_Chain Q hC.2 htfasQ)).sr L.α '' inv_set L.α = A := by
        have hsr :
            (DProd (L.α :: LPerm_of_Chain Q hC.2 htfasQ)).sr L.α '' inv_set L.α
              = L.τ.sr L.α '' inv_set L.α := by
          simpa using congrArg (fun t => t.sr L.α '' inv_set L.α) hτ
        calc
          (DProd (L.α :: LPerm_of_Chain Q hC.2 htfasQ)).sr L.α '' inv_set L.α
              = L.τ.sr L.α '' inv_set L.α := hsr
          _ = L.A := L.inv_set_α.symm
          _ = A := by rfl
      rw [LPerm_of_Chain, LSet_of_LPerm]
      simp [ih]
      constructor
      · exact hA
      · rfl

lemma PChain_of_HF_of_PChain (C : PChain τ) :
  PChain_of_HF h_321a (HF_of_PChain h_321a C) = C := by
  have tfas : set_321a_prop (boxUnion C.val) := by
    simp only [C.prop.2]
    exact (is_321a_iff_set_321a_prop τ.func τ.bijective).mp h_321a
  apply Subtype.ext
  simpa [PChain_of_HF, HF_of_PChain] using
    (LSet_of_LPerm_of_Chain C.val C.prop.1 tfas)

lemma HF_of_PChain_of_HF (A : HeckeFactorization τ) :
  HF_of_PChain h_321a (PChain_of_HF h_321a A) = A := by
  rcases A with ⟨AL, dprodA⟩
  induction AL generalizing τ with
  | nil =>
      apply Subtype.ext
      rfl
  | cons α T ih =>
      let β := DProd T
      have h_L : β ≤L τ := by
        rw [← dprodA, DProd_cons]
        exact Submodular.lel_of_dprod α β
      have h_321a_β : is_321a β := is_321a_of_lel h_321a h_L
      have τ_eq : α ⋆ β = τ := by
        rw [← dprodA, DProd_cons]
      have ih' := ih h_321a_β (by rfl)
      apply Subtype.ext
      have htfas : set_321a_prop (boxUnion (LSet_of_LPerm (α :: T))) := by
        rw [LSet_boxUnion h_321a ⟨α :: T, dprodA⟩]
        exact (is_321a_iff_set_321a_prop τ.func τ.bijective).mp h_321a
      change
        LPerm_of_Chain (LSet_of_LPerm (α :: T)) (LSet_isChain h_321a ⟨α :: T, dprodA⟩) htfas
          = α :: T
      simp only [LSet_cons, LPerm_of_Chain]
      let Lnk : Link := link_of_sets
        (A := (DProd (α :: T)).sr α '' inv_set α)
        (B := boxUnion (LSet_of_LPerm T))
        (LSet_isChain h_321a ⟨α :: T, dprodA⟩).1
        htfas α.χ (chiSum (LSet_of_LPerm T))
      have htfasT :
          set_321a_prop (boxUnion (LSet_of_LPerm T)) := by
        simpa [Lnk] using Lnk.B_set_321a_prop
      have hTail :
          LPerm_of_Chain (LSet_of_LPerm T)
            (LSet_isChain h_321a ⟨α :: T, dprodA⟩).2
            htfasT = T := by
        simpa [PChain_of_HF, HF_of_PChain] using congrArg Subtype.val ih'
      have hLink : Lnk = Link_of_dprod h_321a τ_eq := by
        have hA : Lnk.A = (Link_of_dprod h_321a τ_eq).A := by
          change (DProd (α :: T)).sr α '' inv_set α = τ.sr α '' inv_set α
          simp [dprodA]
        have hB : Lnk.B = (Link_of_dprod h_321a τ_eq).B := by
          change boxUnion (LSet_of_LPerm T) = inv_set β
          simpa [Lnk, Link_of_dprod] using (LSet_boxUnion h_321a_β ⟨T, rfl⟩)
        have hχa : Lnk.χa = (Link_of_dprod h_321a τ_eq).χa := by
          rfl
        have hχb : Lnk.χb = (Link_of_dprod h_321a τ_eq).χb := by
          change chiSum (LSet_of_LPerm T) = β.χ
          simpa [Lnk, Link_of_dprod] using (LSet_chiSum h_321a_β ⟨T, rfl⟩)
        exact Link.ext hA hB hχa hχb
      let e := link_equiv_dprod (τ := τ) h_321a
      let x : {⟨α', β'⟩ : AspPerm × AspPerm | α' ⋆ β' = τ } := ⟨⟨α, β⟩, τ_eq⟩
      have hα₀ : (Link_of_dprod h_321a τ_eq).α = α := by
        simpa [e, x] using congrArg Prod.fst (congrArg Subtype.val (e.right_inv x))
      have hα : Lnk.α = α := by
        rw [hLink]
        exact hα₀
      calc
        Lnk.α :: LPerm_of_Chain (LSet_of_LPerm T)
            (LSet_isChain h_321a ⟨α :: T, dprodA⟩).2 htfasT
          = α :: LPerm_of_Chain (LSet_of_LPerm T)
              (LSet_isChain h_321a ⟨α :: T, dprodA⟩).2 htfasT := by
                simpa using congrArg (fun γ => γ :: LPerm_of_Chain (LSet_of_LPerm T)
                  (LSet_isChain h_321a ⟨α :: T, dprodA⟩).2 htfasT) hα
        _ = α :: T := by simp [hTail]

noncomputable def HF_equiv_PChain :
  HeckeFactorization τ ≃ PChain τ
  where
  toFun := PChain_of_HF h_321a
  invFun := HF_of_PChain h_321a
  left_inv A := by
    exact HF_of_PChain_of_HF h_321a A
  right_inv C := by
    exact PChain_of_HF_of_PChain h_321a C

end Chains

section SetValuedTableaux

/-- A set-valued tableau on `inv_set τ` with symbols `1, ..., n`, encoded as
`Fin n` labels. The order convention is chosen to match `IsLayering`: if
`p ≼ q` and `p ≠ q`, then every label in `q` is at most every label in `p`. -/
structure SetValuedTableau_prop {τ : AspPerm} {n : ℕ}
    (T : ↥(inv_set τ) → Finset (Fin n)) : Prop where
  nonempty : ∀ p, (T p).Nonempty
  weak :
    ∀ {p q : ↥(inv_set τ)} {i j : Fin n},
      i ∈ T p → j ∈ T q → p.val ≼ q.val → p ≠ q → j ≤ i

/-- A set-valued tableau on `inv_set τ` with symbols `1, ..., n`. -/
def SetValuedTableau (τ : AspPerm) (n : ℕ) : Type :=
  {T : ↥(inv_set τ) → Finset (Fin n) // SetValuedTableau_prop (τ := τ) T}

/-- A length-`n` chain of box sets, where the `i`th set records the boxes
carrying symbol `i + 1`. Earlier labels are separated from later labels in the
same way as in `IsLayering`. -/
structure LabelChain_prop {τ : AspPerm} {n : ℕ}
    (C : Fin n → Set (ℤ × ℤ)) : Prop where
  cover : ∀ p, p ∈ inv_set τ ↔ ∃ i, p ∈ C i
  sep :
    ∀ {i j : Fin n}, i < j → ∀ p ∈ C i, ∀ q ∈ C j, p ≼ q → p = q

/-- A fixed-length chain of subsets of `inv_set τ`, indexed by the symbols
`1, ..., n`. -/
def LabelChain (τ : AspPerm) (n : ℕ) : Type :=
  {C : Fin n → Set (ℤ × ℤ) // LabelChain_prop (τ := τ) C}

variable {τ : AspPerm} {n : ℕ}

/-- Convert a tableau to the corresponding family of label sets. -/
def labelChainOfTableau (T : SetValuedTableau τ n) : LabelChain τ n := by
  refine ⟨fun i p => ∃ hp : p ∈ inv_set τ, i ∈ T.1 ⟨p, hp⟩, ?_⟩
  refine ⟨?_, ?_⟩
  · intro p
    constructor
    · intro hp
      rcases T.2.nonempty ⟨p, hp⟩ with ⟨i, hi⟩
      exact ⟨i, hp, hi⟩
    · rintro ⟨i, hp⟩
      exact hp.1
  · intro i j hij p hp q hq hpq
    by_cases hEq : p = q
    · exact hEq
    · rcases hp with ⟨hpτ, hip⟩
      rcases hq with ⟨hqτ, hjq⟩
      have hneq : (⟨p, hpτ⟩ : ↥(inv_set τ)) ≠ ⟨q, hqτ⟩ := by
        intro h
        apply hEq
        exact congrArg Subtype.val h
      exfalso
      exact (not_le_of_gt hij) (T.2.weak hip hjq hpq hneq)

/-- Convert a fixed-length chain of label sets to the corresponding tableau. -/
noncomputable def tableauOfLabelChain (C : LabelChain τ n) :
    SetValuedTableau τ n := by
  classical
  refine ⟨fun p => Finset.univ.filter fun i => p.1 ∈ C.1 i, ?_⟩
  refine ⟨?_, ?_⟩
  · intro p
    rcases (C.2.cover p.1).mp p.2 with ⟨i, hi⟩
    exact ⟨i, by simp [hi]⟩
  · intro p q i j hi hj hpq hneq
    have hpC : p.1 ∈ C.1 i := by simpa using hi
    have hqC : q.1 ∈ C.1 j := by simpa using hj
    by_cases hlt : i < j
    · have hpq_eq : p.1 = q.1 := C.2.sep hlt p.1 hpC q.1 hqC hpq
      exfalso
      apply hneq
      apply Subtype.ext
      exact hpq_eq
    · exact le_of_not_gt hlt

lemma mem_labelChainOfTableau_iff (T : SetValuedTableau τ n)
    (p : ↥(inv_set τ)) (i : Fin n) :
    p.1 ∈ (labelChainOfTableau T).1 i ↔ i ∈ T.1 p := by
  constructor
  · rintro ⟨hp, hi⟩
    have hp_eq : (⟨p.1, hp⟩ : ↥(inv_set τ)) = p := by
      apply Subtype.ext
      rfl
    simpa [hp_eq] using hi
  · intro hi
    exact ⟨p.2, hi⟩

lemma mem_labelChainOfTableau_tableauOfLabelChain_iff (C : LabelChain τ n)
    (p : ℤ × ℤ) (i : Fin n) :
    p ∈ (labelChainOfTableau (tableauOfLabelChain C)).1 i ↔ p ∈ C.1 i := by
  constructor
  · rintro ⟨hp, hi⟩
    simpa [tableauOfLabelChain] using hi
  · intro hp
    have hpτ : p ∈ inv_set τ := (C.2.cover p).mpr ⟨i, hp⟩
    exact ⟨hpτ, by simp [tableauOfLabelChain, hp]⟩

/-- The tableau reconstructed from the label-chain of `T` is `T` itself. -/
lemma tableauOfLabelChain_labelChainOfTableau (T : SetValuedTableau τ n) :
    tableauOfLabelChain (labelChainOfTableau T) = T := by
  exact Subtype.ext (by
    funext p
    apply Finset.ext
    intro i
    calc
      i ∈ (tableauOfLabelChain (labelChainOfTableau T)).1 p
        ↔ p.1 ∈ (labelChainOfTableau T).1 i := by
            simp [tableauOfLabelChain]
      _ ↔ i ∈ T.1 p := mem_labelChainOfTableau_iff T p i)

/-- The label-chain reconstructed from the tableau of `C` is `C` itself. -/
lemma labelChainOfTableau_tableauOfLabelChain (C : LabelChain τ n) :
    labelChainOfTableau (tableauOfLabelChain C) = C := by
  exact Subtype.ext (by
    funext i
    ext p
    exact mem_labelChainOfTableau_tableauOfLabelChain_iff C p i)

/-- Fixed-length label-chains and set-valued tableaux are equivalent. -/
noncomputable def setValuedTableauEquivLabelChain (τ : AspPerm) (n : ℕ) :
    SetValuedTableau τ n ≃ LabelChain τ n where
  toFun := labelChainOfTableau
  invFun := tableauOfLabelChain
  left_inv := tableauOfLabelChain_labelChainOfTableau
  right_inv := labelChainOfTableau_tableauOfLabelChain

end SetValuedTableaux
end Tableaux
