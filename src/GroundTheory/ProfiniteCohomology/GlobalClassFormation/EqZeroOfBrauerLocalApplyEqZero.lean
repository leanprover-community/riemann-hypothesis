import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.Sequence
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.NormalFixingSubgroupGaloisClosure
import GroundTheory.ProfiniteCohomology.GaloisModules.Discrete
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.LevelsColimit
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
import GroundTheory.GlobalFields.SecondInequality.Cyclic
import GroundTheory.TateCohomology.Herbrand
import GroundTheory.ProfiniteCohomology.LocalClassFormation.OrderInfRes
import GroundTheory.GlobalFields.IdeleClassGroup.IdeleClassEquivIdeleClassMapOfComm
import GroundTheory.TateCohomology.TateResEqZeroOfNsmulEqZero
import GroundTheory.TateCohomology.ResCoresPos
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalInvariants

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

universe u

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

abbrev unitsRep : Rep ℤ (ℚ̄ ≃ₐ[ℚ] ℚ̄) := galUnitsZ ℚ ℚ̄

abbrev classRep : Rep ℤ (ℚ̄ ≃ₐ[ℚ] ℚ̄) := Rep.ofMulDistribMulAction (ℚ̄ ≃ₐ[ℚ] ℚ̄) IdeleClassLimit

instance isDiscreteRep_classRep : IsDiscreteRep classRep := by
  refine (isDiscreteRep_iff classRep).2 fun z => ?_
  obtain ⟨F, c, rfl⟩ := IdeleClassLimit.exists_of (Additive.toMul z)
  have : FiniteDimensional ℚ F.1 := F.2
  refine Subgroup.isOpen_mono (H₁ := F.1.fixingSubgroup) (fun σ hσ ↦ ?_) F.1.fixingSubgroup_isOpen
  exact congrArg Additive.ofMul (IdeleClassLimit.smul_of_eq_of_mem_fixingSubgroup hσ c)

def diagMor : unitsRep ⟶ IdeleLimit.rep :=
  Rep.ofHom ⟨(MonoidHom.toAdditive IdeleLimit.diag).toIntLinearMap, fun σ => LinearMap.ext fun x =>
    congrArg Additive.ofMul (IdeleLimit.diag_map σ x.toMul)⟩

@[simp]
theorem diagMor_hom_apply (x : Additive ℚ̄ˣ) :
    diagMor.hom x = Additive.ofMul (IdeleLimit.diag x.toMul) :=
  rfl

def toClassMor : IdeleLimit.rep ⟶ classRep :=
  Rep.ofHom ⟨(MonoidHom.toAdditive IdeleLimit.toClassLimit).toIntLinearMap, fun σ => LinearMap.ext
    fun x => congrArg Additive.ofMul (IdeleLimit.toClassLimit_smul σ x.toMul)⟩

@[simp]
theorem toClassMor_hom_apply (x : Additive IdeleLimit) :
    toClassMor.hom x = Additive.ofMul (IdeleLimit.toClassLimit x.toMul) :=
  rfl

def idelesShortComplex : ShortComplex (Rep ℤ (ℚ̄ ≃ₐ[ℚ] ℚ̄)) :=
  ShortComplex.mk diagMor toClassMor (by
    ext x
    exact congrArg Additive.ofMul (IdeleLimit.toClassLimit_diag x.toMul))

theorem shortExact_of_injective_of_surjective {k G : Type u} [CommRing k] [Group G]
    (S : ShortComplex (Rep.{u} k G)) (hf : Function.Injective S.f.hom)
    (hex : ∀ b, S.g.hom b = 0 → ∃ a, S.f.hom a = b) (hg : Function.Surjective S.g.hom) :
    S.ShortExact where
  exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{u} k G) (ModuleCat.{u} k)),
      ShortComplex.moduleCat_exact_iff]
    exact hex
  mono_f := (Rep.mono_iff_injective _).2 hf
  epi_g := (Rep.epi_iff_surjective _).2 hg

theorem idelesShortComplex_shortExact : idelesShortComplex.ShortExact := by
  refine shortExact_of_injective_of_surjective _ (fun x y h =>
    congrArg Additive.ofMul (IdeleLimit.diag_injective (congrArg Additive.toMul h))) (fun z hz => ?_)
    (fun c => ?_)
  · obtain ⟨a, ha⟩ := (IdeleLimit.mem_range_diag_iff (Additive.toMul z)).2
      (congrArg Additive.toMul hz)
    exact ⟨Additive.ofMul a, congrArg Additive.ofMul ha⟩
  · obtain ⟨z, hz⟩ := IdeleLimit.toClassLimit_surjective (Additive.toMul c)
    exact ⟨Additive.ofMul z, congrArg Additive.ofMul hz⟩

variable (K : FiniteSubfield)

abbrev unitsLimitRep : Rep ℤ K.1.fixingSubgroup := Rep.res K.1.fixingSubgroup.subtype unitsRep

abbrev classLimitRep : Rep ℤ K.1.fixingSubgroup := Rep.res K.1.fixingSubgroup.subtype classRep

abbrev idelesShortComplexRes : ShortComplex (Rep ℤ K.1.fixingSubgroup) :=
  idelesShortComplex.map (Rep.resFunctor K.1.fixingSubgroup.subtype)

theorem idelesShortComplexRes_shortExact : (idelesShortComplexRes K).ShortExact :=
  (Rep.shortExact_res _).2 idelesShortComplex_shortExact

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open GroundTheory.Global NumberField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

noncomputable abbrev ideleClassRep : Rep ℤ Gal(L/K) :=
  Rep.ofMulDistribMulAction Gal(L/K) (IdeleClassGroup L)

variable {K L}

omit [NumberField K] in

theorem ideleClassRep_ρ_apply (σ : Gal(L/K)) (x : Additive (IdeleClassGroup L)) :
    (ideleClassRep K L).ρ σ x = Additive.ofMul (σ • Additive.toMul x) :=
  rfl

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory CategoryTheory.Limits GroundTheory.Global NumberField Module

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem natCard_tateCohomology_zero_ideleClassRep (σ : Gal(L/K))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (tateCohomology (ideleClassRep K L) 0) = finrank K L := by
  rw [GroundTheory.GroupCoh.natCard_tateCohomology_zero _ hσ]
  exact (classFieldAxiom_ideleClassGroup σ hσ).1

theorem natCard_tateCohomology_neg_one_ideleClassRep (σ : Gal(L/K))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (tateCohomology (ideleClassRep K L) (-1)) = 1 := by
  rw [GroundTheory.GroupCoh.natCard_tateCohomology_neg_one _ hσ]
  exact (classFieldAxiom_ideleClassGroup σ hσ).2

variable [IsCyclic Gal(L/K)]

theorem isZero_groupCohomology_one_ideleClassRep_of_isCyclic :
    IsZero (groupCohomology (ideleClassRep K L) 1) := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  have e2 : (-1 + 2 : ℤ) = ((1 : ℕ) : ℤ) := by norm_num
  have h0 : Nat.card (groupCohomology (ideleClassRep K L) 1) =
      Nat.card (tateCohomology (ideleClassRep K L) ((1 : ℕ) : ℤ)) :=
    (Nat.card_congr
      ((TateCohomology.isoGroupCohomology 1).app (ideleClassRep K L)).toLinearEquiv.toEquiv).symm
  have h1 : Nat.card (tateCohomology (ideleClassRep K L) (-1 + 2)) =
      Nat.card (tateCohomology (ideleClassRep K L) (-1)) :=
    Nat.card_congr
      (GroundTheory.GroupCoh.tateCohomologyPeriodicIso (ideleClassRep K L) hσ (-1)).toLinearEquiv.toEquiv
  have h : Nat.card (groupCohomology (ideleClassRep K L) 1) = 1 := by
    rw [h0, ← e2, h1]
    exact natCard_tateCohomology_neg_one_ideleClassRep σ hσ
  have : Subsingleton (groupCohomology (ideleClassRep K L) 1) :=
    (Nat.card_eq_one_iff_unique.1 h).1
  exact ModuleCat.isZero_of_subsingleton _

theorem natCard_groupCohomology_two_ideleClassRep_of_isCyclic :
    Nat.card (groupCohomology (ideleClassRep K L) 2) = finrank K L := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  let e : groupCohomology (ideleClassRep K L) 2 ≅ tateCohomology (ideleClassRep K L) 0 :=
    ((TateCohomology.isoGroupCohomology 2).app (ideleClassRep K L)).symm ≪≫
      GroundTheory.GroupCoh.tateCohomologyPeriodicIso (ideleClassRep K L) hσ 0
  rw [Nat.card_congr e.toLinearEquiv.toEquiv]
  exact natCard_tateCohomology_zero_ideleClassRep σ hσ

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory CategoryTheory.Limits GroundTheory.Global NumberField Module IntermediateField

section Tower

variable (K F M : Type) [Field K] [NumberField K] [Field F] [NumberField F] [Field M]
  [NumberField M] [Algebra K F] [Algebra K M] [Algebra F M] [IsScalarTower K F M]

omit [NumberField K] in

theorem smul_ideleClassMap_restrictNormal [Normal K F] (σ : Gal(M/K)) (c : IdeleClassGroup F) :
    σ • ideleClassMap F M c = ideleClassMap F M (AlgEquiv.restrictNormalHom F σ • c) :=
  ideleClassEquiv_ideleClassMap_of_comm (AlgEquiv.restrictNormalHom F σ : F ≃+* F) (σ : M ≃+* M)
    (fun l => (AlgEquiv.restrictNormal_commutes σ F l).symm) c

variable [Normal K F] [IsGalois K M]

noncomputable def classFixingCohomologyIso (n : ℕ) :
    groupCohomology (ideleClassRep F M) n ≅
      groupCohomology (Rep.res (galFixing K F M).subtype (ideleClassRep K M)) n :=
  groupCohomology.mapIso (galFixingEquiv K F M) (LinearEquiv.refl _ _)
    (fun _ => LinearMap.ext fun _ => rfl) n

omit [NumberField K] [NumberField F] [IsGalois K M] in

theorem isZero_groupCohomology_one_classFixing
    (h : IsZero (groupCohomology (ideleClassRep F M) 1)) :
    IsZero (groupCohomology (Rep.res (galFixing K F M).subtype (ideleClassRep K M)) 1) :=
  h.of_iso (classFixingCohomologyIso K F M 1).symm

omit [NumberField K] [IsGalois K M] in

theorem smul_ideleClassMap_of_mem_galFixing (g : galFixing K F M) (c : IdeleClassGroup F) :
    (g : Gal(M/K)) • ideleClassMap F M c = ideleClassMap F M c := by
  rw [smul_ideleClassMap_restrictNormal, MonoidHom.mem_ker.1 g.2, one_smul]

noncomputable def classToInvariants :
    (ideleClassRep K F) →ₗ[ℤ]
      Representation.invariants ((ideleClassRep K M).ρ.comp (galFixing K F M).subtype) :=
  LinearMap.codRestrict _
    ((MonoidHom.toAdditive (ideleClassMap F M)).toIntLinearMap :
      (ideleClassRep K F) →ₗ[ℤ] (ideleClassRep K M)) fun x g =>
    congrArg Additive.ofMul
      (smul_ideleClassMap_of_mem_galFixing K F M g (Additive.toMul (α := IdeleClassGroup F) x))

omit [NumberField K] in

theorem classToInvariants_bijective : Function.Bijective (classToInvariants K F M) := by
  have : IsGalois F M := IsGalois.tower_top_of_isGalois K F M
  constructor
  · intro x y h
    have h' : ideleClassMap F M (Additive.toMul (α := IdeleClassGroup F) x) =
        ideleClassMap F M (Additive.toMul (α := IdeleClassGroup F) y) :=
      congrArg (fun v => Additive.toMul (α := IdeleClassGroup M) v.1) h
    exact Additive.toMul.injective (ideleClassMap_injective h')
  · intro v
    have hfix : ∀ τ : Gal(M/F), τ • Additive.toMul (α := IdeleClassGroup M) v.1 =
        Additive.toMul (α := IdeleClassGroup M) v.1 := by
      intro τ
      have := v.2 ⟨galRestrictScalars K F M τ, (range_galRestrictScalars K F M) ▸ ⟨τ, rfl⟩⟩
      exact congrArg (Additive.toMul (α := IdeleClassGroup M)) this
    obtain ⟨c, hc⟩ := (forall_smul_eq_iff_mem_range_ideleClassMap
      (Additive.toMul (α := IdeleClassGroup M) v.1)).1 hfix
    exact ⟨Additive.ofMul c, Subtype.ext (congrArg Additive.ofMul hc)⟩

noncomputable def classInvariantsEquiv :
    (ideleClassRep K F) ≃ₗ[ℤ]
      Representation.invariants ((ideleClassRep K M).ρ.comp (galFixing K F M).subtype) :=
  LinearEquiv.ofBijective _ (classToInvariants_bijective K F M)

noncomputable def classQuotientCohomologyIso (n : ℕ) :
    groupCohomology (ideleClassRep K F) n ≅
      groupCohomology ((ideleClassRep K M).quotientToInvariants (galFixing K F M)) n :=
  groupCohomology.mapIso (galQuotientEquiv K F M).symm (classInvariantsEquiv K F M) (fun g => by
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) M g
    have hq : (galQuotientEquiv K F M).symm (AlgEquiv.restrictNormalHom F σ) =
        (σ : Gal(M/K) ⧸ galFixing K F M) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hq]
    refine LinearMap.ext fun x => Subtype.ext ?_
    exact congrArg Additive.ofMul
      (smul_ideleClassMap_restrictNormal K F M σ
        (Additive.toMul (α := IdeleClassGroup F) x)).symm) n

variable {K F M}

omit [NumberField K] in

theorem isZero_groupCohomology_one_ideleClassRep_of_tower
    (hF : IsZero (groupCohomology (ideleClassRep K F) 1))
    (hM : IsZero (groupCohomology (ideleClassRep F M) 1)) :
    IsZero (groupCohomology (ideleClassRep K M) 1) := by
  have hS := isZero_groupCohomology_one_classFixing K F M hM
  have hQ : IsZero (groupCohomology ((ideleClassRep K M).quotientToInvariants
      (galFixing K F M)) 1) := hF.of_iso (classQuotientCohomologyIso K F M 1).symm
  have hex := GroundTheory.GroupCoh.range_inflation_eq_ker_restriction (A := ideleClassRep K M)
    (S := galFixing K F M) one_ne_zero fun i hi hi1 => absurd hi1 (by omega)
  rw [ModuleCat.isZero_iff_subsingleton] at hS hQ ⊢
  have hzero : ∀ x : groupCohomology (ideleClassRep K M) 1, x = 0 := by
    intro x
    have hx : x ∈ LinearMap.ker
        (GroundTheory.GroupCoh.restriction (ideleClassRep K M) (galFixing K F M) 1).hom := by
      rw [LinearMap.mem_ker]
      exact Subsingleton.elim _ _
    rw [← hex] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [Subsingleton.elim y 0, map_zero]
  exact ⟨fun x y => by rw [hzero x, hzero y]⟩

theorem natCard_groupCohomology_two_ideleClassRep_dvd_of_tower
    (hM1 : IsZero (groupCohomology (ideleClassRep F M) 1))
    (hM2 : Nat.card (groupCohomology (ideleClassRep F M) 2) ∣ finrank F M)
    (hF2 : Nat.card (groupCohomology (ideleClassRep K F) 2) ∣ finrank K F) :
    Nat.card (groupCohomology (ideleClassRep K M) 2) ∣ finrank K M := by
  have h1 := isZero_groupCohomology_one_classFixing K F M hM1
  have hinj := GroundTheory.GroupCoh.inflation_two_injective (A := ideleClassRep K M)
    (S := galFixing K F M) h1
  have hex := GroundTheory.GroupCoh.range_inflation_two_eq_ker_restriction (A := ideleClassRep K M)
    (S := galFixing K F M) h1
  set res := (GroundTheory.GroupCoh.restriction (ideleClassRep K M) (galFixing K F M) 2).hom
  set infl := (GroundTheory.GroupCoh.inflation (ideleClassRep K M) (galFixing K F M) 2).hom

  have hcard : Nat.card (groupCohomology (ideleClassRep K M) 2) =
      Nat.card (LinearMap.range res) * Nat.card (LinearMap.ker res) := by
    rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker res),
      Nat.card_congr (LinearMap.quotKerEquivRange res).toEquiv, mul_comm]

  have hker : Nat.card (LinearMap.ker res) =
      Nat.card (groupCohomology (ideleClassRep K F) 2) := by
    rw [← hex, ← Nat.card_congr (LinearEquiv.ofInjective infl hinj).toEquiv]
    exact (Nat.card_congr (classQuotientCohomologyIso K F M 2).toLinearEquiv.toEquiv).symm

  have hrange : Nat.card (LinearMap.range res) ∣
      Nat.card (groupCohomology (ideleClassRep F M) 2) := by
    rw [Nat.card_congr (classFixingCohomologyIso K F M 2).toLinearEquiv.toEquiv]
    exact AddSubgroup.card_addSubgroup_dvd_card (LinearMap.range res).toAddSubgroup
  rw [hcard, hker, ← Module.finrank_mul_finrank K F M, mul_comm (finrank K F)]
  exact Nat.mul_dvd_mul (hrange.trans hM2) hF2

end Tower

section PGroup

theorem ideleClassRep_of_isPGroup_of_finrank (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [IsGalois K L], IsPGroup p Gal(L/K) → finrank K L = n →
      IsZero (groupCohomology (ideleClassRep K L) 1) ∧
        Nat.card (groupCohomology (ideleClassRep K L) 2) ∣ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K L _ _ _ _ _ _ hp hn
  subst hn
  by_cases hcyc : IsCyclic Gal(L/K)
  · exact ⟨isZero_groupCohomology_one_ideleClassRep_of_isCyclic,
      natCard_groupCohomology_two_ideleClassRep_of_isCyclic.dvd⟩
  have : Group.IsNilpotent Gal(L/K) := hp.isNilpotent
  obtain ⟨N, hN, hbot, htop⟩ := exists_normal_ne_bot_ne_top_of_not_isCyclic hcyc
  have hpos : 0 < finrank K (fixedField N) := Module.finrank_pos
  have hLE : finrank (fixedField N) L = Nat.card N := finrank_fixedField_eq_card N
  have hmul := Module.finrank_mul_finrank K (fixedField N) L
  have hcardG : Nat.card Gal(L/K) = finrank K L := IsGalois.card_aut_eq_finrank K L
  have hNlt : Nat.card N < finrank K L := by
    rw [← hcardG]
    exact lt_of_le_of_ne (Subgroup.card_le_card_group N)
      fun h => htop ((Subgroup.card_eq_iff_eq_top N).1 h)
  have hN1 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).2 hbot
  have hpL : IsPGroup p Gal(L/fixedField N) :=
    (hp.to_subgroup N).of_equiv (subgroupEquivGalFixedField N)
  have hpE : IsPGroup p Gal(fixedField N/K) :=
    hp.of_surjective (AlgEquiv.restrictNormalHom (fixedField N))
      (AlgEquiv.restrictNormalHom_surjective L)
  obtain ⟨hL1, hL2⟩ := ih _ (by rw [hLE]; exact hNlt) (fixedField N) L hpL rfl
  obtain ⟨hE1, hE2⟩ := ih _ (by rw [← hmul, hLE]; exact lt_mul_right hpos hN1) K (fixedField N)
    hpE rfl
  exact ⟨isZero_groupCohomology_one_ideleClassRep_of_tower hE1 hL1,
    natCard_groupCohomology_two_ideleClassRep_dvd_of_tower hL1 hL2 hE2⟩

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem isZero_groupCohomology_one_ideleClassRep_of_isPGroup {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p Gal(L/K)) : IsZero (groupCohomology (ideleClassRep K L) 1) :=
  (ideleClassRep_of_isPGroup_of_finrank p _ K L hp rfl).1

theorem natCard_groupCohomology_two_ideleClassRep_dvd_of_isPGroup {p : ℕ} [Fact p.Prime]
    (hp : IsPGroup p Gal(L/K)) :
    Nat.card (groupCohomology (ideleClassRep K L) 2) ∣ finrank K L :=
  (ideleClassRep_of_isPGroup_of_finrank p _ K L hp rfl).2

end PGroup

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory CategoryTheory.Limits GroundTheory.Global NumberField Module IntermediateField

section Sylow

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem eq_zero_of_forall_sylow_map_eq_zero (A : Rep.{u} k G) (n : ℕ) [NeZero n]
    (x : groupCohomology A n)
    (h : ∀ p ∈ (Nat.card G).primeFactors, ∃ P : Sylow p G,
      (groupCohomology.map (P : Subgroup G).subtype (𝟙 _) n).hom x = 0) :
    x = 0 := by
  classical
  let e : tateCohomology A (n : ℤ) ≅ groupCohomology A n :=
    (TateCohomology.isoGroupCohomology n).app A
  obtain ⟨y, hy⟩ := e.toLinearEquiv.surjective x
  subst hy
  suffices hy : y = 0 by subst hy; exact map_zero _

  have hidx : ∀ p ∈ (Nat.card G).primeFactors, ∃ P : Sylow p G, (P : Subgroup G).index • y = 0 := by
    intro p hp
    obtain ⟨P, hP⟩ := h p hp
    refine ⟨P, ?_⟩
    have hc := congrArg (fun f => f.hom y)
      (GroundTheory.GroupCoh.tateRes_comp_isoGroupCohomology (P : Subgroup G) n A)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hc
    have hres : ((GroundTheory.GroupCoh.tateRes (P : Subgroup G) n).app A).hom y = 0 := by
      have hinj : Function.Injective
          ((TateCohomology.isoGroupCohomology n).app (Rep.res (P : Subgroup G).subtype A)).toLinearEquiv :=
        LinearEquiv.injective _
      apply hinj
      rw [map_zero]
      exact hc.trans hP
    rw [← GroundTheory.GroupCoh.tateCores_app_tateRes_app_apply (P : Subgroup G) A n y, hres, map_zero]

  have hG : Nat.card G • y = 0 := by
    rw [Nat.card_eq_fintype_card]
    exact GroundTheory.GroupCoh.card_smul_tateCohomology A n y
  by_contra hne
  have hm1 : addOrderOf y ≠ 1 := fun h1 => hne (AddMonoid.addOrderOf_eq_one_iff.1 h1)
  set q := (addOrderOf y).minFac
  have hq : q.Prime := Nat.minFac_prime hm1
  have hqG : q ∣ Nat.card G := (Nat.minFac_dvd _).trans (addOrderOf_dvd_of_nsmul_eq_zero hG)
  have hqmem : q ∈ (Nat.card G).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hq, hqG, Nat.card_pos.ne'⟩
  obtain ⟨P, hP⟩ := hidx q hqmem
  have : Fact q.Prime := ⟨hq⟩
  exact P.not_dvd_index ((Nat.minFac_dvd _).trans (addOrderOf_dvd_of_nsmul_eq_zero hP))

end Sylow

section Level

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

noncomputable def groupCohomologyResIdeleClassIso (H : Subgroup Gal(L/K)) (n : ℕ) :
    groupCohomology (Rep.res H.subtype (ideleClassRep K L)) n ≅
      groupCohomology (ideleClassRep (fixedField H) L) n :=
  groupCohomology.mapIso (subgroupEquivGalFixedField H) (LinearEquiv.refl _ _)
    (fun _ => LinearMap.ext fun _ => rfl) n

variable [IsGalois K L]

omit [IsGalois K L] in

theorem isPGroup_gal_fixedField_sylow {p : ℕ} (P : Sylow p Gal(L/K)) :
    IsPGroup p Gal(L/fixedField (P : Subgroup Gal(L/K))) :=
  P.isPGroup'.of_equiv (subgroupEquivGalFixedField _)

theorem isZero_groupCohomology_one_ideleClassRep :
    IsZero (groupCohomology (ideleClassRep K L) 1) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  have hz : ∀ x : groupCohomology (ideleClassRep K L) 1, x = 0 := fun x =>
    eq_zero_of_forall_sylow_map_eq_zero _ 1 x fun p hp => by
      have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
      let P : Sylow p Gal(L/K) := Classical.arbitrary _
      refine ⟨P, ?_⟩
      have h0 := (isZero_groupCohomology_one_ideleClassRep_of_isPGroup
        (isPGroup_gal_fixedField_sylow P)).of_iso
        (groupCohomologyResIdeleClassIso (P : Subgroup Gal(L/K)) 1)
      rw [ModuleCat.isZero_iff_subsingleton] at h0
      exact Subsingleton.elim _ _
  exact ⟨fun x y => by rw [hz x, hz y]⟩

theorem natCard_groupCohomology_two_ideleClassRep_dvd :
    Nat.card (groupCohomology (ideleClassRep K L) 2) ∣ finrank K L := by
  classical
  set n := Nat.card Gal(L/K) with hn
  have hn0 : n ≠ 0 := Nat.card_pos.ne'

  have hS : ∀ p : n.primeFactors, ∃ _ : Sylow (p : ℕ) Gal(L/K), True := fun p => by
    have : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    exact ⟨Classical.arbitrary _, trivial⟩
  choose P _ using hS

  let Φ : groupCohomology (ideleClassRep K L) 2 →+
      ∀ p : n.primeFactors,
        groupCohomology (ideleClassRep (fixedField (P p : Subgroup Gal(L/K))) L) 2 :=
    AddMonoidHom.pi fun p =>
      ((groupCohomologyResIdeleClassIso (P p : Subgroup Gal(L/K)) 2).hom.hom.comp
        (groupCohomology.map (P p : Subgroup Gal(L/K)).subtype (𝟙 _) 2).hom).toAddMonoidHom
  have hΦ : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 fun x hx => ?_
    refine eq_zero_of_forall_sylow_map_eq_zero _ 2 x fun p hp => ⟨P ⟨p, hp⟩, ?_⟩
    have hxp := congrFun hx ⟨p, hp⟩
    have hinj : Function.Injective
        (groupCohomologyResIdeleClassIso (P ⟨p, hp⟩ : Subgroup Gal(L/K)) 2).toLinearEquiv :=
      LinearEquiv.injective _
    apply hinj
    rw [map_zero]
    exact hxp

  have hdvd : ∀ p : n.primeFactors,
      Nat.card (groupCohomology (ideleClassRep (fixedField (P p : Subgroup Gal(L/K))) L) 2) ∣
        (p : ℕ) ^ n.factorization p := by
    intro p
    have : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    have h := natCard_groupCohomology_two_ideleClassRep_dvd_of_isPGroup
      (isPGroup_gal_fixedField_sylow (P p))
    rwa [finrank_fixedField_eq_card, Sylow.card_eq_multiplicity] at h
  calc Nat.card (groupCohomology (ideleClassRep K L) 2)
      = Nat.card Φ.range := Nat.card_congr (AddMonoidHom.ofInjective hΦ).toEquiv
    _ ∣ Nat.card (∀ p : n.primeFactors,
          groupCohomology (ideleClassRep (fixedField (P p : Subgroup Gal(L/K))) L) 2) :=
        AddSubgroup.card_addSubgroup_dvd_card _
    _ = ∏ p : n.primeFactors,
          Nat.card (groupCohomology (ideleClassRep (fixedField (P p : Subgroup Gal(L/K))) L) 2) :=
        Nat.card_pi
    _ ∣ ∏ p : n.primeFactors, (p : ℕ) ^ n.factorization p :=
        Finset.prod_dvd_prod_of_dvd _ _ fun p _ => hdvd p
    _ = n := by
        rw [Finset.prod_coe_sort n.primeFactors (fun p => p ^ n.factorization p)]
        exact (Nat.prod_primeFactors_pow_factorization hn0).symm
    _ = finrank K L := IsGalois.card_aut_eq_finrank K L


end Level

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield}

section Level

variable {F : FiniteSubfield} [Fact (K ≤ F)] [F.1.fixingSubgroup.Normal]

theorem classSmul_of_restrictHom (g : K.1.fixingSubgroup) (c : IdeleClassGroup F.1) :
    (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • IdeleClassLimit.of F c = IdeleClassLimit.of F (restrictHom (E := F) g • c) :=
  IdeleClassLimit.smul_of_of_normal g c

variable (K F) in

def classLevelMor :
    Rep.res (restrictHom (F := K) (E := F)) (ideleClassRep K.1 F.1) ⟶ classLimitRep K :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (IdeleClassLimit.of F)).toIntLinearMap, fun g => LinearMap.ext fun x =>
    congrArg Additive.ofMul (classSmul_of_restrictHom g x.toMul).symm⟩

@[simp]
theorem classLevelMor_hom_apply (x : Additive (IdeleClassGroup F.1)) :
    (classLevelMor K F).hom x = Additive.ofMul (IdeleClassLimit.of F x.toMul) :=
  rfl

variable (K F) in

def classLevelInfl (n : ℕ) : cohomology (ideleClassRep K.1 F.1) n ⟶ cohomology (classLimitRep K) n :=
  cohomologyMapAlong restrictHom continuous_restrictHom (classLevelMor K F) n

end Level

section Transition

variable {F E : FiniteSubfield} [Fact (K ≤ F)] [Fact (K ≤ E)] [Fact (F ≤ E)]
  [F.1.fixingSubgroup.Normal] [E.1.fixingSubgroup.Normal]

theorem ideleClassMap_smul (τ : E.1 ≃ₐ[K.1] E.1) (c : IdeleClassGroup F.1) :
    ideleClassMap (Fact.out : F ≤ E) (levelRestrict K F E τ • c) =
      τ • ideleClassMap (Fact.out : F ≤ E) c := by
  change ideleClassMap (Fact.out : F ≤ E)
      (ideleClassEquiv ((levelRestrict K F E τ : F.1 ≃ₐ[K.1] F.1) : F.1 ≃+* F.1) c) =
    ideleClassEquiv ((τ : E.1 ≃ₐ[K.1] E.1) : E.1 ≃+* E.1) (ideleClassMap (Fact.out : F ≤ E) c)
  let := algebraOfLE (Fact.out : F ≤ E)
  exact (ideleClassEquiv_ideleClassMap_of_comm ((levelRestrict K F E τ : F.1 ≃ₐ[K.1] F.1) : F.1 ≃+* F.1)
    (τ : E.1 ≃+* E.1) (fun y ↦ (coe_levelRestrict_apply τ y).symm) c).symm

variable (K F E) in

def classLevelMap : Rep.res (levelRestrict K F E) (ideleClassRep K.1 F.1) ⟶ ideleClassRep K.1 E.1 :=
  Rep.ofHom ⟨(MonoidHom.toAdditive (ideleClassMap (Fact.out : F ≤ E))).toIntLinearMap,
    fun τ => LinearMap.ext fun x => congrArg Additive.ofMul (ideleClassMap_smul τ x.toMul)⟩

@[simp]
theorem classLevelMap_hom_apply (x : Additive (IdeleClassGroup F.1)) :
    (classLevelMap K F E).hom x = Additive.ofMul (ideleClassMap (Fact.out : F ≤ E) x.toMul) :=
  rfl

variable (K F E) in

def classLevelTransition (n : ℕ) :
    cohomology (ideleClassRep K.1 F.1) n ⟶ cohomology (ideleClassRep K.1 E.1) n :=
  cohomologyMapAlong (levelRestrict K F E) continuous_levelRestrict (classLevelMap K F E) n

theorem classLevelCochains_comp :
    cochainsMapAlong (levelRestrict K F E) continuous_levelRestrict (classLevelMap K F E) ≫
      cochainsMapAlong restrictHom continuous_restrictHom (classLevelMor K E) =
      cochainsMapAlong restrictHom continuous_restrictHom (classLevelMor K F) := by
  rw [← cochainsMapAlong_comp]
  ext m x : 3
  apply Subtype.ext
  funext g
  change Additive.ofMul (IdeleClassLimit.of E (ideleClassMap (Fact.out : F ≤ E)
      ((x.1 fun i => levelRestrict K F E (restrictHom (E := E) (g i))).toMul))) =
    Additive.ofMul (IdeleClassLimit.of F ((x.1 fun i => restrictHom (E := F) (g i)).toMul))
  have hfun : (fun i => levelRestrict K F E (restrictHom (E := E) (g i))) =
      fun i => restrictHom (E := F) (g i) := funext fun i => levelRestrict_restrictHom (g i)
  refine (congrArg Additive.ofMul (IdeleClassLimit.of_ideleClassMap (Fact.out : F ≤ E) _)).trans ?_
  rw [hfun]


end Transition

section Colimit

abbrev classLevelCochainsInfl (p : GLevel K) :
    cochainsComplex (ideleClassRep K.1 p.1.1) ⟶ cochainsComplex (classLimitRep K) :=
  cochainsMapAlong restrictHom continuous_restrictHom (classLevelMor K p.1)

abbrev classLevelCochainsMap {p q : GLevel K} (h : p ≤ q) :
    cochainsComplex (ideleClassRep K.1 p.1.1) ⟶ cochainsComplex (ideleClassRep K.1 q.1.1) :=
  haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
  cochainsMapAlong (levelRestrict K p.1 q.1) continuous_levelRestrict (classLevelMap K p.1 q.1)

theorem classLevelCochainsMap_comp_classLevelCochainsInfl {p q : GLevel K} (h : p ≤ q) :
    classLevelCochainsMap h ≫ classLevelCochainsInfl q = classLevelCochainsInfl p :=
  haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
  classLevelCochains_comp

theorem classLevelCochains_injective (p : GLevel K) (m : ℕ) :
    Function.Injective ((classLevelCochainsInfl p).f m).hom := by
  intro y y' h
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι (ideleClassRep K.1 p.1.1)).f m)).1 inferInstance
  funext τ
  let σ : Fin m → K.1.fixingSubgroup := fun i =>
    Function.surjInv (restrictHom_surjective (F := K) (E := p.1)) (τ i)
  have hσ : (fun i => restrictHom (E := p.1) (σ i)) = τ :=
    funext fun i => Function.surjInv_eq (restrictHom_surjective (F := K) (E := p.1)) (τ i)
  have h1 := congrFun (congrArg (fun c => ((cochainsComplexι (classLimitRep K)).f m).hom c) h) σ
  simp only at h1
  change Additive.ofMul (IdeleClassLimit.of p.1 (((cochainsComplexι _).f m).hom y
      (fun i => restrictHom (E := p.1) (σ i))).toMul) =
    Additive.ofMul (IdeleClassLimit.of p.1 (((cochainsComplexι _).f m).hom y'
      (fun i => restrictHom (E := p.1) (σ i))).toMul) at h1
  rw [hσ] at h1
  exact congrArg Additive.ofMul (IdeleClassLimit.of_injective p.1 (congrArg Additive.toMul h1))

theorem exists_classLevelCochains_eq (m : ℕ) (x : (cochainsComplex (classLimitRep K)).X m) :
    ∃ (p : GLevel K) (y : (cochainsComplex (ideleClassRep K.1 p.1.1)).X m),
      ((classLevelCochainsInfl p).f m).hom y = x := by
  classical
  have hx : IsLocallyConstant (((cochainsComplexι (classLimitRep K)).f m).hom x :
      (Fin m → K.1.fixingSubgroup) → classLimitRep K) :=
    (show locallyConstantCochains (classLimitRep K) m from x).2
  set f := ((cochainsComplexι (classLimitRep K)).f m).hom x with hf
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_fin_of_isLocallyConstant hx
  obtain ⟨t, ht, htU⟩ := isOpen_induced_iff.1 U.isOpen
  have h1t : (1 : ℚ̄ ≃ₐ[ℚ] ℚ̄) ∈ t := by
    have : (1 : K.1.fixingSubgroup) ∈ Subtype.val ⁻¹' t := by
      rw [htU]
      exact U.one_mem
    exact this
  obtain ⟨E₀, hE₀fin, hE₀⟩ := (krullTopology_mem_nhds_one_iff ℚ ℚ̄ t).1 (ht.mem_nhds h1t)
  have hfin : (Set.range f).Finite := hx.range_finite
  choose idx x' hx' using fun a : classLimitRep K => IdeleClassLimit.exists_of (Additive.toMul a)
  choose lev hlev using fun E : FiniteSubfield => GLevel.exists_le (K := K) E
  obtain ⟨p, hp⟩ := Finset.exists_le ((hfin.toFinset.image fun a => lev (idx a)) ∪
    {lev ⟨E₀, hE₀fin⟩})
  have hpE₀ : E₀ ≤ p.1.1 := (hlev ⟨E₀, hE₀fin⟩).trans
    (hp _ (Finset.mem_union_right _ (Finset.mem_singleton_self _)))
  have hker : ∀ g : K.1.fixingSubgroup, restrictHom (E := p.1) g = 1 → g ∈ U := by
    intro g hg
    have hg' : g ∈ p.1.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup := by
      rw [← ker_restrictHom, MonoidHom.mem_ker]
      exact hg
    rw [Subgroup.mem_subgroupOf] at hg'
    have : g ∈ Subtype.val ⁻¹' t := hE₀ (IntermediateField.fixingSubgroup_le hpE₀ hg')
    rw [htU] at this
    exact this
  have hval : ∀ g, ∃ z : IdeleClassGroup p.1.1, IdeleClassLimit.of p.1 z = Additive.toMul (f g) := by
    intro g
    have hmem : f g ∈ hfin.toFinset := by simp
    have hle : idx (f g) ≤ p.1 := (hlev (idx (f g))).trans
      (hp _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hmem)))
    exact ⟨ideleClassMap hle (x' (f g)), by rw [IdeleClassLimit.of_ideleClassMap]; exact hx' _⟩
  choose z hz using hval
  let lift : (Fin m → (p.1.1 ≃ₐ[K.1] p.1.1)) → Fin m → K.1.fixingSubgroup := fun τ i =>
    Function.surjInv (restrictHom_surjective (F := K) (E := p.1)) (τ i)
  refine ⟨p, ⟨fun τ => Additive.ofMul (z (lift τ)), IsLocallyConstant.of_discrete _⟩, ?_⟩
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι (classLimitRep K)).f m)).1 inferInstance
  funext g
  change Additive.ofMul (IdeleClassLimit.of p.1 (z (lift fun i => restrictHom (E := p.1) (g i)))) = f g
  rw [hz]
  refine hU _ _ fun i => hker _ ?_
  rw [map_mul, map_inv, Function.surjInv_eq (restrictHom_surjective (F := K) (E := p.1)),
    inv_mul_cancel]

theorem exists_classLevelInfl_eq (n : ℕ) (x : cohomology (classLimitRep K) n) :
    ∃ (p : GLevel K) (y : cohomology (ideleClassRep K.1 p.1.1) n), (classLevelInfl K p.1 n).hom y = x := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((cochainsComplex (classLimitRep K)).homologyπ n)).1 inferInstance x
  obtain ⟨p, y₀, hy₀⟩ := exists_classLevelCochains_eq n
    (((cochainsComplex (classLimitRep K)).iCycles n).hom z)
  have hd : ((cochainsComplex (ideleClassRep K.1 p.1.1)).d n (n + 1)).hom y₀ = 0 := by
    apply classLevelCochains_injective p (n + 1)
    rw [map_zero, hom_f_d_apply, hy₀]
    exact iCycles_d_apply _ n (n + 1) z
  obtain ⟨w, hw⟩ := exists_iCycles_eq_of_d_eq_zero _ n y₀ hd
  refine ⟨p, ((cochainsComplex (ideleClassRep K.1 p.1.1)).homologyπ n).hom w, ?_⟩
  refine (homologyMap_homologyπ_apply (classLevelCochainsInfl p) n w).trans (congrArg _ ?_)
  apply (ModuleCat.mono_iff_injective ((cochainsComplex (classLimitRep K)).iCycles n)).1 inferInstance
  rw [iCycles_cyclesMap_apply, hw, hy₀]

set_option maxHeartbeats 1600000 in

theorem exists_classLevelTransition_eq_zero (n : ℕ) (p : GLevel K)
    (y : cohomology (ideleClassRep K.1 p.1.1) n) (hy : (classLevelInfl K p.1 n).hom y = 0) :
    ∃ (q : GLevel K) (h : p ≤ q),
      (HomologicalComplex.homologyMap (classLevelCochainsMap h) n).hom y = 0 := by
  obtain ⟨w, hw⟩ : ∃ w, ((cochainsComplex (ideleClassRep K.1 p.1.1)).homologyπ n).hom w = y :=
    (ModuleCat.epi_iff_surjective ((cochainsComplex (ideleClassRep K.1 p.1.1)).homologyπ n)).1
      inferInstance y
  subst hw
  have hy' := (homologyMap_homologyπ_apply (classLevelCochainsInfl p) n w).symm.trans hy
  obtain ⟨u, hu⟩ := (homologyπ_eq_zero_iff _ _).1 hy'
  rw [iCycles_cyclesMap_apply] at hu
  obtain ⟨q, u', hu'⟩ := exists_classLevelCochains_eq _ u
  obtain ⟨r, hpr, hqr⟩ := GLevel.exists_ge p q
  refine ⟨r, hpr, (homologyMap_homologyπ_apply (classLevelCochainsMap hpr) n w).trans
    ((homologyπ_eq_zero_iff _ _).2 ⟨((classLevelCochainsMap hqr).f _).hom u', ?_⟩)⟩
  rw [iCycles_cyclesMap_apply]
  apply classLevelCochains_injective r n
  rw [hom_f_d_apply]
  have e1 := congrArg (fun φ => (φ.f _).hom u') (classLevelCochainsMap_comp_classLevelCochainsInfl hqr)
  have e2 := congrArg (fun φ => (φ.f n).hom
      (((cochainsComplex (ideleClassRep K.1 p.1.1)).iCycles n).hom w))
    (classLevelCochainsMap_comp_classLevelCochainsInfl hpr)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at e1 e2
  rw [e1, e2, hu', hu]

end Colimit

variable (K) in

theorem isZero_cohomology_one_classLimitRep : Limits.IsZero (cohomology (classLimitRep K) 1) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  have hz : ∀ x : cohomology (classLimitRep K) 1, x = 0 := by
    intro x
    obtain ⟨p, y, rfl⟩ := exists_classLevelInfl_eq 1 x
    have h0 : Limits.IsZero (cohomology (ideleClassRep K.1 p.1.1) 1) :=
      isZero_groupCohomology_one_ideleClassRep.of_iso (cohomologyIsoGroupCohomology _ 1)
    rw [ModuleCat.isZero_iff_subsingleton] at h0
    rw [Subsingleton.elim y 0, map_zero]
  exact ⟨fun x y => by rw [hz x, hz y]⟩

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField GroundTheory.Global FiniteSubfield

open scoped DirectSum

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable (K : FiniteSubfield)

instance isDiscreteRep_idelesShortComplexRes_X₁ : IsDiscreteRep (idelesShortComplexRes K).X₁ :=
  inferInstanceAs (IsDiscreteRep (unitsLimitRep K))

instance isDiscreteRep_idelesShortComplexRes_X₂ : IsDiscreteRep (idelesShortComplexRes K).X₂ :=
  inferInstanceAs (IsDiscreteRep (limitRep K))

instance isDiscreteRep_idelesShortComplexRes_X₃ : IsDiscreteRep (idelesShortComplexRes K).X₃ :=
  inferInstanceAs (IsDiscreteRep (classLimitRep K))

abbrev unitsToIdeles (n : ℕ) : cohomology (unitsLimitRep K) n ⟶ cohomology (limitRep K) n :=
  cohomologyMap (idelesShortComplexRes K).f n

abbrev idelesToClasses (n : ℕ) : cohomology (limitRep K) n ⟶ cohomology (classLimitRep K) n :=
  cohomologyMap (idelesShortComplexRes K).g n

abbrev classesToUnits (n : ℕ) : cohomology (classLimitRep K) n ⟶ cohomology (unitsLimitRep K) (n + 1) :=
  δ (idelesShortComplexRes_shortExact K) n (n + 1) rfl

theorem exists_unitsToIdeles_eq (n : ℕ) (y : cohomology (limitRep K) n)
    (hy : (idelesToClasses K n).hom y = 0) : ∃ x, (unitsToIdeles K n).hom x = y :=
  ((ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    (cohomology_exact₂ (idelesShortComplexRes_shortExact K) n)) hy


theorem exists_classesToUnits_eq (n : ℕ) (x : cohomology (unitsLimitRep K) (n + 1))
    (hx : (unitsToIdeles K (n + 1)).hom x = 0) : ∃ c, (classesToUnits K n).hom c = x :=
  ((ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    (cohomology_exact₁ (idelesShortComplexRes_shortExact K) n (n + 1) rfl)) hx

theorem injective_cohomologyMap_units_ideles : Function.Injective (unitsToIdeles K 2).hom := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨c, rfl⟩ := exists_classesToUnits_eq K 1 x hx
  have h0 := isZero_cohomology_one_classLimitRep K
  rw [ModuleCat.isZero_iff_subsingleton] at h0
  rw [Subsingleton.elim c 0, map_zero]

variable {K}

def brauerLocal (ι : LocalEmbeddings K) :
    cohomology (unitsLimitRep K) 2 →+ ⨁ v : Place K.1, localGaloisCohomology K 2 v :=
  (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).toAddMonoidHom.comp
    (unitsToIdeles K 2).hom.toAddMonoidHom

theorem brauerLocal_apply (ι : LocalEmbeddings K) (x : cohomology (unitsLimitRep K) 2) :
    brauerLocal ι x = idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2) ((unitsToIdeles K 2).hom x) :=
  rfl

theorem brauerLocal_injective (ι : LocalEmbeddings K) : Function.Injective (brauerLocal ι) :=
  (idelesLimitCohomologyEquiv ι (by norm_num : 1 ≤ 2)).injective.comp
    (injective_cohomologyMap_units_ideles K)

theorem eq_zero_of_brauerLocal_apply_eq_zero (ι : LocalEmbeddings K) (x : cohomology (unitsLimitRep K) 2)
    (hx : ∀ v, brauerLocal ι x v = 0) : x = 0 :=
  brauerLocal_injective ι ((DFinsupp.ext hx).trans (map_zero _).symm)

def brauerSumInv (ι : LocalEmbeddings K) : cohomology (unitsLimitRep K) 2 →+ QZ :=
  (sumPlaceInv K).comp (brauerLocal ι)

end

end GroundTheory.ProfCoh
end
