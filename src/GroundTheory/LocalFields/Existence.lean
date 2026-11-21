import Mathlib
import GroundTheory.LocalFields.LocalReciprocityFinite
import GroundTheory.LocalFields.LubinTateReciprocity.Descent
import GroundTheory.LocalFields.LocalAxiom
import GroundTheory.LocalFields.AbstractLocalReciprocity.ReciprocityMap
import GroundTheory.LocalFields.LubinTateUnramified

section
namespace GroundTheory.LocalField

open Abstract

section Dictionary

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

attribute [local instance] isDiscreteModule_units

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem normal_subgroupOf_top_fixingOpenSubgroup_iff (L : IntermediateField K Ω)
    [FiniteDimensional K L] :
    ((fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).Normal ↔ IsGalois K L := by
  rw [← InfiniteGalois.normal_iff_isGalois, coe_fixingOpenSubgroup]
  constructor
  · intro h
    refine ⟨fun n hn g => ?_⟩
    have := h.conj_mem ⟨n, Subgroup.mem_top n⟩ (Subgroup.mem_subgroupOf.2 hn) ⟨g, Subgroup.mem_top g⟩
    exact Subgroup.mem_subgroupOf.1 this
  · intro h
    exact h.subgroupOf _

theorem isAbelianExtension_fixingOpenSubgroup_iff (L : IntermediateField K Ω) [FiniteDimensional K L] :
    IsAbelianExtension ⊤ (fixingOpenSubgroup L) ↔
      IsGalois K L ∧ ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ := by
  constructor
  · intro h
    have hn := h.normal
    have hG : IsGalois K L := (normal_subgroupOf_top_fixingOpenSubgroup_iff L).1 hn
    refine ⟨hG, fun σ τ => ?_⟩
    have hc := h.isMulCommutative
    obtain ⟨p, rfl⟩ := (baseQuotientEquiv L).surjective σ
    obtain ⟨q, rfl⟩ := (baseQuotientEquiv L).surjective τ
    rw [← map_mul, ← map_mul, hc.is_comm.comm]
  · rintro ⟨hG, hc⟩
    have hn := (normal_subgroupOf_top_fixingOpenSubgroup_iff L).2 hG
    have : IsMulCommutative (((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) ⧸
        (fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
          ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) :=
      ⟨⟨fun p q => (baseQuotientEquiv L).injective (by rw [map_mul, map_mul, hc])⟩⟩
    exact isAbelianExtension_of_isMulCommutative le_top

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem map_baseUnitsEquiv_normGroup (L : IntermediateField K Ω) [FiniteDimensional K L] :
    (normGroup Ωˣ ⊤ (fixingOpenSubgroup L)).map
      (baseUnitsEquiv (K := K) (Ω := Ω) : fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) →* Kˣ) =
      (normUnits K L).range := by
  have : (L.fixingSubgroup.subgroupOf ⊤).FiniteIndex :=
    inferInstanceAs (((fixingOpenSubgroup L : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).FiniteIndex)
  ext y
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨_, (baseUnitsEquiv_norm L a).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨_, ⟨(fixedModuleUnitsEquiv L).symm b, rfl⟩, ?_⟩
    change baseUnitsEquiv (Abstract.norm Ωˣ ⊤ L.fixingSubgroup _) = _
    rw [baseUnitsEquiv_norm, MulEquiv.apply_symm_apply]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem mem_normGroup_iff_mem_range_normUnits (L : IntermediateField K Ω) [FiniteDimensional K L]
    (a : fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω))) :
    a ∈ normGroup Ωˣ ⊤ (fixingOpenSubgroup L) ↔ baseUnitsEquiv a ∈ (normUnits K L).range := by
  rw [← map_baseUnitsEquiv_normGroup L]
  constructor
  · intro ha
    exact ⟨a, ha, rfl⟩
  · rintro ⟨b, hb, hba⟩
    rwa [← baseUnitsEquiv.injective hba]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem normGroup_eq_comap (L : IntermediateField K Ω) [FiniteDimensional K L] :
    normGroup Ωˣ ⊤ (fixingOpenSubgroup L) =
      (normUnits K L).range.comap
        (baseUnitsEquiv (K := K) (Ω := Ω) : fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) →* Kˣ) := by
  ext a
  exact mem_normGroup_iff_mem_range_normUnits L a

variable (L : IntermediateField K Ω) [FiniteDimensional K L]

noncomputable def maximalAbelianSubextension : IntermediateField K Ω :=
  IntermediateField.fixedField (maxAbelian (le_top : fixingOpenSubgroup L ≤ ⊤) : Subgroup (Ω ≃ₐ[K] Ω))

instance finiteDimensional_maximalAbelianSubextension :
    FiniteDimensional K (maximalAbelianSubextension L) :=
  finiteDimensional_fixedField_openSubgroup _

theorem fixingOpenSubgroup_maximalAbelianSubextension :
    fixingOpenSubgroup (maximalAbelianSubextension L) = maxAbelian (le_top : fixingOpenSubgroup L ≤ ⊤) :=
  fixingOpenSubgroup_fixedField _

theorem isAbelianExtension_fixingOpenSubgroup_maximalAbelianSubextension :
    IsAbelianExtension ⊤ (fixingOpenSubgroup (maximalAbelianSubextension L)) := by
  rw [fixingOpenSubgroup_maximalAbelianSubextension]
  exact isAbelianExtension_maxAbelian _

instance isGalois_maximalAbelianSubextension : IsGalois K (maximalAbelianSubextension L) :=
  ((isAbelianExtension_fixingOpenSubgroup_iff _).1
    (isAbelianExtension_fixingOpenSubgroup_maximalAbelianSubextension L)).1

end Dictionary

section Correspondence

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

attribute [local instance] isDiscreteModule_units

theorem range_normUnits_le_range_normUnits_iff {L L' : IntermediateField K Ω} [FiniteDimensional K L]
    [FiniteDimensional K L'] [IsGalois K L] [IsGalois K L']
    (hL : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) (hL' : ∀ σ τ : L' ≃ₐ[K] L', σ * τ = τ * σ) :
    (normUnits K L).range ≤ (normUnits K L').range ↔ L' ≤ L := by
  rw [← map_baseUnitsEquiv_normGroup, ← map_baseUnitsEquiv_normGroup,
    Subgroup.map_le_map_iff_of_injective baseUnitsEquiv.injective,
    (localClassFieldTheory K Ω).normGroup_le_normGroup_iff (localClassFieldTheory K Ω).classFieldAxiom
      ((isAbelianExtension_fixingOpenSubgroup_iff L).2 ⟨inferInstance, hL⟩)
      ((isAbelianExtension_fixingOpenSubgroup_iff L').2 ⟨inferInstance, hL'⟩)]
  exact fixingSubgroup_le_fixingSubgroup_iff

end Correspondence

end GroundTheory.LocalField
end

section
noncomputable section

open PowerSeries IsLocalRing ValuativeRel GroundTheory.LocalField.FormalGroup IntermediateField

namespace GroundTheory.LocalField

open Abstract

section Units

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {π : 𝒪[K]}

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem coe_ne_zero_of_irreducible (hπ : Irreducible π) : (π : K) ≠ 0 :=
  fun h => hπ.ne_zero (Subtype.ext h)

def unitUniformizerPow (hπ : Irreducible π) (u : 𝒪[K]ˣ) (k : ℤ) : Kˣ :=
  Units.map (algebraMap 𝒪[K] K : 𝒪[K] →* K) u * Units.mk0 (π : K) (coe_ne_zero_of_irreducible hπ) ^ k

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem coe_unitUniformizerPow_one (hπ : Irreducible π) (u : 𝒪[K]ˣ) :
    ((unitUniformizerPow hπ u 1 : Kˣ) : K) = (((u : 𝒪[K]) * π : 𝒪[K]) : K) := by
  rw [unitUniformizerPow, zpow_one, Units.val_mul, Units.coe_map, Units.val_mk0, Subring.coe_mul]
  rfl

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem unitUniformizerPow_mul (hπ : Irreducible π) (u : 𝒪[K]ˣ) (j : ℤ) :
    unitUniformizerPow hπ u 1 * unitUniformizerPow hπ 1 1 ^ j = unitUniformizerPow hπ u (1 + j) := by
  simp only [unitUniformizerPow, map_one, one_mul, zpow_one, mul_assoc]
  rw [zpow_add, zpow_one]

theorem ord_unitUniformizerPow_one (hπ : Irreducible π) (u : 𝒪[K]ˣ) :
    ord ((unitUniformizerPow hπ u 1 : Kˣ) : K) = 1 := by
  rw [coe_unitUniformizerPow_one, Subring.coe_mul, ord_mul (by simp) (coe_ne_zero_of_irreducible hπ),
    ord_unit, ord_uniformizer hπ, zero_add]

end Units

section Main

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]} (hf : IsLubinTateSeries π f)

attribute [local instance] isDiscreteModule_units

include hπ hf in

theorem exists_lubinTate_frobenius {n : ℕ} (hn : 0 < n) (w : 𝒪[K]ˣ) :
    ∃ σ : Ω ≃ₐ[K] Ω, unramifiedDegree K Ω σ = Multiplicative.ofAdd 1 ∧
      ∀ x ∈ lubinTateTorsion Ω (hπ := hπ) hf n,
        lubinTateGalPointMap (hπ := hπ) hf σ x = ((w⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) • x := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  let ρ0 : lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n :=
    (lubinTateGalEquiv hπ hf n).symm
      (Units.map (Ideal.Quotient.mk (Ideal.span {π ^ n})).toMonoidHom w⁻¹)
  have hτ0 : ∀ y : lubinTateField Ω hπ hf n, ρ0.liftNormal Ω (y : Ω) = (ρ0 y : Ω) :=
    fun y => ρ0.liftNormal_commutes Ω y
  have hmap := map_unramifiedDegree_fixingSubgroup (K := K) (Ω := Ω) (lubinTateField Ω hπ hf n)
  rw [residueDegree_lubinTateField hπ hf hn] at hmap
  have hmem : (unramifiedDegree K Ω (ρ0.liftNormal Ω))⁻¹ * Multiplicative.ofAdd 1 ∈
      (lubinTateField Ω hπ hf n).fixingSubgroup.map (unramifiedDegree K Ω) := by
    rw [hmap]
    exact ⟨_, pow_one _⟩
  obtain ⟨ρ1, hρ1, hρ1d⟩ := Subgroup.mem_map.mp hmem
  refine ⟨ρ0.liftNormal Ω * ρ1, by rw [map_mul, hρ1d, mul_inv_cancel_left], fun x hx => ?_⟩
  apply IdealPoint.ext
  have hxE := val_mem_lubinTateField hπ hf hx
  rw [lubinTateGalPointMap_val, AlgEquiv.mul_apply,
    (mem_fixingSubgroup_iff (K := lubinTateField Ω hπ hf n) ρ1).mp hρ1 _ hxE]
  change ρ0.liftNormal Ω ((⟨x.val, hxE⟩ : lubinTateField Ω hπ hf n) : Ω) = _
  rw [hτ0]
  refine lubinTateGalEquiv_spec hf n ρ0 x hx _ ?_
  simp [ρ0]

include hπ hf in

theorem apply_root_eq_psEval (m : ℕ) (w : 𝒪[K]ˣ) (σ : Ω ≃ₐ[K] Ω)
    (hσ : ∀ x ∈ lubinTateTorsion Ω (hπ := hπ) hf (m + 1),
      lubinTateGalPointMap (hπ := hπ) hf σ x = ((w⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) • x) {l : Ω}
    (hl : Polynomial.aeval l ((ltEisenstein π m).map (algebraMap 𝒪[K] K)) = 0) :
    σ l = psEval (lubinTateHom hπ (isLubinTateSeries_ltPoly π) (isLubinTateSeries_ltPoly π)
      ((w⁻¹ : 𝒪[K]ˣ) : 𝒪[K])).toPowerSeries fun _ => l := by
  have hl' : Polynomial.aeval l ((ltPolyIter π (m + 1)).map (algebraMap 𝒪[K] K)) = 0 := by
    rw [ltPolyIter_succ_eq_mul, Polynomial.map_mul, map_mul, hl, mul_zero]
  let lpt : IdealPoint Ω (lubinTateFormalGroup hπ (isLubinTateSeries_ltPoly π)) :=
    IdealPoint.mk l (valuation_lt_one_of_aeval_ltPolyIter_eq_zero hπ (m + 1) hl')
  have hlt : lpt ∈ lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) (m + 1) :=
    (mem_lubinTateTorsion_ltPoly_iff (m + 1) lpt).mpr hl'
  have he := (lubinTatePointEquiv_mem_torsion_iff hf (isLubinTateSeries_ltPoly π) (m + 1) lpt).mpr hlt
  have h1 := hσ _ he
  have hcomm : lubinTateGalPointMap hf σ (lubinTatePointEquiv hf (isLubinTateSeries_ltPoly π) lpt) =
      lubinTatePointEquiv hf (isLubinTateSeries_ltPoly π)
        (lubinTateGalPointMap (isLubinTateSeries_ltPoly π) σ lpt) := by
    apply IdealPoint.ext
    rw [lubinTateGalPointMap_val, lubinTatePointEquiv_val, lubinTatePointEquiv_val,
      lubinTateGalPointMap_val, algEquiv_psEval σ _ _ fun _ => lpt.valuation_lt_one]
  have h2 := (lubinTatePointEquiv hf (isLubinTateSeries_ltPoly π)).injective
    (hcomm.symm.trans (h1.trans (map_smul _ _ _).symm))
  have h3 := congrArg IdealPoint.val h2
  rwa [lubinTateGalPointMap_val, lubinTate_smul_val] at h3

end Main

section Frobenius

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]} (hf : IsLubinTateSeries π f)

attribute [local instance] isDiscreteModule_units

omit [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] in

theorem inertiaDegree_unramifiedDegree_top :
    inertiaDegree (unramifiedDegree K Ω) (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) = 1 := by
  rw [inertiaDegree, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top_of_surjective _ unramifiedDegree_surjective, Subgroup.index_top]

include hπ hf in

theorem ramificationIndex_fixingSubgroup_lubinTateField {n : ℕ} (hn : 0 < n) :
    Abstract.ramificationIndex (unramifiedDegree K Ω) (lubinTateField Ω hπ hf n).fixingSubgroup =
      Module.finrank K (lubinTateField Ω hπ hf n) := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have h := index_eq_mul unramifiedDegree_surjective (lubinTateField Ω hπ hf n).fixingSubgroup
  rw [inertiaDegree_unramifiedDegree_fixingSubgroup, residueDegree_lubinTateField hπ hf hn,
    mul_one, ← finrank_eq_fixingSubgroup_index] at h
  exact h.symm

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [IsSepClosure K Ω] in

theorem norm_neg_gen_eq_coeff_zero {x : Ω} (hint : IsIntegral K x) :
    Algebra.norm K (-AdjoinSimple.gen K x) = (minpoly K x).coeff 0 := by
  set pb := adjoin.powerBasis hint
  have hdim : pb.dim = (minpoly K x).natDegree := by
    rw [adjoin.powerBasis_dim]
  have hnorm : Algebra.norm K pb.gen = (-1) ^ (minpoly K x).natDegree * (minpoly K x).coeff 0 := by
    rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, hdim, adjoin.powerBasis_gen,
      minpoly_gen]
  have h1 : (-1 : K⟮x⟯) = algebraMap K K⟮x⟯ (-1) := by simp
  rw [← adjoin.powerBasis_gen hint, neg_eq_neg_one_mul, h1, map_mul, Algebra.norm_algebraMap, hnorm,
    ← adjoin.finrank hint, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

include hπ hf in
set_option maxHeartbeats 1000000 in

theorem reciprocity_frobenius_lubinTate (m : ℕ) (U : OpenSubgroup (Ω ≃ₐ[K] Ω))
    [((U : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).Normal]
    (hUH : (U : Subgroup (Ω ≃ₐ[K] Ω)) ≤ (lubinTateField Ω hπ hf (m + 1)).fixingSubgroup)
    (hHU : (lubinTateField Ω hπ hf (m + 1)).fixingSubgroup ⊓ (unramifiedDegree K Ω).ker ≤ U)
    (w : 𝒪[K]ˣ) (σ : Ω ≃ₐ[K] Ω) (hσd : unramifiedDegree K Ω σ = Multiplicative.ofAdd 1)
    (hσ : ∀ x ∈ lubinTateTorsion Ω (hπ := hπ) hf (m + 1),
      lubinTateGalPointMap (hπ := hπ) hf σ x = ((w⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) • x) :
    (localClassFieldTheory K Ω).reciprocity (le_top : U ≤ ⊤)
        (localClassFieldTheory K Ω).classFieldAxiom (QuotientGroup.mk ⟨σ, by simp⟩) =
      QuotientGroup.mk (baseUnitsEquiv.symm (unitUniformizerPow hπ w 1)) := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K

  have hinert : inertiaDegree (localClassFieldTheory K Ω).deg
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) = 1 := by
    rw [localClassFieldTheory_deg]
    exact inertiaDegree_unramifiedDegree_top
  let s : (localClassFieldTheory K Ω).FrobeniusLift ⊤ :=
    { elt := σ
      mem := by simp
      deg := 1
      deg_pos := one_pos
      deg_eq := by rw [hinert, localClassFieldTheory_deg, hσd]; simp }

  obtain ⟨l, hlE, hl⟩ := exists_lubinTateField_eq_adjoin_eisenstein (Ω := Ω) hπ hf m
  obtain ⟨x, hxP, hσx, hτx⟩ := exists_fixed_root_ltEisenstein hπ w m σ hσd hl
    (apply_root_eq_psEval hπ hf m w σ hσ hl)
  have hwπ : ((w : 𝒪[K]) * π : 𝒪[K]) ≠ 0 := mul_ne_zero w.ne_zero hπ.ne_zero
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [Polynomial.aeval_def, Polynomial.eval₂_at_zero, Polynomial.coeff_map,
      coeff_zero_ltEisenstein, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective K Ω),
      map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective 𝒪[K] K)] at hxP
    exact hwπ hxP

  have hy : (-(Units.mk0 x hx0) : Ωˣ) ∈
      fixedModule Ωˣ ((s.field U le_top : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) := by
    rw [ClassFieldData.FrobeniusLift.coe_field]
    refine mem_fixedModule_frobeniusClosure.mpr ⟨?_, ?_⟩
    · rw [mem_fixedModule_units_iff']
      intro g hg
      obtain ⟨hgU, hgk⟩ := Subgroup.mem_inf.mp hg
      have hgker : g ∈ (maximalUnramifiedExtension K Ω).fixingSubgroup := by
        rw [← ker_unramifiedDegree]
        exact hgk
      have hgl : g l = l := (mem_fixingSubgroup_iff _ g).mp (hUH hgU) l
        (hlE ▸ mem_adjoin_simple_self K l)
      have hgx := hτx g (fun y hy => (mem_fixingSubgroup_iff _ g).mp hgker y hy) hgl
      rw [Units.val_neg, Units.val_mk0, map_neg, hgx]
    · apply Units.ext
      change σ ((-(Units.mk0 x hx0) : Ωˣ) : Ω) = ((-(Units.mk0 x hx0) : Ωˣ) : Ω)
      rw [Units.val_neg, Units.val_mk0, map_neg, hσx]

  set S := s.field U le_top with hS
  have hFfix : (fixedField ((S : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).fixingSubgroup =
      (S : Subgroup (Ω ≃ₐ[K] Ω)) :=
    fixingSubgroup_fixedField_openSubgroup S
  have hxF : x ∈ fixedField ((S : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) := by
    rw [mem_fixedField_iff]
    intro g hg
    have h1 := (mem_fixedModule_units_iff' _ _).mp hy g hg
    rw [Units.val_neg, Units.val_mk0, map_neg, neg_inj] at h1
    exact h1
  have hπ' : Irreducible ((w : 𝒪[K]) * π) := (irreducible_units_mul w).2 hπ
  have hq := one_lt_card_residueField' K
  have hdeg : 0 < (ltEisenstein ((w : 𝒪[K]) * π) m).natDegree := by
    rw [(ltEisenstein_monic _ m).2]
    exact Nat.mul_pos (by omega) (pow_pos (by omega) m)
  have hmon := (ltEisenstein_monic ((w : 𝒪[K]) * π) m).1
  have hint : IsIntegral K x := ⟨_, hmon.map _, hxP⟩
  have hmin : minpoly K x = (ltEisenstein ((w : 𝒪[K]) * π) m).map (algebraMap 𝒪[K] K) :=
    (minpoly.eq_of_irreducible_of_monic
      (irreducible_map_of_isEisensteinAt (isEisensteinAt_ltEisenstein hπ' m) hdeg) hxP
      (hmon.map _)).symm
  have hindex : (S : Subgroup (Ω ≃ₐ[K] Ω)).index = (ltEisenstein ((w : 𝒪[K]) * π) m).natDegree := by
    have hinf : (U : Subgroup (Ω ≃ₐ[K] Ω)) ⊓ (unramifiedDegree K Ω).ker =
        (lubinTateField Ω hπ hf (m + 1)).fixingSubgroup ⊓ (unramifiedDegree K Ω).ker :=
      le_antisymm (inf_le_inf_right _ hUH) (le_inf hHU inf_le_right)
    have hSk := ClassFieldData.FrobeniusLift.field_inf_ker le_top s (L := U)
    rw [localClassFieldTheory_deg] at hSk
    rw [index_eq_mul (localClassFieldTheory K Ω).surjective_deg,
      ClassFieldData.FrobeniusLift.inertiaDegree_field, hinert, mul_one, mul_one,
      Abstract.ramificationIndex, localClassFieldTheory_deg, ← Subgroup.inf_relIndex_right, hSk, hinf,
      Subgroup.inf_relIndex_right, ← Abstract.ramificationIndex,
      ramificationIndex_fixingSubgroup_lubinTateField hπ hf (Nat.succ_pos m),
      finrank_lubinTateField hπ hf (Nat.succ_pos m), (ltEisenstein_monic _ m).2, Nat.succ_sub_one]
  have hFeq : K⟮x⟯ = fixedField ((S : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) := by
    refine eq_of_le_of_finrank_eq (adjoin_simple_le_iff.mpr hxF) ?_
    rw [adjoin.finrank hint, hmin, Polynomial.natDegree_map_eq_of_injective
      (FaithfulSMul.algebraMap_injective 𝒪[K] K), finrank_eq_fixingSubgroup_index, hFfix, hindex]

  have hnegxF : -x ∈ fixedField ((S : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) :=
    neg_mem hxF
  have hnormF : Algebra.norm K
      (⟨-x, hnegxF⟩ : fixedField ((S : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) =
      (((w : 𝒪[K]) * π : 𝒪[K]) : K) := by
    have he : IntermediateField.equivOfEq hFeq (-AdjoinSimple.gen K x) = ⟨-x, hnegxF⟩ :=
      Subtype.ext (by simp)
    rw [← he, Algebra.norm_eq_of_algEquiv, norm_neg_gen_eq_coeff_zero hint, hmin,
      Polynomial.coeff_map, coeff_zero_ltEisenstein]
    rfl
  have hfi : ((fixedField ((S : OpenSubgroup (Ω ≃ₐ[K] Ω)) :
      Subgroup (Ω ≃ₐ[K] Ω))).fixingSubgroup.subgroupOf ⊤).FiniteIndex := by
    rw [hFfix]
    infer_instance
  let a : fixedModule Ωˣ ((S : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) :=
    ⟨-(Units.mk0 x hx0), hy⟩
  have hnorm : baseUnitsEquiv (norm Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω))
      ((S : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) a) = unitUniformizerPow hπ w 1 := by
    apply Units.ext
    apply (algebraMap K Ω).injective
    rw [algebraMap_baseUnitsEquiv, coe_norm_congr rfl hFfix.symm, coe_norm_top,
      coe_unitUniformizerPow_one, ← hnormF]
    congr 2

  have hval : (localClassFieldTheory K Ω).valuation S a = Multiplicative.ofAdd 1 := by
    rw [ClassFieldData.valuation_eq_iff, ClassFieldData.FrobeniusLift.inertiaDegree_field, hinert]
    apply Multiplicative.toAdd.injective
    rw [localClassFieldTheory_val_apply, hnorm, ord_unitUniformizerPow_one]
    simp [s]
  have key := (localClassFieldTheory K Ω).reciprocity_mk_eq_norm (le_top : U ≤ ⊤)
    (localClassFieldTheory K Ω).classFieldAxiom s hval
  refine key.trans ?_
  congr 1
  apply baseUnitsEquiv.injective
  rw [MulEquiv.apply_symm_apply]
  exact hnorm

include hπ hf in

theorem reciprocity_lubinTate {n : ℕ} (hn : 0 < n) (U : OpenSubgroup (Ω ≃ₐ[K] Ω))
    [((U : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).Normal]
    (hUH : (U : Subgroup (Ω ≃ₐ[K] Ω)) ≤ (lubinTateField Ω hπ hf n).fixingSubgroup)
    (hHU : (lubinTateField Ω hπ hf n).fixingSubgroup ⊓ (unramifiedDegree K Ω).ker ≤ U)
    (u : 𝒪[K]ˣ) (k : ℤ) (τ : Ω ≃ₐ[K] Ω)
    (hτd : unramifiedDegree K Ω τ = Multiplicative.ofAdd (k : ℤ̂))
    (hτ : ∀ x ∈ lubinTateTorsion Ω (hπ := hπ) hf n,
      lubinTateGalPointMap (hπ := hπ) hf τ x = ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) • x) :
    (localClassFieldTheory K Ω).reciprocity (le_top : U ≤ ⊤)
        (localClassFieldTheory K Ω).classFieldAxiom (QuotientGroup.mk ⟨τ, by simp⟩) =
      QuotientGroup.mk (baseUnitsEquiv.symm (unitUniformizerPow hπ u k)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
  obtain ⟨σu, hσud, hσu⟩ := exists_lubinTate_frobenius (Ω := Ω) hπ hf hn u
  obtain ⟨σ1, hσ1d, hσ1⟩ := exists_lubinTate_frobenius (Ω := Ω) hπ hf hn 1

  have hσ1H : σ1 ∈ (lubinTateField Ω hπ hf (m + 1)).fixingSubgroup := by
    rw [lubinTateField, mem_fixingSubgroup_adjoin_iff]
    rintro _ ⟨x, hx, rfl⟩
    have h := congrArg IdealPoint.val (hσ1 x hx)
    rwa [lubinTateGalPointMap_val, inv_one, Units.val_one, one_smul] at h

  have hcls : (QuotientGroup.mk ⟨τ, by simp⟩ : ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω)) ⧸
      (U : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))) =
      QuotientGroup.mk ⟨σu, by simp⟩ * (QuotientGroup.mk ⟨σ1, by simp⟩) ^ (k - 1) := by
    rw [← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    apply hHU
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [lubinTateField, mem_fixingSubgroup_adjoin_iff]
      rintro _ ⟨x, hx, rfl⟩
      have hxE := val_mem_lubinTateField hπ hf hx
      have h1 : (σ1 ^ (k - 1)) x.val = x.val :=
        (mem_fixingSubgroup_iff _ _).mp (Subgroup.zpow_mem _ hσ1H (k - 1)) x.val hxE
      have h2 : τ x.val = σu x.val := by
        have e1 := congrArg IdealPoint.val (hτ x hx)
        have e2 := congrArg IdealPoint.val (hσu x hx)
        rw [lubinTateGalPointMap_val] at e1 e2
        rw [e1, e2]
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h1, ← h2]
      exact τ.symm_apply_apply x.val
    · rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_zpow, hτd, hσud, hσ1d]
      apply Multiplicative.toAdd.injective
      simp only [toAdd_mul, toAdd_inv, toAdd_zpow, toAdd_ofAdd, toAdd_one, zsmul_eq_mul]
      push_cast
      ring
  rw [hcls, map_mul, map_zpow,
    reciprocity_frobenius_lubinTate hπ hf m U hUH hHU u σu hσud hσu,
    reciprocity_frobenius_lubinTate hπ hf m U hUH hHU 1 σ1 hσ1d hσ1,
    ← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul, ← map_zpow, ← map_mul, unitUniformizerPow_mul,
    add_sub_cancel]

include hπ hf in

theorem exists_lubinTate_action {n : ℕ} (hn : 0 < n) (u : 𝒪[K]ˣ) (k : ℤ) :
    ∃ τ : Ω ≃ₐ[K] Ω, unramifiedDegree K Ω τ = Multiplicative.ofAdd (k : ℤ̂) ∧
      ∀ x ∈ lubinTateTorsion Ω (hπ := hπ) hf n,
        lubinTateGalPointMap (hπ := hπ) hf τ x = ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) • x := by
  obtain ⟨σu, hσud, hσu⟩ := exists_lubinTate_frobenius (Ω := Ω) hπ hf hn u
  obtain ⟨σ1, hσ1d, hσ1⟩ := exists_lubinTate_frobenius (Ω := Ω) hπ hf hn 1
  have hσ1x : ∀ x ∈ lubinTateTorsion Ω (hπ := hπ) hf n, σ1 x.val = x.val := fun x hx => by
    have h := congrArg IdealPoint.val (hσ1 x hx)
    rwa [lubinTateGalPointMap_val, inv_one, Units.val_one, one_smul] at h
  have hσ1H : σ1 ∈ (lubinTateField Ω hπ hf n).fixingSubgroup := by
    rw [lubinTateField, mem_fixingSubgroup_adjoin_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact hσ1x x hx
  refine ⟨σu * σ1 ^ (k - 1), ?_, fun x hx => ?_⟩
  · rw [map_mul, map_zpow, hσud, hσ1d]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul]
    push_cast
    ring
  · apply IdealPoint.ext
    have h1 : (σ1 ^ (k - 1)) x.val = x.val :=
      (mem_fixingSubgroup_iff _ _).mp (Subgroup.zpow_mem _ hσ1H (k - 1)) x.val
        (val_mem_lubinTateField hπ hf hx)
    have e := congrArg IdealPoint.val (hσu x hx)
    rw [lubinTateGalPointMap_val] at e ⊢
    rw [AlgEquiv.mul_apply, h1, e]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] in

theorem normal_subgroupOf_fixingOpenSubgroup (M : IntermediateField K Ω) [FiniteDimensional K M]
    [IsGalois K M] :
    ((fixingOpenSubgroup M : Subgroup (Ω ≃ₐ[K] Ω)).subgroupOf
      ((⊤ : OpenSubgroup (Ω ≃ₐ[K] Ω)) : Subgroup (Ω ≃ₐ[K] Ω))).Normal := by
  rw [coe_fixingOpenSubgroup]
  infer_instance

include hπ hf in

theorem reciprocity_lubinTate_sup {n : ℕ} (hn : 0 < n) (E : IntermediateField K Ω)
    [FiniteDimensional K E] [IsGalois K E] (hE : E ≤ maximalUnramifiedExtension K Ω)
    (u : 𝒪[K]ˣ) (k : ℤ) (τ : Ω ≃ₐ[K] Ω)
    (hτd : unramifiedDegree K Ω τ = Multiplicative.ofAdd (k : ℤ̂))
    (hτ : ∀ x ∈ lubinTateTorsion Ω (hπ := hπ) hf n,
      lubinTateGalPointMap (hπ := hπ) hf τ x = ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) • x) :
    have : IsSepClosed Ω := IsSepClosure.sep_closed K
    have := normal_subgroupOf_fixingOpenSubgroup (lubinTateField Ω hπ hf n ⊔ E)
    (localClassFieldTheory K Ω).reciprocity
        (le_top : fixingOpenSubgroup (lubinTateField Ω hπ hf n ⊔ E) ≤ ⊤)
        (localClassFieldTheory K Ω).classFieldAxiom (QuotientGroup.mk ⟨τ, by simp⟩) =
      QuotientGroup.mk (baseUnitsEquiv.symm (unitUniformizerPow hπ u k)) := by
  intro _ _
  refine reciprocity_lubinTate hπ hf hn _ ?_ ?_ u k τ hτd hτ
  · rw [coe_fixingOpenSubgroup]
    exact fixingSubgroup_antitone le_sup_left
  · rw [coe_fixingOpenSubgroup, fixingSubgroup_sup, ker_unramifiedDegree]
    exact inf_le_inf_left _ (fixingSubgroup_antitone hE)

end Frobenius

end GroundTheory.LocalField
end
end

section
noncomputable section

open IntermediateField Topology Filter

namespace GroundTheory.LocalField

open ValuativeRel GroundTheory.LocalField.Abstract

namespace FormalGroup

section UnramifiedTower

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosed Ω]

variable (K Ω) in

def unramifiedTowerRoot (k : ℕ) : Ω :=
  Classical.choose (exists_isPrimitiveRoot_card_pow_sub_one (K := K) (Ksep := Ω)
    (Nat.factorial_ne_zero (k + 1)))

theorem isPrimitiveRoot_unramifiedTowerRoot (k : ℕ) :
    IsPrimitiveRoot (unramifiedTowerRoot K Ω k) (Nat.card 𝓀[K] ^ (k + 1).factorial - 1) := by
  unfold unramifiedTowerRoot
  exact Classical.choose_spec (exists_isPrimitiveRoot_card_pow_sub_one (K := K) (Ksep := Ω)
    (Nat.factorial_ne_zero (k + 1)))

variable (K Ω) in

def unramifiedTower (k : ℕ) : IntermediateField K Ω := K⟮unramifiedTowerRoot K Ω k⟯

theorem isUnramifiedSubextension_unramifiedTower (k : ℕ) :
    IsUnramifiedSubextension (unramifiedTower K Ω k) :=
  (isUnramifiedSubextension_adjoin (Nat.factorial_ne_zero _)
    (isPrimitiveRoot_unramifiedTowerRoot (K := K) (Ω := Ω) k)).1

theorem finrank_unramifiedTower (k : ℕ) :
    Module.finrank K (unramifiedTower K Ω k) = (k + 1).factorial :=
  (isUnramifiedSubextension_adjoin (Nat.factorial_ne_zero _)
    (isPrimitiveRoot_unramifiedTowerRoot (K := K) (Ω := Ω) k)).2

theorem le_unramifiedTower_of_isUnramifiedSubextension {E : IntermediateField K Ω}
    (hE : IsUnramifiedSubextension E) {k : ℕ} (hk : Module.finrank K E ≤ k + 1) :
    E ≤ unramifiedTower K Ω k := by
  have := hE.1
  exact hE.le_adjoin (Nat.factorial_ne_zero _)
    (Nat.dvd_factorial Module.finrank_pos hk) (isPrimitiveRoot_unramifiedTowerRoot k)

theorem monotone_unramifiedTower : Monotone (unramifiedTower K Ω) := fun j k h => by
  have := (isUnramifiedSubextension_unramifiedTower (K := K) (Ω := Ω) j).1
  exact (isUnramifiedSubextension_unramifiedTower j).le_adjoin (Nat.factorial_ne_zero _)
    (by rw [finrank_unramifiedTower]; exact Nat.factorial_dvd_factorial (Nat.succ_le_succ h))
    (isPrimitiveRoot_unramifiedTowerRoot k)

theorem unramifiedTower_le_maximalUnramifiedExtension (k : ℕ) :
    unramifiedTower K Ω k ≤ maximalUnramifiedExtension K Ω :=
  (isUnramifiedSubextension_unramifiedTower k).le_maximalUnramifiedExtension

theorem exists_mem_unramifiedTower {x : Ω} (hx : x ∈ maximalUnramifiedExtension K Ω) :
    ∃ k, x ∈ unramifiedTower K Ω k := by
  obtain ⟨E, hE, hxE⟩ := mem_maximalUnramifiedExtension_iff.mp hx
  exact ⟨Module.finrank K E, le_unramifiedTower_of_isUnramifiedSubextension hE (Nat.le_succ _) hxE⟩

instance (k : ℕ) : IsGalois K (unramifiedTower K Ω k) :=
  (isUnramifiedSubextension_unramifiedTower k).isGalois

end UnramifiedTower

section MaxUnramified

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsSepClosed Ω]
variable {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]}

abbrev towerSup (hf : IsLubinTateSeries π f) (k : ℕ) : IntermediateField K Ω :=
  lubinTateField Ω hπ hf (k + 1) ⊔ unramifiedTower K Ω k

theorem monotone_towerSup (hf : IsLubinTateSeries π f) : Monotone (towerSup (Ω := Ω) hπ hf) :=
  fun _ _ h => sup_le_sup (lubinTateField_mono hπ hf (Nat.succ_le_succ h))
    (monotone_unramifiedTower h)

variable (Ω) in

abbrev lubinTateMaxUnramified (hπ : Irreducible π) : IntermediateField K Ω :=
  lubinTateLimit Ω hπ ⊔ maximalUnramifiedExtension K Ω

theorem towerSup_le (hf : IsLubinTateSeries π f) (k : ℕ) :
    towerSup (Ω := Ω) hπ hf k ≤ lubinTateMaxUnramified Ω hπ :=
  sup_le_sup (lubinTateField_le_lubinTateLimit hπ hf _) (unramifiedTower_le_maximalUnramifiedExtension k)

theorem exists_mem_towerSup (hf : IsLubinTateSeries π f) {x : Ω}
    (hx : x ∈ lubinTateMaxUnramified Ω hπ) : ∃ k, x ∈ towerSup hπ hf k := by
  have hle : lubinTateMaxUnramified Ω hπ ≤ ⨆ k, towerSup hπ hf k := by
    refine sup_le ?_ ?_
    · rw [lubinTateLimit_eq hπ hf]
      refine iSup_le fun n => ?_
      exact (lubinTateField_mono hπ hf n.le_succ).trans
        ((le_sup_left : _ ≤ towerSup hπ hf n).trans (le_iSup (towerSup hπ hf) n))
    · intro y hy
      obtain ⟨k, hk⟩ := exists_mem_unramifiedTower hy
      exact (le_iSup (towerSup hπ hf) k) ((le_sup_right : _ ≤ towerSup hπ hf k) hk)
  have := hle hx
  rw [← SetLike.mem_coe, IntermediateField.coe_iSup_of_directed
    (monotone_towerSup hπ hf).directed_le] at this
  simpa only [Set.mem_iUnion, SetLike.mem_coe] using this

def lubinTateMaxUnramifiedRestrict :
    (lubinTateMaxUnramified Ω hπ ≃ₐ[K] lubinTateMaxUnramified Ω hπ) →*
      (lubinTateLimit Ω hπ ≃ₐ[K] lubinTateLimit Ω hπ) ×
        (maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω) :=
  (restrictAut le_sup_left).prod (restrictAut le_sup_right)

theorem lubinTateMaxUnramifiedRestrict_injective :
    Function.Injective (lubinTateMaxUnramifiedRestrict (Ω := Ω) hπ) := fun _ _ h =>
  algEquiv_ext_sup (congrArg Prod.fst h) (congrArg Prod.snd h)

theorem lubinTateMaxUnramifiedRestrict_surjective (hf : IsLubinTateSeries π f) :
    Function.Surjective (lubinTateMaxUnramifiedRestrict (Ω := Ω) hπ) := by
  rintro ⟨τ₁, τ₂⟩
  have hK : ∀ k, lubinTateField Ω hπ hf (k + 1) ≤ lubinTateLimit Ω hπ := fun k =>
    lubinTateField_le_lubinTateLimit hπ hf _
  have hE : ∀ k, unramifiedTower K Ω k ≤ maximalUnramifiedExtension K Ω :=
    unramifiedTower_le_maximalUnramifiedExtension
  have hσ := fun k => (bijective_restrictAut_prod hπ hf (Nat.succ_pos k)
    (isUnramifiedSubextension_unramifiedTower (K := K) (Ω := Ω) k)).2
      (restrictAut (hK k) τ₁, restrictAut (hE k) τ₂)
  choose σ hσ using hσ
  have hσ₁ : ∀ k, restrictAut le_sup_left (σ k) = restrictAut (hK k) τ₁ := fun k =>
    congrArg Prod.fst (hσ k)
  have hσ₂ : ∀ k, restrictAut le_sup_right (σ k) = restrictAut (hE k) τ₂ := fun k =>
    congrArg Prod.snd (hσ k)
  have hcompat : ∀ j k (h : j ≤ k), restrictAut (monotone_towerSup hπ hf h) (σ k) = σ j := by
    intro j k h
    apply algEquiv_ext_sup
    · rw [restrictAut_restrictAut, hσ₁ j,
        ← restrictAut_restrictAut (le_sup_left : _ ≤ towerSup hπ hf k)
          (lubinTateField_mono hπ hf (Nat.succ_le_succ h)),
        hσ₁ k, restrictAut_restrictAut]
    · rw [restrictAut_restrictAut, hσ₂ j,
        ← restrictAut_restrictAut (le_sup_right : _ ≤ towerSup hπ hf k)
          (monotone_unramifiedTower h), hσ₂ k, restrictAut_restrictAut]
  obtain ⟨ρ, hρ⟩ := exists_algEquiv_of_compatible (monotone_towerSup hπ hf) (towerSup_le hπ hf)
    (fun _ hx => exists_mem_towerSup hπ hf hx) σ hcompat
  refine ⟨ρ, Prod.ext ?_ ?_⟩
  · refine algEquiv_ext_of_restrictAut (F := fun k => lubinTateField Ω hπ hf (k + 1)) hK
      (fun x hx => ?_) fun k => ?_
    · obtain ⟨n, hn⟩ := (mem_lubinTateLimit_iff hπ hf).mp hx
      exact ⟨n, lubinTateField_mono hπ hf n.le_succ hn⟩
    · change restrictAut (hK k) (restrictAut le_sup_left ρ) = _
      rw [restrictAut_restrictAut,
        ← restrictAut_restrictAut (towerSup_le hπ hf k) (le_sup_left : _ ≤ towerSup hπ hf k),
        hρ k, hσ₁ k]
  · refine algEquiv_ext_of_restrictAut (F := unramifiedTower K Ω) hE
      (fun x hx => exists_mem_unramifiedTower hx) fun k => ?_
    change restrictAut (hE k) (restrictAut le_sup_right ρ) = _
    rw [restrictAut_restrictAut,
      ← restrictAut_restrictAut (towerSup_le hπ hf k) (le_sup_right : _ ≤ towerSup hπ hf k),
      hρ k, hσ₂ k]

variable [IsGalois K Ω]

def lubinTateMaxUnramifiedGalEquiv (hf : IsLubinTateSeries π f) :
    (lubinTateMaxUnramified Ω hπ ≃ₐ[K] lubinTateMaxUnramified Ω hπ) ≃ₜ*
      𝒪[K]ˣ × Multiplicative ℤ̂ :=
  let e := (MulEquiv.ofBijective (lubinTateMaxUnramifiedRestrict (Ω := Ω) hπ)
    ⟨lubinTateMaxUnramifiedRestrict_injective hπ, lubinTateMaxUnramifiedRestrict_surjective hπ hf⟩).trans
      (MulEquiv.prodCongr (lubinTateLimitGalEquiv hπ hf).symm.toMulEquiv
        (maximalUnramifiedExtensionGaloisEquiv K Ω).toMulEquiv)
  have hc : Continuous e :=
    (((lubinTateLimitGalEquiv hπ hf).symm.continuous.comp (continuous_restrictAut le_sup_left)).prodMk
      ((maximalUnramifiedExtensionGaloisEquiv K Ω).continuous.comp
        (continuous_restrictAut le_sup_right)))
  { e with
    continuous_toFun := hc
    continuous_invFun := (hc.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }

end MaxUnramified

end FormalGroup

end GroundTheory.LocalField
end
end

section
noncomputable section

open ValuativeRel GroundTheory.LocalField.FormalGroup

namespace GroundTheory.LocalField

open Abstract

section LubinTate

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [IsSepClosure K Ω]
  {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]} (hf : IsLubinTateSeries π f)

attribute [local instance] isDiscreteModule_units

theorem lubinTateField_mul_comm (n : ℕ)
    (σ τ : lubinTateField Ω hπ hf n ≃ₐ[K] lubinTateField Ω hπ hf n) : σ * τ = τ * σ := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  apply (lubinTateGalEquiv hπ hf n).injective
  rw [map_mul, map_mul]
  exact mul_comm (G := (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ) _ _

include hf in

theorem mem_unitFiltration_of_mem_range_normUnits {n : ℕ} (hn : 0 < n) (u : 𝒪[K]ˣ) (k : ℤ)
    (h : unitUniformizerPow hπ u k ∈ (normUnits K (lubinTateField Ω hπ hf n)).range) :
    u ∈ unitFiltration K n := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  set T := lubinTateField Ω hπ hf n
  have hab : IsAbelianExtension ⊤ (fixingOpenSubgroup T) :=
    (isAbelianExtension_fixingOpenSubgroup_iff T).2 ⟨inferInstance, lubinTateField_mul_comm hπ hf n⟩
  have := hab.normal
  obtain ⟨τ, hτd, hτ⟩ := exists_lubinTate_action (Ω := Ω) hπ hf hn u k
  have hr := reciprocity_lubinTate hπ hf hn (fixingOpenSubgroup T)
    (by rw [coe_fixingOpenSubgroup]) (by rw [coe_fixingOpenSubgroup]; exact inf_le_left) u k τ hτd hτ
  have hmem : τ ∈ (fixingOpenSubgroup T : Subgroup (Ω ≃ₐ[K] Ω)) := by
    refine ((localClassFieldTheory K Ω).mem_normGroup_iff_of_reciprocity
      (localClassFieldTheory K Ω).classFieldAxiom hab hr).1 ?_
    rw [mem_normGroup_iff_mem_range_normUnits, MulEquiv.apply_symm_apply]
    exact h
  rw [coe_fixingOpenSubgroup] at hmem

  have hchar := lubinTateChar_eq_of_apply hπ hf (le_refl T) 1 ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) fun x hx => by
    have e := congrArg IdealPoint.val (hτ x hx)
    rw [lubinTateGalPointMap_val] at e
    rw [← e, AlgEquiv.one_apply]
    exact ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem _
      (val_mem_lubinTateField hπ hf hx)).symm
  rw [map_one, Units.val_one] at hchar
  have h1 : unitsMk π n u⁻¹ = 1 := Units.ext (by rw [coe_unitsMk, Units.val_one, hchar])
  exact inv_mem_iff.1 ((unitsMk_eq_one_iff hπ).1 h1)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω]
  [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω] in

theorem range_normUnits_anti {L L' : IntermediateField K Ω} [FiniteDimensional K L]
    [FiniteDimensional K L'] (h : L ≤ L') : (normUnits K L').range ≤ (normUnits K L).range := by
  rw [← map_baseUnitsEquiv_normGroup, ← map_baseUnitsEquiv_normGroup]
  exact Subgroup.map_mono (normGroup_mono (fixingOpenSubgroup_anti h) le_top)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem unitUniformizerPow_eq (u : 𝒪[K]ˣ) (k : ℤ) :
    unitUniformizerPow hπ u k = uniformizerUnit hπ ^ k * unitsIncl K u := by
  rw [unitUniformizerPow, mul_comm]
  rfl

include hf in

theorem range_normUnits_sup_le {n m : ℕ} (hn : 0 < n) {E : IntermediateField K Ω}
    (hE : IsUnramifiedSubextension E) (hmE : m ∣ Module.finrank K E) {H : Subgroup Kˣ}
    (hnH : unitFiltrationUnits K n ≤ H) (hmH : (powMonoidHom m : Kˣ →* Kˣ).range ≤ H) :
    (normUnits K (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω)).range ≤ H := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have := hE.1
  set T := lubinTateField Ω hπ hf n
  set L : IntermediateField K Ω := T ⊔ E
  rintro _ ⟨y, rfl⟩

  have hdvd : m ∣ residueDegree K L := by
    have h1 := residueDegree_dvd_of_le (le_sup_right : E ≤ L)
    rw [residueDegree_eq_finrank_of_unramified K E hE.ramificationIndex_eq_one] at h1
    exact hmE.trans h1
  obtain ⟨j, hj⟩ := hdvd
  obtain ⟨⟨k, u⟩, hx⟩ := (unitsOfIntProd_bijective hπ).2 (normUnits K L y)
  have hk : k.toAdd = (m : ℤ) * ((j : ℤ) * ord ((y : L) : L)) := by
    rw [← ord_unitsOfIntProd hπ k u, hx, coe_normUnits, ord_norm, hj]
    push_cast
    ring
  have hxu : unitUniformizerPow hπ u k.toAdd = normUnits K L y := by
    rw [← hx, unitsOfIntProd_eq, unitUniformizerPow_eq]

  have hT : unitUniformizerPow hπ u k.toAdd ∈ (normUnits K T).range := by
    rw [hxu]
    exact range_normUnits_anti le_sup_left ⟨y, rfl⟩
  have hu := mem_unitFiltration_of_mem_range_normUnits hπ hf hn u k.toAdd hT
  rw [← hxu, unitUniformizerPow_eq]
  refine H.mul_mem (hmH ⟨uniformizerUnit hπ ^ ((j : ℤ) * ord ((y : L) : L)), ?_⟩)
    (hnH ⟨u, hu, rfl⟩)
  rw [powMonoidHom_apply, ← zpow_natCast, ← zpow_mul, hk, mul_comm]

end LubinTate

section Existence

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

attribute [local instance] isDiscreteModule_units

theorem exists_range_normUnits_le (H : Subgroup Kˣ) [H.FiniteIndex] (hH : IsOpen (H : Set Kˣ)) :
    ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L), (normUnits K L).range ≤ H := by
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  obtain ⟨⟨n, hnH⟩, m, hm, hmH⟩ := exists_unitFiltrationUnits_le_and_range_pow_le hH
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hE := isUnramifiedSubextension_unramifiedTower (K := K) (Ω := Ω) m
  have := hE.1
  have hmE : m ∣ Module.finrank K (unramifiedTower K Ω m) := by
    rw [finrank_unramifiedTower]
    exact Nat.dvd_factorial (Nat.pos_of_ne_zero hm) m.le_succ
  exact ⟨_, inferInstance, range_normUnits_sup_le hπ (isLubinTateSeries_ltPoly π) n.succ_pos hE hmE
    ((unitFiltrationUnits_antitone n.le_succ).trans hnH) hmH⟩

theorem isOpen_range_normUnits_and_finiteIndex (L : IntermediateField K Ω) [FiniteDimensional K L] :
    IsOpen ((normUnits K L).range : Set Kˣ) ∧ (normUnits K L).range.FiniteIndex := by
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  have : Algebra.IsSeparable K L := Algebra.isSeparable_tower_bot_of_isSeparable K L Ω
  exact ⟨isOpen_range_normUnits K L, finiteIndex_range_normUnits K L⟩

theorem exists_range_normUnits_eq (H : Subgroup Kˣ) [H.FiniteIndex] (hH : IsOpen (H : Set Kˣ)) :
    ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L), IsGalois K L ∧
      (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) ∧ (normUnits K L).range = H := by
  obtain ⟨L₀, _, hL₀⟩ := exists_range_normUnits_le (Ω := Ω) H hH
  set B := H.comap (baseUnitsEquiv (K := K) (Ω := Ω) :
    fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) →* Kˣ)
  have hB : normGroup Ωˣ ⊤ (fixingOpenSubgroup L₀) ≤ B := by
    rw [normGroup_eq_comap]
    exact Subgroup.comap_mono hL₀
  obtain ⟨U, hU, -, hUB⟩ := (localClassFieldTheory K Ω).exists_normGroup_eq_of_le
    (localClassFieldTheory K Ω).classFieldAxiom le_top hB
  set M := IntermediateField.fixedField (U : Subgroup (Ω ≃ₐ[K] Ω))
  have hMU : fixingOpenSubgroup M = U := fixingOpenSubgroup_fixedField U
  rw [← hMU] at hU hUB
  obtain ⟨hG, hc⟩ := (isAbelianExtension_fixingOpenSubgroup_iff M).1 hU
  refine ⟨M, inferInstance, hG, hc, ?_⟩
  rw [← map_baseUnitsEquiv_normGroup, hUB]
  exact Subgroup.map_comap_eq_self_of_surjective baseUnitsEquiv.surjective H

end Existence

end GroundTheory.LocalField
end
end
