import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.SplitEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.QuotMk

section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.DiscSpec
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.V.KernelIndexFullLattice

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

private theorem retract_zpow_mul (n : ℤ) (g : GA E a) :
    retractOne (splitCentre E a 1 ^ n * g) = retractOne g := by
  rw [retractOne_mul, splitEq_holds E a 1, ← map_zpow, retractOne_centralSection, one_mul]

private theorem one_lt_mod (ha : 0 < a) : (1 : ℝ) < (detModule E a (splitCentre E a 1) : ℝ) := by
  rw [splitEq_holds E a 1, detModule_centralSection ha]
  have h1 : (0 : ℝ) < a := Nat.cast_pos.2 ha
  have h2 : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  exact Real.one_lt_exp_iff.2 (by positivity)

private theorem coe_mul_mem_band (x : G1 E a) (g : GA E a) : (x : GA E a) * g ∈ band E a ↔ g ∈ band E a := by
  simp only [band, Set.mem_setOf_eq, map_mul, mem_normOneGL_iff_detModule.1 x.2, one_mul]

private theorem zpow_mul_mem_band (ha : 0 < a) (n : ℤ) (g : GA E a) :
    splitCentre E a 1 ^ n * g ∈ band E a ↔
      (detModule E a g : ℝ) ∈ Set.Ico ((detModule E a (splitCentre E a 1) : ℝ) ^ (-n))
        ((detModule E a (splitCentre E a 1) : ℝ) ^ (-n + 1)) := by
  have hy := one_lt_mod (E := E) ha
  have hy0 : (0 : ℝ) < (detModule E a (splitCentre E a 1) : ℝ) := zero_lt_one.trans hy
  simp only [band, Set.mem_setOf_eq, map_mul, map_zpow, ha.ne', false_or, Set.mem_Ico]
  rw [← Subtype.coe_le_coe, ← Subtype.coe_lt_coe, Positive.val_mul, Positive.coe_zpow, Positive.val_one,
    zpow_add_one₀ hy0.ne', zpow_neg, ← one_div, div_le_iff₀' (zpow_pos hy0 n), one_div,
    lt_inv_mul_iff₀ (zpow_pos hy0 n)]

private theorem exists_zpow_mul_mem_band (g : GA E a) : ∃ n : ℤ, splitCentre E a 1 ^ n * g ∈ band E a := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · exact ⟨0, Or.inl ha⟩
  · obtain ⟨n, hn⟩ := exists_mem_Ico_zpow (detModule E a g).2 (one_lt_mod (E := E) ha)
    exact ⟨-n, (zpow_mul_mem_band ha _ g).2 (by rwa [neg_neg])⟩

private theorem zpow_eq_of_mem_band {g : GA E a} {m n : ℤ} (hm : splitCentre E a 1 ^ m * g ∈ band E a)
    (hn : splitCentre E a 1 ^ n * g ∈ band E a) : splitCentre E a 1 ^ m = splitCentre E a 1 ^ n := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact Units.ext (Subsingleton.elim _ _)
  · have hy := one_lt_mod (E := E) ha
    rw [zpow_mul_mem_band ha] at hm hn
    have h1 := (zpow_lt_zpow_iff_right₀ hy).1 (hm.1.trans_lt hn.2)
    have h2 := (zpow_lt_zpow_iff_right₀ hy).1 (hn.1.trans_lt hm.2)
    rw [show m = n by omega]

end UpperTheory.V.KernelIndexFullLattice

open UpperTheory.V.KernelIndexFullLattice in
theorem UpperTheory.V.KernelIndexFullLattice.bandDom_holds :
    UpperTheory.V.KernelIndexFullLattice.BandDom := by
  intro E _ _ _ a D hD g
  obtain ⟨⟨x, hx⟩, hxD, huniq⟩ := hD (retractOne g)
  obtain ⟨n, hn⟩ := exists_zpow_mul_mem_band g
  obtain ⟨γ, hγ⟩ := id hx
  have hγ' : ratGL E a γ = (x : GA E a) := hγ
  refine ⟨⟨(x : GA E a) * splitCentre E a 1 ^ n, mem_latticeGL_iff.2 ⟨γ, n, by rw [hγ']⟩⟩, ⟨?_, ?_⟩, ?_⟩
  · change retractOne ((x : GA E a) * splitCentre E a 1 ^ n * g) ∈ D
    rw [mul_assoc, retractOne_coe_mul, retract_zpow_mul]
    exact hxD
  · change (x : GA E a) * splitCentre E a 1 ^ n * g ∈ band E a
    rw [mul_assoc, coe_mul_mem_band]
    exact hn
  · rintro ⟨l, hl⟩ ⟨h1, h2⟩
    obtain ⟨δ, m, rfl⟩ := mem_latticeGL_iff.1 hl
    let y : G1 E a := ⟨ratGL E a δ, rationalGL_le_normOneGL ⟨δ, rfl⟩⟩
    change retractOne ((y : GA E a) * splitCentre E a 1 ^ m * g) ∈ D at h1
    change (y : GA E a) * splitCentre E a 1 ^ m * g ∈ band E a at h2
    rw [mul_assoc, retractOne_coe_mul, retract_zpow_mul] at h1
    rw [mul_assoc, coe_mul_mem_band] at h2
    have e : y = x := congrArg Subtype.val (huniq ⟨y, ⟨δ, rfl⟩⟩ h1)
    refine Subtype.ext ?_
    change (y : GA E a) * splitCentre E a 1 ^ m = (x : GA E a) * splitCentre E a 1 ^ n
    rw [e, zpow_eq_of_mem_band h2 hn]
end

section
open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.V.KernelIndexFullLattice

private theorem measurableSet_band' (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) :
    MeasurableSet (band E a) := by
  have hc : Continuous fun g : GA E a => (detModule E a g : ℝ) :=
    continuous_subtype_val.comp continuous_detModule
  have h := hc.measurable (measurableSet_Ico (a := (1 : ℝ)) (b := (detModule E a (splitCentre E a 1) : ℝ)))
  exact (MeasurableSet.const (a = 0)).union h

theorem UpperTheory.V.KernelIndexFullLattice.quotPres_holds :
    UpperTheory.V.KernelIndexFullLattice.QuotPres := by
  intro E _ _ _ a μ _
  have hr : Measurable (retractOne : GA E a → G1 E a) := continuous_retractOne.measurable
  have hD := RightCosetSpace.measurableSet_fundamentalDomain (Γ1 E a)
  have hmk : Measurable (RightCosetSpace.mk (Γ1 E a)) := RightCosetSpace.measurable_mk _
  have hcomp : quotMap E a ∘ mk (latticeGL E a) = RightCosetSpace.mk (Γ1 E a) ∘ retractOne :=
    funext fun g => quotMk_holds E a g
  have hq : Measurable (quotMap E a) := by
    refine measurable_from_quotient.2 ?_
    change Measurable (quotMap E a ∘ mk (latticeGL E a))
    rw [hcomp]
    exact hmk.comp hr
  have hF : IsFundamentalDomain (latticeGL E a)
      (retractOne ⁻¹' RightCosetSpace.fundamentalDomain (Γ1 E a) ∩ band E a) μ :=
    IsFundamentalDomain.mk' ((hr hD).inter (measurableSet_band' E a)).nullMeasurableSet
      (bandDom_holds E a _ (RightCosetSpace.existsUnique_smul_mem_fundamentalDomain (Γ1 E a)))
  refine ⟨hq, ?_⟩
  rw [quotMeasure_eq hF, Measure.map_map hq measurable_mk, hcomp, RightCosetSpace.quotientMeasure, muOne,
    Measure.restrict_map hr hD, Measure.restrict_restrict (hr hD), Measure.map_map hmk hr]
end
