import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMapLinearScalingByDeterminant
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalUnitScalingHaarProductFormula
import BuildAid.ForwardExisting

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_map_linear_scaling_by_determinant : ∀ (F : Type) [Field F] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → ∀ (lam : Measure R), lam.IsAddHaarMeasure → ∀ c : ℝ≥0, lam.map (fun x => algebraMap F R A.det * x) = c • lam → ∀ μ : Measure (ι → R), μ.IsAddHaarMeasure → μ.map (fun x => A.map (algebraMap F R) *ᵥ x) = c • μ := by
  first | exact @GlobalTheory.CompanionTheory.SW.DetScale.map_mulVec_eq_smul | exact GlobalTheory.CompanionTheory.SW.DetScale.map_mulVec_eq_smul | (intros; apply GlobalTheory.CompanionTheory.SW.DetScale.map_mulVec_eq_smul <;> assumption)
end

section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_unit_scaling_haar_product_formula : ∀ (F : Type) [Field F] [NumberField F] (a : F), a ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ : Measure (Ainf F), μ.IsAddHaarMeasure → μ.map (fun x => algebraMap F (Ainf F) a * x) = cinf • μ) ∧ ∀ v : HeightOneSpectrum (𝓞 F), ∀ μ : Measure (Fv F v), μ.IsAddHaarMeasure → μ.map (fun x => algebraMap F (Fv F v) a * x) = c v • μ := by
  first | exact @GlobalTheory.CompanionTheory.SW.ProdFormula.unitProd_scalar | exact GlobalTheory.CompanionTheory.SW.ProdFormula.unitProd_scalar | (intros; apply GlobalTheory.CompanionTheory.SW.ProdFormula.unitProd_scalar <;> assumption)
end

section
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.ProdFormula

theorem modulus_matrix : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ : Measure (ι → Ainf F), μ.IsAddHaarMeasure → μ.map (fun x => A.map (algebraMap F (Ainf F)) *ᵥ x) = cinf • μ) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ μ : Measure (ι → Fv F v), μ.IsAddHaarMeasure → μ.map (fun x => A.map (algebraMap F (Fv F v)) *ᵥ x) = c v • μ) := by
  intro F _ _ ι _ _ A hA
  obtain ⟨cinf, c, hU, hinf, hv⟩ := GlobalTheory.T.global_unit_scaling_haar_product_formula F A.det hA
  refine ⟨cinf, c, hU, ?_, ?_⟩
  · intro μ hμ
    haveI : BorelSpace (Ainf F) := ⟨rfl⟩
    exact GlobalTheory.T.haar_map_linear_scaling_by_determinant F (Ainf F) ι A hA Measure.addHaar inferInstance cinf
      (hinf Measure.addHaar inferInstance) μ hμ
  · intro v μ hμ
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    haveI : SecondCountableTopology (Fv F v) := (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v).2.2.1
    exact GlobalTheory.T.haar_map_linear_scaling_by_determinant F (Fv F v) ι A hA Measure.addHaar inferInstance (c v)
      (hv v Measure.addHaar inferInstance) μ hμ

end GlobalTheory.CompanionTheory.SW.ProdFormula
end

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addHaar_map_mulVec_eq_smul_at_all_places : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ : Measure (ι → Ainf F), μ.IsAddHaarMeasure → μ.map (fun x => A.map (algebraMap F (Ainf F)) *ᵥ x) = cinf • μ) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ μ : Measure (ι → Fv F v), μ.IsAddHaarMeasure → μ.map (fun x => A.map (algebraMap F (Fv F v)) *ᵥ x) = c v • μ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SW.ProdFormula.modulus_matrix
end
