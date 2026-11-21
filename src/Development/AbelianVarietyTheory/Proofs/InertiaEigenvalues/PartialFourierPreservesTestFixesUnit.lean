import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNhdsZeroTranslationInvariantOfLocallyConst
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorGLBlockIsLocallyConstantCompactSupp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTestUnitIndicatorHermitianBlock
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantPartialFourierGLBlockStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasCompactSupportPartialFourierGLBlockStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierHermitianBlockIsLocallyConstant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierHermitianBlockHasCompactSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierGLBlockUnitIndicator
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierHermitianBlockUnitIndicator
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticTraceEqAddStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralTraceUnitUnramifiedQuadratic

section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem fourier_test_unit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → (∀ f', IsTest f' → IsTest (fourG M ψ f')) ∧ (∀ f, IsTest f → IsTest (fourU M ψ f)) ∧ IsTest (unitG r F) ∧ IsTest (unitU r F E) ∧ fourG M ψ (unitG r F) = unitG r F ∧ fourU M ψ (unitU r F E) = unitU r F E := by
  intro F E _ _ _ _ hU r M ψ hψ
  haveI := hU.ultraF; haveI := hU.ultraE; haveI := hU.lcF; haveI := hU.lcE
  have htr := GlobalTheory.T.unramifiedQuadratic_trace_eq_add_star F E
  refine ⟨fun f' hf => ⟨GlobalTheory.T.isLocallyConstant_partialFourierGLBlock F E r M ψ hψ f' hf (GlobalTheory.T.exists_nhds_zero_translation_invariant_of_locallyConstant _ f' hf), GlobalTheory.T.hasCompactSupport_partialFourierGLBlock F E r M ψ hψ f' hf (GlobalTheory.T.exists_nhds_zero_translation_invariant_of_locallyConstant _ f' hf)⟩,
    fun f hf => ⟨GlobalTheory.T.partialFourierHermitianBlock_isLocallyConstant F E r M ψ hψ htr f hf (GlobalTheory.T.exists_nhds_zero_translation_invariant_of_locallyConstant _ f hf), GlobalTheory.T.partialFourierHermitianBlock_hasCompactSupport F E r M ψ hψ htr f hf (GlobalTheory.T.exists_nhds_zero_translation_invariant_of_locallyConstant _ f hf)⟩,
    GlobalTheory.T.unitIndicatorGLBlock_isLocallyConstantCompactSupport F r, GlobalTheory.T.isTest_unitIndicatorHermitianBlock F E r hU.norm_star, GlobalTheory.T.partialFourierGLBlock_unitIndicator F E r M ψ hψ, GlobalTheory.T.partialFourierHermitianBlock_unitIndicator F E r M ψ hψ htr (GlobalTheory.T.exists_integral_trace_unit_unramifiedQuadratic F E htr)⟩

end GlobalTheory
end

open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialFourier_preserves_test_fixes_unit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → (∀ f', IsTest f' → IsTest (fourG M ψ f')) ∧ (∀ f, IsTest f → IsTest (fourU M ψ f)) ∧ IsTest (unitG r F) ∧ IsTest (unitU r F E) ∧ fourG M ψ (unitG r F) = unitG r F ∧ fourU M ψ (unitU r F E) = unitU r F E := by
  atlas_forward_decl GlobalTheory.fourier_test_unit
