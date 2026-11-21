import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsoluteFourierCoefficients
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsoluteCutoffBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FriedrichsExtensionFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusCurveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WvAlg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureOperatorFactsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevOperatorFactsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSobolevEmbedding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirOperatorFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevIntegrationByPartsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenseDomainFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionNormBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevSpacePreserved
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcentrationTimeBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusJointCurveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusFirstAssumptionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PaleyWienerDecay
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothOperatorFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRegularity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelLocalization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelWeightFacts

section
namespace PositivityTheory.RgBcC.Fc

open PositivityTheory.RgBcC

theorem asmKerOne_of_steps (hC : AsmCpt) (hS : CalcSteps) (hO : SmoothOp) (hP : PWdecay) (hK : KerCore)
    (hL : KerLoc) (hW : KerW) : AsmKerOne := by
  intro h1 h2 h3 h4 h5 h6 n _ _ μ _ E w g T hg
  have hWC : WaveCpt := hC h1 h2 h3 h4
  apply hW n μ E w g h1 h2 h3
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := hK n μ E g T hg h1 h2 h3 h4 h5 h6 hWC hS hO hP
  exact ⟨k, hL n μ E g T k hg h1 h2 h3 h6 hWC hk1 hk2 hk3 hk4⟩

end PositivityTheory.RgBcC.Fc
end

section
namespace PositivityTheory.RgBcC.Fc

open PositivityTheory.RgBcC

theorem calcSteps : CalcSteps :=
  ⟨GlobalTheory.T.absolute_fourier_coefficients, GlobalTheory.T.absolute_cutoff_bound, GlobalTheory.T.functional_calculus_curve, GlobalTheory.CompanionTheory.WaveFc.wvAlg, GlobalTheory.T.closure_operator_facts, GlobalTheory.T.sobolev_operator_facts, GlobalTheory.T.compact_sobolev_embedding,
    GlobalTheory.T.section_norm_bound, GlobalTheory.T.sobolev_space_preserved, GlobalTheory.T.concentration_time_bound, GlobalTheory.T.functional_calculus_joint_curve, GlobalTheory.T.friedrichs_extension_facts, GlobalTheory.T.casimir_operator_formula, GlobalTheory.T.sobolev_integration_by_parts,
    GlobalTheory.T.dense_domain_facts⟩

theorem asmCpt : AsmCpt :=
  GlobalTheory.T.functional_calculus_first_assumption GlobalTheory.T.absolute_fourier_coefficients GlobalTheory.T.absolute_cutoff_bound GlobalTheory.T.functional_calculus_curve GlobalTheory.CompanionTheory.WaveFc.wvAlg GlobalTheory.T.closure_operator_facts GlobalTheory.T.sobolev_operator_facts GlobalTheory.T.compact_sobolev_embedding
    GlobalTheory.T.section_norm_bound GlobalTheory.T.sobolev_space_preserved GlobalTheory.T.concentration_time_bound GlobalTheory.T.functional_calculus_joint_curve GlobalTheory.T.friedrichs_extension_facts GlobalTheory.T.casimir_operator_formula GlobalTheory.T.sobolev_integration_by_parts GlobalTheory.T.dense_domain_facts

theorem asmKerOne : AsmKerOne :=
  asmKerOne_of_steps asmCpt calcSteps GlobalTheory.T.smooth_operator_facts GlobalTheory.T.paley_wiener_decay GlobalTheory.T.kernel_regularity GlobalTheory.T.kernel_localization GlobalTheory.T.kernel_weight_facts

end PositivityTheory.RgBcC.Fc
end
