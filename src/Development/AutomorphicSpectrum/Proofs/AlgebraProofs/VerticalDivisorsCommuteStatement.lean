import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.HilbertSamuelIrreducibleBasicOpenConnected
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpVerticalPush
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpVerticalFibre
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpFibreDegree
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFiniteBirationalLength
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpDivisorPush
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHorizontalComponentModel
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSBlowupfibre
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjectionFormulaDegree

section
section
namespace GlobalTheory.CompanionTheory.CommAlg.BlowUpFibre

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpFibreSemilocal.Statement.{0} :=
  PositivityTheory.Xgn.t_s_blowupfibre

end GlobalTheory.CompanionTheory.CommAlg.BlowUpFibre
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blow_up_fibre_semilocal : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpFibreSemilocal.Statement.{0} := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CommAlg.BlowUpFibre.main
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projection_formula_degree : GroundTheory.Heights₂.Heights.FieldNumbers.ProjectionFormulaDegree.Statement.{0} := by
  first | exact @GlobalTheory.CompanionTheory.FieldNumbers.projectionFormulaDegree | exact GlobalTheory.CompanionTheory.FieldNumbers.projectionFormulaDegree | (intros; apply GlobalTheory.CompanionTheory.FieldNumbers.projectionFormulaDegree <;> assumption)
end

section
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Num.CutClosed

open GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.AutoClose

theorem verticalPush : BlowUpVerticalPush.Statement.{0} :=
  BlowUpVerticalPush.proof (BlowUpVerticalFibre.proof BlowUpModel.full
    (BlowUpFibreDegree.proof NumbersDVR_HomLocRingLocal NumbersDVR_DivCycleHomLoc
      FiniteBirationalLength.full GlobalTheory.T.blow_up_fibre_semilocal) GlobalTheory.T.projection_formula_degree)

theorem main : CutByEffectiveDivisor.Statement.{0} :=
  CutByEffectiveDivisor.of_steps NumbersDVR_C3NoCommon
    (CommonFactorInduction.of_open ReesAlgebraDim.full BlowUpStrictTransform.proof
      NumbersDVR_C3BlowUpExcessDrop verticalPush (BlowUpDivisorPush.proof verticalPush)
      NumbersDVR_BlowUpHorizontalCorresp HorizontalComponentModel.proof)

end GlobalTheory.CompanionTheory.Ar.Num.CutClosed
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cut_effective_divisor : GroundTheory.Heights₂.Heights.NumbersDVR.CutByEffectiveDivisor.Statement.{0} := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Num.CutClosed.main
end

section
namespace GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem verticalDivisorsCommute : VerticalDivisorsCommute.Statement.{0} :=
  VerticalDivisorsCommute.proof GlobalTheory.T.cut_effective_divisor Representative.full
    IntNumAddFirst.full DivCycleFiniteSupport.full MinimalPrimeMultiHomog.full
    SupSpanMultiHomog.full SpecialQuotDim.full SpecialIdealCorresp.full SpecialIdealMultiHomog.full
    DimStrictDrop.full

end GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_divisors_commute : GroundTheory.Heights₂.Heights.NumbersDVR.VerticalDivisorsCommute.Statement.{0} := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors.verticalDivisorsCommute | exact GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors.verticalDivisorsCommute | (intros; apply GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors.verticalDivisorsCommute <;> assumption)
end
