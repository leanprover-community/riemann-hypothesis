import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AdditionIdentityOfSigmaFormulaUnit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaCubeRelationIntegralFormalGroupBiadditiveStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaPointsIntegralNormConjugateLaws

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaJets

theorem jetsPh_all : ∀ D : D7, GL3Theta.jetsPh D := fun D =>
  Formalism.MainNotions.Ext.CutA.jetsPh_of' Formalism.MainNotions.Ext.CutA.jetsHigh_holds Formalism.MainNotions.Ext.CutA.jetsOne_holds
    Formalism.MainNotions.Ext.CutA.jetsTwo_holds D (GlobalTheory.T.theta_cube_relation_integral_formalGroup_biadditive D).1 (GlobalTheory.T.cmThetaPoints_integral_norm_conjugate_laws D).2.1 (GlobalTheory.T.cmThetaPoints_integral_norm_conjugate_laws D).2.2

end GlobalTheory.ThetaJets
end

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_normalized_theta_jets_integral : ∀ D : D7, GL3Theta.jetsPh D := by
  atlas_forward_decl GlobalTheory.ThetaJets.jetsPh_all
