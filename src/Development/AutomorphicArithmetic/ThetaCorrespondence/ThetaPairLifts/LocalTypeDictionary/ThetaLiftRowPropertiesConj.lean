module

public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestLiftFormulaPrincipalLevelStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestRationalSumsOfFiniteSumsMeaningfulStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ConstK
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RowSumOfHyp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaPairLiftCuspidalOfHypotheses
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedCharactersLinearlyIndependent
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedJetSuccEqAssembly
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedLiftFlipInvariant
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedPeriodIdentityLocal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaIntegralUnfolding
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

section
namespace GlobalTheory.RowClaim.Join
theorem thetaLift_row_properties_conj : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → GlobalTheory.RowClaim.SumOKK ∧ GlobalTheory.RowClaim.ConstK ∧ GlobalTheory.RowClaim.LinK ∧ GlobalTheory.RowClaim.Formula2K ∧ GlobalTheory.RowClaim.SumRatK := by
  intro P K L s1 s2 s3
  have c := _root_.GlobalTheory.ConstNZ.constK_alt P K L s1 s2 s3
  have cusp := _root_.GlobalTheory.T.twisted_thetaLift_cuspidal P
  have sum := _root_.GlobalTheory.T.sumOKK_of_theta_local_inputs P
  exact ⟨sum, c, _root_.GlobalTheory.T.twisted_characters_linearly_independent P cusp,
    GlobalTheory.T.rowTestLiftFormula_principalLevel (_root_.GlobalTheory.T.twisted_period_identity P) (_root_.GlobalTheory.T.twisted_lift_flip_invariant P cusp s1 K c) (_root_.GlobalTheory.T.twisted_theta_integral_unfolds P cusp sum)
      (_root_.GlobalTheory.T.twisted_jets_assemble P sum) c sum,
    GlobalTheory.T.rowTestRationalSums_of_finiteSumsMeaningful sum⟩
end GlobalTheory.RowClaim.Join
end

section

theorem _root_.GlobalTheory.T.thetaLift_row_properties : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → GlobalTheory.RowClaim.SumOKK ∧ GlobalTheory.RowClaim.ConstK ∧ GlobalTheory.RowClaim.LinK ∧ GlobalTheory.RowClaim.Formula2K ∧ GlobalTheory.RowClaim.SumRatK := by
  first | exact @_root_.GlobalTheory.RowClaim.Join.thetaLift_row_properties_conj | exact _root_.GlobalTheory.RowClaim.Join.thetaLift_row_properties_conj | (intros; apply _root_.GlobalTheory.RowClaim.Join.thetaLift_row_properties_conj <;> assumption)
end
