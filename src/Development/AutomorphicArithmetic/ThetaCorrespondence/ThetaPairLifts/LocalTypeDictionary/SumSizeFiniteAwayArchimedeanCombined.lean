module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSumSizeBoundLargeDataFromFactorsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSumDenominatorBoundOfFactorClaims
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaNormBoundHypothesesSatisfiedStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanClassCountBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanSumCountBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanSumSizeOppositeConjugate
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanTensorSizeBoundOfLocal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DepthOfSumBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FieldPairComparison
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FiniteCoefficientBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FiniteDataBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FiniteInfiniteScalarBounds
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FiniteTopTermIntegralBoundOfLocal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FormValueFiniteInfiniteFactorization
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GammaFactorLossAtFinitePlaces
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KernelConjugationMeanArchimedeanTopTerm
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RowSumOfHyp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SumSizeBoundFinitePlaces
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SumSizeDictionaryOfLocalBounds
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TestVectorValueFactorization
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedLocalFactorAwayFromLevel
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt

@[expose] public section

section
namespace GlobalTheory.SumSize.Join
theorem sum_size_finite_away_archimedean_combined : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.SumSize.FinK ∧ GlobalTheory.SumSize.AwayK ∧ GlobalTheory.SumSize.InfK := by
  intro P
  have hInp : ∀ D, GlobalTheory.NormSum.Inp D := GlobalTheory.T.cmThetaNormBoundHypotheses_satisfied
  have hOK : GlobalTheory.RowClaim.SumOKK := _root_.GlobalTheory.T.sumOKK_of_theta_local_inputs P
  have hDep : GlobalTheory.SumSize.DepthK := _root_.GlobalTheory.T.depthK_of_sumOKK P hOK
  have hDict : GlobalTheory.SumSize.DictK := _root_.GlobalTheory.T.sum_size_dictionary P hInp
  have hScal := _root_.GlobalTheory.T.finite_and_infinite_scalar_bounds P
  have hForm := _root_.GlobalTheory.T.form_value_finite_infinite_factorization P
  have hPair := _root_.GlobalTheory.T.field_pair_comparison P
  have hPsi := _root_.GlobalTheory.Adopt.test_vector_value_factorization P
  have hTopF := _root_.GlobalTheory.T.sum_size_finite_top_term_integral P hInp hDict hDep
  have hRowF := _root_.GlobalTheory.T.sum_size_bound_finite_places P hInp hDict hDep
  have hTopI := _root_.GlobalTheory.T.kernel_conjugation_mean_archimedean_top_term P hInp hDict hDep
  have hRowI := _root_.GlobalTheory.T.sum_size_bound_opposite_conjugation P hInp hDict hDep
  refine ⟨?_, _root_.GlobalTheory.Adopt.twisted_local_factor_away_from_level P, ?_⟩
  · exact GlobalTheory.Adopt.finiteSumDenominatorBound_of_factor_claims hOK hDep hScal.1 (_root_.GlobalTheory.Adopt.finCoefK_of_theta_inputs P) (_root_.GlobalTheory.T.finDatK_of_theta_inputs P) (_root_.GlobalTheory.T.gamma_factor_loss_at_finite_places P)
      hTopF hRowF hPair.1 hPsi.1 hForm.1
  · exact GlobalTheory.T.archimedeanSumSizeBound_largeData_from_factors hOK hDep hScal.2 (_root_.GlobalTheory.T.sum_size_archimedean_tensor_bound P) (_root_.GlobalTheory.T.sum_count_bound_archimedean P hDep) (_root_.GlobalTheory.T.class_count_bound_archimedean P)
      hTopI hRowI hPair.2 hPsi.2 hForm.2
end GlobalTheory.SumSize.Join
end

section

theorem _root_.GlobalTheory.T.sum_size_bound_all_places : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.SumSize.FinK ∧ GlobalTheory.SumSize.AwayK ∧ GlobalTheory.SumSize.InfK := by
  first | exact @_root_.GlobalTheory.SumSize.Join.sum_size_finite_away_archimedean_combined | exact _root_.GlobalTheory.SumSize.Join.sum_size_finite_away_archimedean_combined | (intros; apply _root_.GlobalTheory.SumSize.Join.sum_size_finite_away_archimedean_combined <;> assumption)
end
