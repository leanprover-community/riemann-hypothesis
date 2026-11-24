module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumCountBoundLargeDataStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorCountBoundOfCosetDepthBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaKCosetCountFormula
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
open GlobalTheory.SumSize GlobalTheory.RowClaim
namespace GlobalTheory.SumCount
theorem archimedean_sum_count_bound : _root_.GlobalTheory.FunPr.ThetaLocalInputs → DepthK → InfCountK := fun hP hD =>
  infCountK_of GlobalTheory.T.datumCountBound_largeData (_root_.GlobalTheory.T.theta_kCoset_count_formula hP) (GlobalTheory.T.pureTensorCountBound_of_cosetDepthBound hD)
end GlobalTheory.SumCount
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.sum_count_bound_archimedean : _root_.GlobalTheory.FunPr.ThetaLocalInputs → DepthK → InfCountK := by
  first | exact @_root_.GlobalTheory.SumCount.archimedean_sum_count_bound | exact _root_.GlobalTheory.SumCount.archimedean_sum_count_bound | (intros; apply _root_.GlobalTheory.SumCount.archimedean_sum_count_bound <;> assumption)
end
