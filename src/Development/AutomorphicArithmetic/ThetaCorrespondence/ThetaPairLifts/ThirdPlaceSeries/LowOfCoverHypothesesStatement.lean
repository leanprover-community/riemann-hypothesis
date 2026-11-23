module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowOfCoverHypotheses
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
open GlobalTheory.CovTop GlobalTheory.BigTop

theorem _root_.GlobalTheory.T.liftLowBound_of_cover_estimates : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.LowDefectCondition → _root_.GlobalTheory.CovTop.DeepExistence → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.RingCondition → _root_.GlobalTheory.CovTop.MapsCondition → _root_.GlobalTheory.CovTop.CoverRank → _root_.GlobalTheory.CovTop.MinimalGenerator → _root_.GlobalTheory.CovTop.FlatnessCondition → _root_.GlobalTheory.CovTop.UniformLowerBound → _root_.GlobalTheory.CovTop.LiftLowBound := by
  first | exact @_root_.GlobalTheory.CovTop.LowCover.low_of_cover_hypotheses | exact _root_.GlobalTheory.CovTop.LowCover.low_of_cover_hypotheses | (intros; apply _root_.GlobalTheory.CovTop.LowCover.low_of_cover_hypotheses <;> assumption)
end
