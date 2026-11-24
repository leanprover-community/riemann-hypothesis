module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIsolatedPointsCountPrime
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSameOrdersLiftCentre
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PImageDimLe
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedFibreOpenPolyFull
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedPointsCountPrime
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSameOrdersLiftCentre
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.CentredDiscCoverCurveHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

theorem GroundTheory.Heights₂.Heights.AutoClose.IsolatedPointsCountPrime : GroundTheory.Heights₂.Heights.IsolatedPointsCountPrime.Statement :=
  @GroundTheory.Heights₂.Heights.IsolatedPointsCountPrime.proof GroundTheory.Heights₂.Heights.IsolatedFibreOpenPoly.full GroundTheory.Heights₂.Heights.AutoClose.DominantFibreBound GroundTheory.Heights₂.Heights.ImageDimLe.proof

theorem GroundTheory.Heights₂.Heights.AutoClose.SameOrdersLiftCentre : GroundTheory.Heights₂.Heights.SameOrdersLiftCentre.Statement :=
  @GroundTheory.Heights₂.Heights.SameOrdersLiftCentre.proof GroundTheory.Heights₂.Heights.AutoClose.branchOffHypersurface_holds
