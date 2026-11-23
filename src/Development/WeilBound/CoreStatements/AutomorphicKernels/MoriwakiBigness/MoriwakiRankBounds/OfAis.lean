module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.MoriwakiRankBounds.Development
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSeparatedSmallCount
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftSectionSeparation
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftVolumeBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeOfIsIntersectionSystem
public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.MoriwakiRankBounds.OfDegreeGeneric
public import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.MoriwakiRankBounds.OfUpper
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PositivityTheory.Pf1.MbRank

open GroundTheory.Heights₂.Heights.HilbertSamuel

theorem ShiftSectionsRankUpper.of_ais (hAIS : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement) :
    ShiftSectionsRankUpper.Statement :=
  ShiftSectionsRankUpper.of_degreeGeneric
    (GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree (GlobalTheory.CompanionTheory.Ar.Giv.degree_of_system hAIS))

theorem ShiftVolumeBound.of_ais (hSep : ShiftSectionSeparation.Statement) (hCount : SeparatedSmallCount.Statement)
    (hAIS : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement) : ShiftVolumeBound.Statement :=
  ShiftVolumeBound.of_upper hSep hCount (ShiftSectionsRankUpper.of_ais hAIS)

end PositivityTheory.Pf1.MbRank
