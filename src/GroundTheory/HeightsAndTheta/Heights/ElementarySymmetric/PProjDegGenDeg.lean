module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjDegGenDeg
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDegLTGrowth
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEventualPolynomial
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFiltrationHilbSum
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertDimZero
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertIncrement
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertPrime
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntersectionRecursion
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedNumberPolynomial
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PModulesFromPrimes
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultigradedFiltration
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultigradedHilbertPolynomial
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjDegGenDeg
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRankOfSections
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Swarm

open GroundTheory.Heights₂.Heights.HilbertSamuel

theorem HilbertPrime.closed : HilbertPrime.Statement.{0} :=
  HilbertPrime.proof HilbertDimZero.proof (HilbertIncrement.proof IntersectionRecursion.proof)
    (MixedNumberPolynomial.proof (MultigradedHilbertPolynomial.proof EventualPolynomial.proof))
    (ModulesFromPrimes.proof MultigradedFiltration.proof FiltrationHilbSum.proof DegLTGrowth.proof)

theorem RankOfSections.closed : RankOfSections.Statement :=
  RankOfSections.proof HilbertPrime.closed
    (MixedNumberPolynomial.proof (MultigradedHilbertPolynomial.proof EventualPolynomial.proof))

theorem ProjDegGenDeg.proof : ProjDegGenDeg.Statement :=
  HilbertSamuel.ProjDegGenDeg.proof RankOfSections.closed

end GroundTheory.Heights₂.Heights.Swarm
