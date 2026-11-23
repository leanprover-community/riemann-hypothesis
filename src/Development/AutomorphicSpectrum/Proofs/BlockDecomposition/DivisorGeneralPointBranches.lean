module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorGeneralPointBranches
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDivisorBranches
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDivisorGeneralPointBranches
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDivisorGoodPointBranches
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDivisorOneComponent
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PJacobianRankOffHypersurface
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalCodimOneCompleteIntersection
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalCodimOneUniformiser
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalDivisorChartGeneric
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalDoublePointsGeneric
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelDivisorChartGeneric
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelExists
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelGoodPointChart
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelGoodPointGeneric
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProjectionUnramifiedGeneric
public import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.BranchInverseOffHypersurfaceHolds
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

namespace GlobalTheory.CompanionTheory.ComplexSets


open GroundTheory.Heights₂.Heights in
theorem divisorGeneralPointBranches : GroundTheory.Heights₂.Heights.DivisorGeneralPointBranches.Statement :=
  DivisorGeneralPointBranches.proof DivisorOneComponent.proof
    (DivisorBranches.proof IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.proof
      GroundTheory.Heights₂.Heights.AutoClose.DivisorRegularGeneric
      (NormalDivisorChartGeneric.proof
        (NormalModelDivisorChartGeneric.proof
          (NormalModelGoodPointGeneric.proof NormalCodimOneCompleteIntersection.proof
            NormalCodimOneUniformiser.proof JacobianRankOffHypersurface.proof
            ProjectionUnramifiedGeneric.proof)
          NormalModelGoodPointChart.proof))
      NormalDoublePointsGeneric.proof DivisorGoodPointBranches.proof)

end GlobalTheory.CompanionTheory.ComplexSets
