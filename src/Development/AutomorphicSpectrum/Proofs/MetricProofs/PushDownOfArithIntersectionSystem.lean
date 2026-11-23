module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfArithSystemStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionFormulaOfArithSystem
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagArith
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagMinorTrdeg
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagNeZero
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagRatioFieldEq
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagRatioTrdeg
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPushDown
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv


open GroundTheory.Heights₂.Heights.LowerBoundFree in
theorem hodgeFlagArith : HodgeFlagArith.Statement :=
  HodgeFlagArith.proof HodgeFlagNeZero.proof
    (HodgeFlagRatioTrdeg.proof HodgeFlagRatioFieldEq.full HodgeFlagMinorTrdeg.proof)

theorem pushDown :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement →
      GroundTheory.Heights₂.Heights.LowerBoundFree.PushDown.Statement := fun h =>
  GroundTheory.Heights₂.Heights.LowerBoundFree.PushDown.proof (GlobalTheory.T.generic_degree_of_arith_system h) GlobalTheory.CompanionTheory.Ar.Giv.ProjF.pfStep hodgeFlagArith

end GlobalTheory.CompanionTheory.Ar.Giv
