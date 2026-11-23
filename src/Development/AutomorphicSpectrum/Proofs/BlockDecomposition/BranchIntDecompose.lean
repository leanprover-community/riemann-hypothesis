module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchIntDecompose
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchProperAtPointHoldsStatement
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchIntDecompose
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsExists
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjHomInjective
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionsContainOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericProjectionFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHomogDimZeroPow
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLeadIdealDim
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLinearFormCut
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PUnitaryZariskiDense
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PBranchChartIntX
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.ParametrisationSheetsConnectedHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

namespace GlobalTheory.CompanionTheory.Ar

theorem branchIntDecompose : GroundTheory.Heights₂.Heights.BranchIntDecompose.Statement :=
  GroundTheory.Heights₂.Heights.BranchIntDecompose.proof GlobalTheory.T.branch_proper_at_point_holds
    (GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.proof
      (GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjectionsContainOpen.proof
        GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsFinite.proof
        GroundTheory.Heights₂.Heights.ComplexSets.FiniteProjHomInjective.proof
        GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsOpen.proof
        (GroundTheory.Heights₂.Heights.ComplexSets.ConeAvoidsExists.proof
          GroundTheory.Heights₂.Heights.ComplexSets.LeadIdealDim.proof
          GroundTheory.Heights₂.Heights.ComplexSets.LinearFormCut.proof
          GroundTheory.Heights₂.Heights.ComplexSets.HomogDimZeroPow.proof))
      GroundTheory.Heights₂.Heights.ComplexSets.UnitaryZariskiDense.proof)
    GroundTheory.Heights₂.Heights.AutoClose.ChartIntSumOffHyperplane
    GroundTheory.Heights₂.Heights.Swarm.BranchChartInt.proof

end GlobalTheory.CompanionTheory.Ar
