module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParamChartInt
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBranchInt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchProperAtPointHoldsStatement
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChartIntCountAdd
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamChartInt
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamCritNull
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamDensIntegrable
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamOffRegularZero
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamPieceInt
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularInjectivePieces
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceBranchInt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
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

namespace GlobalTheory.CompanionTheory.Ar.SliceBranch

theorem paramChartInt : GroundTheory.Heights₂.Heights.ParamChartInt.Statement :=
  GroundTheory.Heights₂.Heights.ParamChartInt.proof
    (GroundTheory.Heights₂.Heights.ChartIntCountAdd.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact)
    GroundTheory.Heights₂.Heights.ParamPieceInt.proof GroundTheory.Heights₂.Heights.ParamCritNull.proof
    GroundTheory.Heights₂.Heights.ParamOffRegularZero.proof GroundTheory.Heights₂.Heights.RegularInjectivePieces.proof
    GroundTheory.Heights₂.Heights.ParamDensIntegrable.proof

theorem sliceBranchInt : GroundTheory.Heights₂.Heights.SliceBranchInt.Statement :=
  GroundTheory.Heights₂.Heights.SliceBranchInt.proof GlobalTheory.T.branch_proper_at_point_holds paramChartInt

end GlobalTheory.CompanionTheory.Ar.SliceBranch
