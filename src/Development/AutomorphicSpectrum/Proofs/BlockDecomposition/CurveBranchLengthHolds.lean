module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchNormalisation
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveBranchLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchNormalisationHoldsStatement
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCurveBranchLength
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.BranchInverseOffHypersurfaceHolds
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

namespace GlobalTheory.CompanionTheory.Heights.CurveBranch

theorem curveBranchLength_of_branchNormalisation
    (hB : GroundTheory.Heights₂.Heights.BranchNormalisation.Statement) :
    GroundTheory.Heights₂.Heights.CurveBranchLength.Statement :=
  GroundTheory.Heights₂.Heights.CurveBranchLength.proof GroundTheory.Heights₂.Heights.AutoClose.CurveNormalisationLength hB

theorem curveBranchLength : GroundTheory.Heights₂.Heights.CurveBranchLength.Statement :=
  curveBranchLength_of_branchNormalisation GlobalTheory.T.branch_normalisation_holds

end GlobalTheory.CompanionTheory.Heights.CurveBranch
