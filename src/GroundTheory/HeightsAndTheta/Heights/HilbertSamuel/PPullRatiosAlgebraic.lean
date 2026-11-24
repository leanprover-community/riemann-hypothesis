module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullConeDegree
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullGradedAlgebraic
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullRatiosAlgebraic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

theorem PullRatiosAlgebraic.proof (h₁ : PullConeNull.Statement) (h₂ : PullConeDegree.Statement)
    (h₃ : PullGradedAlgebraic.Statement) : PullRatiosAlgebraic.Statement := by
  intro K _ ι _ Ω _ _ y D e L hy he hL hz
  obtain ⟨N, hN⟩ := h₁ K ι Ω y D L hz
  exact h₃ K ι Ω y D e L (fun k => e k + N * Fintype.card (ι k)) hy he hL
    (fun d g hg hd => h₂ K ι Ω y D e L N hy hL hN d g hg hd)

end GroundTheory.Heights₂.Heights.HilbertSamuel
