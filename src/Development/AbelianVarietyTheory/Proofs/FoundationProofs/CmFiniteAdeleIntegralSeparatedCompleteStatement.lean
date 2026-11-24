module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleIntegralSeparatedComplete
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

theorem _root_.GlobalTheory.T.cmFiniteAdele_integral_separated_complete : ∀ (D : D7), (∀ y : AE D, (∀ N : ℕ, 0 < N → ∃ w ∈ OhE D, y = (N : AE D) * w) → y = 0) ∧ ∀ x : ℕ → AE D, (∀ N, x N ∈ OhE D) → (∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ OhE D, x (N * m) = x N + (N : AE D) * w) → ∃ y ∈ OhE D, ∀ N : ℕ, 0 < N → ∃ w ∈ OhE D, y = x N + (N : AE D) * w := by
  first | exact @GlobalTheory.IntAdeleComplete.integral_separated_complete | exact GlobalTheory.IntAdeleComplete.integral_separated_complete | (intros; apply GlobalTheory.IntAdeleComplete.integral_separated_complete <;> assumption)
