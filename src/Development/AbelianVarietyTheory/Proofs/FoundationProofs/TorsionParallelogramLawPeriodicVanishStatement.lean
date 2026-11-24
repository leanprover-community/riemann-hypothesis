module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionParallelogramLawPeriodicVanish
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
open scoped BigOperators

theorem _root_.GlobalTheory.T.torsion_parallelogramLaw_periodic_vanish : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ (N : ℕ), 0 < N → ∀ M : ℂ → ℝ,
    (∀ t ∈ Λ, M t = 0) → (∀ t ω : ℂ, (N : ℂ) * t ∈ Λ → ω ∈ Λ → M (t + ω) = M t) →
    (∀ P Q : ℂ, (N : ℂ) * P ∈ Λ → (N : ℂ) * Q ∈ Λ → Q ∉ Λ → M (P + Q) + M (P - Q) = 2 * M P + 2 * M Q) →
    ∀ t : ℂ, (N : ℂ) * t ∈ Λ → M t = 0 := by
  first | exact @GlobalTheory.torsion_parallelogram_vanish | exact GlobalTheory.torsion_parallelogram_vanish | (intros; apply GlobalTheory.torsion_parallelogram_vanish <;> assumption)
