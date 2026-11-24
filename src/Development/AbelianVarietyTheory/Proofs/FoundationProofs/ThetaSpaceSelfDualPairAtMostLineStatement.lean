module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
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

theorem _root_.GlobalTheory.T.theta_space_selfDual_pair_at_most_line : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (A : AddSubgroup (VC D N N')), KLat D (tor0 D cc δ) A → (∀ F ∈ ThSp D (tor0 D cc δ) A, ∀ G ∈ ThSp D (tor0 D cc δ) A, G ≠ 0 → ∃ c : ℂ, F = c • G) ∧ (∀ x ∈ A, ∀ F, Wd D (tor0 D cc δ) x F = fun z => al D (tor0 D cc δ) x * U D (tor0 D cc δ) x F z) ∧ (∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, (Hf D (tor0 D cc δ) x y).im = m) ∧ (∀ x, (∀ y ∈ A, ∃ m : ℤ, (Hf D (tor0 D cc δ) x y).im = m) → x ∈ A) ∧ A.FG ∧ Submodule.span ℝ (A : Set (VC D N N')) = ⊤ ∧ ∀ x ∈ A, ∃ m : ℤ, qH D (tor0 D cc δ) x = m := by
  first | exact @GlobalTheory.ThetaLine.theta_line | exact GlobalTheory.ThetaLine.theta_line | (intros; apply GlobalTheory.ThetaLine.theta_line <;> assumption)
