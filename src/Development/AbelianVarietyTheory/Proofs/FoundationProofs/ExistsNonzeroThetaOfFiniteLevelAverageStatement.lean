module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableComb
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNonzeroThetaOfFiniteLevelAverage
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

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_nonzero_theta_of_finite_level_average : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N')), A.FG → (∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) → (∀ x, (∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) → x ∈ A) → (∀ x ∈ A, ∃ m : ℤ, qH D T x = m) → (∀ x ∈ A, ∀ y ∈ A, al D T (x + y) = al D T x * al D T y * Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ))) → ∀ F : VC D N N' → ℂ, Differentiable ℂ F → F ≠ 0 → ∀ n : ℕ, 0 < n → (∀ x ∈ A, U D T (n • x) F = F) → ∃ P, IsTr D T A F P ∧ P ∈ ThSp D T A ∧ P ≠ 0 := by
  first | exact @GlobalTheory.GalTheta.exists_theta_of_level | exact GlobalTheory.GalTheta.exists_theta_of_level | (intros; apply GlobalTheory.GalTheta.exists_theta_of_level <;> assumption)
