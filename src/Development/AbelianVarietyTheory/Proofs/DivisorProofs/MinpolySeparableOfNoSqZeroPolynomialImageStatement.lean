module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.FieldTheory.Separable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolySeparableOfNoSqZeroPolynomialImage
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder

theorem _root_.GlobalTheory.T.minpoly_separable_of_no_sq_zero_polynomial_image : ∀ (F C : Type) [Field F] [Ring C] [IsSimpleRing C] [Algebra F C] [FiniteDimensional F C] (n : ℕ) (σ : F →+* ℂ) (ψ : C →+* Matrix (Fin n) (Fin n) ℂ), 0 < n → (∀ x : F, ψ (algebraMap F C x) = Matrix.scalar (Fin n) (σ x)) → ∀ c : C, (∀ P : Polynomial ℂ, Polynomial.aeval (ψ c) P * Polynomial.aeval (ψ c) P = 0 → Polynomial.aeval (ψ c) P = 0) → (minpoly F c).Separable := by
  first | (exact @GlobalTheory.LKCx.minpoly_separable_of_sq_zero_free) | (exact GlobalTheory.LKCx.minpoly_separable_of_sq_zero_free) | (intros; apply GlobalTheory.LKCx.minpoly_separable_of_sq_zero_free  <;> assumption)
