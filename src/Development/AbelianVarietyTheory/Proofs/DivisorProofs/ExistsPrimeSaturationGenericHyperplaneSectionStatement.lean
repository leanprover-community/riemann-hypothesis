module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeSaturationGenericHyperplaneSection
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight

@[expose] public section

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_prime_saturation_generic_hyperplane_section : ∀ (K L : Type) [Field K] [Field L] (N : ℕ) [Algebra K L] [Algebra (MvPolynomial (Fin N) K) L] [IsScalarTower K (MvPolynomial (Fin N) K) L] [IsFractionRing (MvPolynomial (Fin N) K) L] (P : Ideal (MvPolynomial (Fin N) K)), P.IsPrime → (∀ u : Fin N → AlgebraicClosure K, ∃ y : Fin N → AlgebraicClosure K, y ≠ 0 ∧ (∀ g ∈ P, aeval y g = 0) ∧ ∑ j, u j * y j = 0) → ∃ Q : Ideal (MvPolynomial (Fin N) L), Q.IsPrime ∧ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔ Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j : MvPolynomial (Fin N) L)} ≤ Q ∧ ∀ g ∈ Q, ∀ j, ∃ m : ℕ, X j ^ m * g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔ Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j : MvPolynomial (Fin N) L)} := by
  first | exact @GlobalTheory.Chow.exists_prime_saturation_generic_section | exact GlobalTheory.Chow.exists_prime_saturation_generic_section | (intros; apply GlobalTheory.Chow.exists_prime_saturation_generic_section <;> assumption)
