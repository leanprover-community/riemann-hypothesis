module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTruncationCongrOfPadicContinuousEvalEqZero
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

@[expose] public section

open GlobalTheory.QLog

theorem _root_.GlobalTheory.T.exists_truncation_congr_of_padicContinuousEval_eq_zero : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (d : ℕ) (x : Fin d → A) (E : MvPowerSeries (Fin d) O →ₐ[O] A), IsEval p x E → ∀ (n N : ℕ) (f : MvPowerSeries (Fin d) O), E f = 0 → ∃ P : MvPolynomial (Fin d) O, (∀ α : Fin d →₀ ℕ, N ≤ α.degree → AddMonoidAlgebra.coeff P α = 0) ∧ (∀ α : Fin d →₀ ℕ, α.degree < N → AddMonoidAlgebra.coeff P α = MvPowerSeries.coeff α f) ∧ MvPolynomial.aeval x P ∈ Ideal.span (Set.range x) ^ N ⊔ Ideal.span {(p : A) ^ n} := by
  first | exact @GlobalTheory.trunc_dec | exact GlobalTheory.trunc_dec | (intros; apply GlobalTheory.trunc_dec <;> assumption)
