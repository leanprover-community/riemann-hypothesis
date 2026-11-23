module

public import Mathlib.Data.Matrix.Mul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEquationOfTwistedCocycleDefect
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


theorem _root_.GlobalTheory.T.frobenius_equation_of_twisted_cocycle_defect : ∀ (R : Type) [CommRing R] (φ σ : R →+* R) (d N k : ℕ) (lr e e₀ : R) (Q Q' B B' A₀ A₀' ε : Matrix (Fin d) (Fin d) R), (∀ x : R, lr * x = 0 → x = 0) → (∃ v : Rˣ, e = lr * v) → (∃ v : Rˣ, e₀ = lr * v) → (∀ x, φ (σ x) = σ (φ x)) → φ lr = lr → σ lr = lr → σ e₀ = e₀ → A₀.map σ = A₀ → Q * Q' = lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R) → B * B' = e ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R) → A₀ * A₀' = e₀ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R) → e ^ N • (Q * A₀) = e₀ ^ N • (B * Q.map φ) → e ^ N • (ε * B.map σ) = σ e ^ N • (B * ε.map φ) → e₀ ^ (2 * N) • (Q' * ε * Q.map σ - lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)) = A₀ * (Q' * ε * Q.map σ - lr ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) R)).map φ * A₀' := by
  first | (exact @GlobalTheory.FrobeniusDefect.frobenius_defect_eq) | (exact GlobalTheory.FrobeniusDefect.frobenius_defect_eq) | (intros; apply GlobalTheory.FrobeniusDefect.frobenius_defect_eq  <;> assumption)
