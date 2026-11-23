module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ModelDyWeights
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun


theorem _root_.GlobalTheory.T.model_dy_weights : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ) (h : ModelOK A x₀ m) (τ : Ψ) (i : Fin (p + q)), (∀ k, (model A x₀ m h).dy (τ, i) (.inl k) = -((rkW i * m (.inl τ) + rkO i * m (.inr τ) : ℕ) : ℤ)) ∧ ∀ t : StepIx Ψ p q, ((t = stepOf Ψ p q (τ, i) ∨ (t.1 = .inl τ ∧ (t.2 : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) → (model A x₀ m h).dy (τ, i) (.inr t) = 1) ∧ (¬ (t = stepOf Ψ p q (τ, i) ∨ (t.1 = .inl τ ∧ (t.2 : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) → (model A x₀ m h).dy (τ, i) (.inr t) = 0) := by
  exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Dy.dy_flag
