module

public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open Matrix Metric GroundTheory.Heights₂.Heights.Regular

structure LogPeriods (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] where
  a_le : a ≤ n
  free : Module.Free ℤ Λ
  fin : Module.Finite ℤ Λ
  rank : Module.finrank ℤ Λ = 2 * g

  E : LinearMap.BilinForm ℤ Λ
  alt : ∀ x, E x x = 0
  unimod : Function.Bijective E

  P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ))
  hol : ∀ x, DifferentiableOn ℂ (fun w => P w x) (logCover a_le)

  H : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ
  herm : ∀ w ∈ logCover a_le, (H (expCover a w)).IsHermitian
  pos : ∀ w ∈ logCover a_le, ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H (expCover a w) *ᵥ star z).re
  im : ∀ w ∈ logCover a_le, ∀ x y, (P w x ⬝ᵥ H (expCover a w) *ᵥ star (P w y)).im = E x y

  T : Fin a → (Λ →ₗ[ℤ] Λ)
  mono : ∀ i, ∀ w ∈ logCover a_le, ∀ x,
    P (w + Pi.single (Fin.castLE a_le i) (2 * Real.pi * Complex.I)) x = P w (T i x)

  W : Submodule ℤ Λ
  coiso : ∀ x, (∀ y ∈ W, E x y = 0) → ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ W

  s : W → (Fin n → ℂ) → (Fin g → ℂ)
  s_hol : ∀ x, DifferentiableOn ℂ (s x) (ball 0 1)
  s_eq : ∀ x, ∀ w ∈ logCover a_le, s x (expCover a w) = P w x
  span : Submodule.span ℂ (Set.range fun x => s x 0) = ⊤

end GlobalTheory.CompanionTheory.Ar.Flat
