module

public import Formalism.LandauZeroFreeBounds.SiegelWalfiszAP
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Complex
open scoped ComplexOrder

noncomputable section

namespace Formalism.ZeroFreeDirichlet

def IsProdChar {q₁ q₂ : ℕ} (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (ψ : DirichletCharacter ℂ (q₁ * q₂)) : Prop :=
  ∀ n : ℕ, ψ (n : ZMod (q₁ * q₂)) = χ₁ (n : ZMod q₁) * χ₂ (n : ZMod q₂)

def Fbq {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)] (χ₁ : DirichletCharacter ℂ q₁)
    (χ₂ : DirichletCharacter ℂ q₂) (ψ : DirichletCharacter ℂ (q₁ * q₂)) (s : ℂ) : ℂ :=
  riemannZeta s * DirichletCharacter.LFunction χ₁ s * DirichletCharacter.LFunction χ₂ s *
    DirichletCharacter.LFunction ψ s

def lamBq {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)] (χ₁ : DirichletCharacter ℂ q₁)
    (χ₂ : DirichletCharacter ℂ q₂) (ψ : DirichletCharacter ℂ (q₁ * q₂)) : ℂ :=
  DirichletCharacter.LFunction χ₁ 1 * DirichletCharacter.LFunction χ₂ 1 * DirichletCharacter.LFunction ψ 1

def ProdCharExists : Prop :=
  ∀ (q₁ q₂ : ℕ) (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂),
    ∃ ψ : DirichletCharacter ℂ (q₁ * q₂), IsProdChar χ₁ χ₂ ψ

def BqCoeff : Prop :=
  ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)] (χ₁ : DirichletCharacter ℂ q₁)
    (χ₂ : DirichletCharacter ℂ q₂) (ψ : DirichletCharacter ℂ (q₁ * q₂)),
    χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 → IsProdChar χ₁ χ₂ ψ →
    ∃ a : ℕ → ℂ, (∀ n, 0 ≤ a n) ∧ a 1 = 1 ∧ LSeries.abscissaOfAbsConv a ≤ 1 ∧
      ∀ s : ℂ, 1 < s.re → Fbq χ₁ χ₂ ψ s = LSeries a s

def BqEntire : Prop :=
  ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)] (χ₁ : DirichletCharacter ℂ q₁)
    (χ₂ : DirichletCharacter ℂ q₂) (ψ : DirichletCharacter ℂ (q₁ * q₂)), χ₁ ≠ 1 → χ₂ ≠ 1 → ψ ≠ 1 →
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∀ s : ℂ, s ≠ 1 → Fbq χ₁ χ₂ ψ s = G s + lamBq χ₁ χ₂ ψ / (s - 1)

def BqGrowth : Prop :=
  ∃ C K : ℝ, ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)] (χ₁ : DirichletCharacter ℂ q₁)
    (χ₂ : DirichletCharacter ℂ q₂) (ψ : DirichletCharacter ℂ (q₁ * q₂)), χ₁ ≠ 1 → χ₂ ≠ 1 → ψ ≠ 1 →
    ∀ s : ℂ, ‖s - 2‖ = 3 / 2 → ‖Fbq χ₁ χ₂ ψ s‖ ≤ C * ((q₁ * q₂ : ℕ) : ℝ) ^ K

def LFunctionOneUpperBound : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ‖DirichletCharacter.LFunction χ 1‖ ≤ C * Real.log (3 * q)

def BqKey : Prop :=
  ∃ C K : ℝ, 0 ≤ K ∧ ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂] [NeZero (q₁ * q₂)] (χ₁ : DirichletCharacter ℂ q₁)
    (χ₂ : DirichletCharacter ℂ q₂) (ψ : DirichletCharacter ℂ (q₁ * q₂)),
    χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 → χ₁ ≠ 1 → χ₂ ≠ 1 → ψ ≠ 1 → IsProdChar χ₁ χ₂ ψ →
    ∀ σ : ℝ, 7 / 8 ≤ σ → σ < 1 →
      1 / 2 - C * ‖lamBq χ₁ χ₂ ψ‖ * ((q₁ * q₂ : ℕ) : ℝ) ^ (K * (1 - σ)) / (1 - σ) ≤ (Fbq χ₁ χ₂ ψ σ).re

def ZetaNegReal : Prop :=
  ∀ σ : ℝ, 0 < σ → σ < 1 → (riemannZeta σ).im = 0 ∧ (riemannZeta σ).re < 0

def LRealPos : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 → χ ≠ 1 → ∀ σ₀ : ℝ,
    (∀ σ : ℝ, σ₀ ≤ σ → DirichletCharacter.LFunction χ σ ≠ 0) →
    ∀ σ : ℝ, σ₀ ≤ σ → (DirichletCharacter.LFunction χ σ).im = 0 ∧ 0 < (DirichletCharacter.LFunction χ σ).re

def SameCharacterLFunctionOne : Prop :=
  ∀ (q₁ q : ℕ) [NeZero q₁] [NeZero q] (χ₁ : DirichletCharacter ℂ q₁) (χ : DirichletCharacter ℂ q),
    χ₁ ≠ 1 → χ ≠ 1 → (∀ n : ℕ, Nat.Coprime n (q₁ * q) → χ₁ (n : ZMod q₁) = χ (n : ZMod q)) →
    ‖DirichletCharacter.LFunction χ₁ 1‖ ≤ (((q₁ * q).primeFactors.card : ℝ) + 1) ^ 2 *
      ‖DirichletCharacter.LFunction χ 1‖

def RealCharExists : Prop :=
  ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q), χ ^ 2 = 1 ∧ χ ≠ 1

def BqKeyOf : Prop := BqCoeff → BqEntire → BqGrowth → LFunctionOneUpperBound → BqKey

def SiegelOf : Prop :=
  ProdCharExists → RealCharExists → BqKey → LFunctionOneUpperBound → ZetaNegReal → LRealPos → SameCharacterLFunctionOne → SiegelLower

end Formalism.ZeroFreeDirichlet
