module

public import Formalism.PeriodIntegrals.OneCosetSharp
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

namespace PI.OneCosetSharp.W

open Loc LocE

def Nums (k₀ m t j n' c n : ℕ) : Prop :=
  1 ≤ k₀ ∧ Even m ∧ 4 ≤ m ∧ 1 ≤ j ∧ j ≤ m - 2 ∧ c = m - 1 - j ∧
    n' + (c + 1) = k₀ + m - 1 + (j - 1) * t ∧ n + c = k₀ + m - 1 + j * t

def Claim1 : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ) (k₀ m t j n' c n : ℕ),
    Nums k₀ m t j n' c n →
    ∀ h : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k),
        (∃ xj : (Fin n' → k) →ₗ[k] (Fin n → k),
          E1 (n' := n') (c' := c + 1) (n := n) (c := c) (fun u => ψ₀ u) Finset.univ 1
            (om (fun _ => 1) (fun _ => 0) 1 (LinearEquiv.refl k _) h (PhiS ψ₀ χ k₀ m t j n' c n)) xj ≠ 0) →
        ∃ ρ ∈ R1 k n c, ∃ κ, InJS k₀ m t c n κ ∧ h = ρ * κ

def Claim2 : Prop :=
  ∀ (k : Type) [Field k] [Fintype k] (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ) (k₀ m t j n' c n : ℕ),
    Nums k₀ m t j n' c n →
    ∃ xj : (Fin n' → k) →ₗ[k] (Fin n → k),
      E1 (n' := n') (c' := c + 1) (n := n) (c := c) (fun u => ψ₀ u) Finset.univ 1 (PhiS ψ₀ χ k₀ m t j n' c n) xj ≠ 0

def PatClosed : Prop :=
  ∀ (k : Type) [Field k] (k₀ m t j n' c n : ℕ), Nums k₀ m t j n' c n →
    ∀ κ₁ κ₂ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k), InJS k₀ m t c n κ₁ → InJS k₀ m t c n κ₂ →
      InJS k₀ m t c n (κ₁ * κ₂) ∧ InJS k₀ m t c n κ₁⁻¹

def KappaZero : Prop :=
  ∀ (k : Type) [Field k] (ψ₀ : AddChar k ℂ) (χ : ℕ → kˣ →* ℂˣ) (k₀ m t j n' c n : ℕ), Nums k₀ m t j n' c n →
    ∀ y : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k), PhiS ψ₀ χ k₀ m t j n' c n y ≠ 0 →
      ∃ κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k), InJS k₀ m t c n κ ∧
        ∀ p < n' + (c + 1), κ (eN k (n + c) (fIdx k₀ c n p)) = y (eN k (n' + (c + 1)) (fIdx k₀ (c + 1) n' p))

def NElem : Prop :=
  ∀ (k : Type) [Field k] (n' c n : ℕ) (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (tt : FC n' (c + 1) n c → k),
    ∃ ν ∈ R1 k n c, (∀ v, ν (inX k n c v) = inX k n c v) ∧
      ∀ i < c, ν (eN k (n + c) (n + i)) = xx1 xj tt (eN k (n' + (c + 1)) (n' + i))

def GaStep : Prop :=
  ∀ (k : Type) [Field k] (k₀ m t j n' c n : ℕ), Nums k₀ m t j n' c n →
    ∀ g : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k),
      (∀ i < c, g (eN k (n + c) (n + i)) = eN k (n + c) (n + i)) →
      (∀ p < n' + (c + 1), (p < k₀ ∨ k₀ + c < p) → ∃ v, g (eN k (n + c) (fIdx k₀ c n p)) = inX k n c v) →
      ∃ γ ∈ R1 k n c, ∃ κ, InJS k₀ m t c n κ ∧ g = γ * κ

end PI.OneCosetSharp.W
