module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
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

open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder

namespace GlobalTheory.SW

noncomputable section

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}

def SWAt (n N : ℕ) : Prop :=
  ∀ (M R : ℕ) (φ : Fam E n N), admitted M R φ → ∀ Z ∈ Hn Ψ N, swd Ψ M φ Z 0 0 = 0

def LevelL (Λ : Lt E n) (R : ℕ) (φ : Matrix (Fin n) (Fin N) E → ℂ) : Prop :=
  (∀ x, φ x ≠ 0 → ColsIn Λ ((R : E) • x)) ∧ ∀ x y, ColsIn Λ y → φ (x + (R : E) • y) = φ x

abbrev CF (a b : ℕ) : Type := Ψ → Fin a → Fin b → ℂ

def IsHeat (D : CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ) : Prop :=
  DifferentiableOn ℂ (fun p : CF Ψ N N × CF Ψ n N × CF Ψ n N => D p.1 p.2.1 p.2.2)
    {p | (p.1 : CM Ψ N N) ∈ Hn Ψ N} ∧
  ∀ Z ∈ Hn Ψ N, ∀ (z z' : CM Ψ n N) (τ : Ψ) (a b : Fin N),
    2 * Real.pi * I * deriv (fun s : ℂ =>
      D (fun σ => Z σ + if σ = τ then Matrix.single a b s else 0) z z') 0 =
    ∑ k, deriv (fun s : ℂ => deriv (fun t : ℂ =>
      D Z (fun σ => z σ + if σ = τ then Matrix.single k a s else 0)
        (fun σ => z' σ + if σ = τ then Matrix.single k b t else 0)) 0) 0

def IsMaj {m : ℕ} (G : Matrix (Fin m) (Fin m) E) (H : CM Ψ m m) : Prop :=
  ∀ τ : Ψ, (H τ).PosDef ∧ H τ * (G.map τ.1)⁻¹ * H τ = G.map τ.1

def hval {m : ℕ} (H : CM Ψ m m) (τ : Ψ) (v : Fin m → E) : ℝ :=
  ((fun a => τ.1 (v a)) ⬝ᵥ H τ *ᵥ fun a => conj (τ.1 (v a))).re

def IsoRows {k m : ℕ} (G : Matrix (Fin m) (Fin m) E) (W : Matrix (Fin k) (Fin m) E) : Prop :=
  LinearIndependent E (fun i => W i) ∧ W * G * ccT W = 0

def ShortIso (N D : ℕ) (ε C : ℝ) : Prop :=
  ∀ (G : Matrix (Fin (2 * N)) (Fin (2 * N)) E) (H : CM Ψ (2 * N) (2 * N)), ccT G = G → G.det ≠ 0 →
    Den D G → Den D G⁻¹ → (∃ W : Matrix (Fin N) (Fin (2 * N)) E, IsoRows G W) → IsMaj Ψ G H →
    (∀ v : Fin (2 * N) → E, v ≠ 0 → (∀ a, IsIntegral ℤ (v a)) → ε ≤ ∑ τ, hval Ψ H τ v) →
    ∃ W : Matrix (Fin N) (Fin (2 * N)) E, IntM W ∧ IsoRows G W ∧ ∀ i τ, hval Ψ H τ (W i) ≤ C

end

end GlobalTheory.SW
