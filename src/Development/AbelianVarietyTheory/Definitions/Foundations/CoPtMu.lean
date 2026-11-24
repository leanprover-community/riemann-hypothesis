module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Integral
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset

namespace GlobalTheory.KummerEisensteinGalois

variable {K : Type*} [Field K] [CharZero K]

def ffMu (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (a : ℤ) (s : ℕ) : K :=
  ∑ d ∈ s.divisors, if ¬ p ∣ d ∧ ¬ p ∣ (s / d) then
    ((if ((s / d : ℕ) : ℤ) ≡ a [ZMOD N] then ψ ((s / d : ℕ) : ZMod (p ^ m)) * ((s / d : ℕ) : K) ^ (k - 2) else 0) -
     (if (-((s / d : ℕ) : ℤ)) ≡ a [ZMOD N] then ψ (-((s / d : ℕ) : ZMod (p ^ m))) * (-((s / d : ℕ) : K)) ^ (k - 2) else 0))
    else 0

def eeMu (N p m : ℕ) (ψ : DirichletCharacter K (p ^ m)) (b : ℤ) (s : ℕ) : K :=
  ∑ d ∈ s.divisors, if ¬ p ∣ d ∧ ¬ p ∣ (s / d) then
    ((if ((s / d : ℕ) : ℤ) ≡ b [ZMOD N] then ψ⁻¹ ((d : ℕ) : ZMod (p ^ m)) else 0) -
     (if (-((s / d : ℕ) : ℤ)) ≡ b [ZMOD N] then ψ⁻¹ (-((d : ℕ) : ZMod (p ^ m))) else 0))
    else 0

def coPtMu (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (a b : ℤ) : ℕ → K :=
  cmul (ffMu N p m k ψ a) (eeMu N p m ψ b)

def coPtS (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (c d x : ℤ) (s : ℕ) : K :=
  (c : K) ^ 2 * (d : K) ^ 2 * coPtMu N p m k ψ x 1 s
    - (c : K) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (p ^ m)) * (d : K) ^ 2 * coPtMu N p m k ψ (c * x) 1 s
    - (c : K) ^ 2 * (d : K) * ψ⁻¹ (d : ZMod (p ^ m)) * coPtMu N p m k ψ x d s
    + (c : K) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (p ^ m)) * (d : K) * ψ⁻¹ (d : ZMod (p ^ m)) * coPtMu N p m k ψ (c * x) d s

end GlobalTheory.KummerEisensteinGalois
