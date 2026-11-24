module

public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
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

namespace GlobalTheory.CompanionTheory.Ar

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt

variable {K : Type} [Field K] [NumberField K]

def sqAt (E : HermitianBundle.{0} K) (σ : K →+* ℂ) (x : Fibre σ E.carrier) : ℝ :=
  ((E.metric.form σ).inner x x).re

def OrthAt (E : HermitianBundle.{0} K) (F F' : Submodule (𝓞 K) E.carrier) : Prop :=
  ∀ (σ : K →+* ℂ), ∀ x ∈ F, ∀ y ∈ F',
    (E.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] y) = 0

structure SatFlag (E : HermitianBundle.{0} K) (r : ℕ) where

  F : Fin (r + 1) → Submodule (𝓞 K) E.carrier
  mono : Monotone F
  sat : ∀ i, E.Saturated (F i)
  rank : ∀ i, E.rank (F i) = i

namespace SatFlag

variable {E : HermitianBundle.{0} K} {r : ℕ}

def top (A : SatFlag E r) : Submodule (𝓞 K) E.carrier := A.F (Fin.last r)

def grDeg (A : SatFlag E r) (i : Fin r) : ℝ := E.normDegree (A.F i.succ) - E.normDegree (A.F i.castSucc)

end SatFlag

structure FlagPair (E : HermitianBundle.{0} K) (Ψ : Type) (j k : ℕ) where

  W : Ψ → SatFlag E j

  S : Ψ → SatFlag E k

namespace FlagPair

variable {E : HermitianBundle.{0} K} {Ψ : Type} [Fintype Ψ] {j k : ℕ}

def lamDeg (A : FlagPair E Ψ j k) (lam : Ψ → Fin (j + k) → ℝ) : ℝ :=
  ∑ τ, (-(∑ i : Fin j, lam τ (Fin.castAdd k i) * (A.W τ).grDeg i) +
    ∑ i : Fin k, lam τ (Fin.natAdd j i) * (A.S τ).grDeg i.rev)

def flatDeg (A : FlagPair E Ψ j k) (τ : Ψ) : ℝ := E.normDegree (A.W τ).top - E.normDegree (A.S τ).top

def part (A : FlagPair E Ψ j k) : Ψ ⊕ Ψ → Submodule (𝓞 K) E.carrier :=
  Sum.elim (fun τ => (A.W τ).top) (fun τ => (A.S τ).top)

def IsOrthFull (A : FlagPair E Ψ j k) : Prop :=
  (∀ a b, a ≠ b → OrthAt E (A.part a) (A.part b)) ∧ Fintype.card Ψ * (j + k) = Module.finrank (𝓞 K) E.carrier

end FlagPair

end GlobalTheory.CompanionTheory.Ar
