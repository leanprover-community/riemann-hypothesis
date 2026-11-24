module

public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitPairGen
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Henselian
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
open NumberField Matrix

namespace PI.SqPair

open Formalism.L2.PairingIndexBounds.Eq.SqG

def PLocal (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ)
    (L' L'' : Submodule (𝓞 E) (Fin N → E)) (n : 𝓞 E) (p : ℕ) : Prop :=
  ∃ e : Matrix (Fin N) (Fin N) E,
    (∀ y ∈ L', e *ᵥ y ∈ L') ∧ (∀ y ∈ L'', e *ᵥ y ∈ L'') ∧
    ∀ M ∈ ({e * e - e, eᴴ * e, (1 - e)ᴴ * (1 - e)} : Set (Matrix (Fin N) (Fin N) E)),
      ∀ y, (y ∈ L' ∨ y ∈ L'') →
        ∃ s : ℤ, ¬ (p : ℤ) ∣ s ∧ ∃ m, m ∈ L' ∧ m ∈ L'' ∧ (s : E) • (M *ᵥ y) = (n : E) • m

def PLocalAll : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], PI.IsCMUnram E →
    ∀ (N : ℕ) (L' L'' : Submodule (𝓞 E) (Fin N → E)), Even N → IsSDG E N L' → IsSDG E N L'' →
      ∀ n : 𝓞 E, n ≠ 0 → ∀ p : ℕ, p.Prime → PLocal E N L' L'' n p

def LocCartanPair : Prop :=
  ∀ (R : Type) [CommRing R] (σ : R ≃+* R), (∀ x, σ (σ x) = x) →
    ∀ (R₀ : Subring R), (∀ x, x ∈ R₀ ↔ σ x = x) →
    ∀ [IsDomain R₀] [IsDiscreteValuationRing R₀] [HenselianLocalRing R₀]
      [Finite (IsLocalRing.ResidueField R₀)],
    (∃ θ : R, IsUnit (θ - σ θ)) →
    ∀ ϖ : R₀, Irreducible ϖ →
    ∀ (N : ℕ), Even N → ∀ (k : ℕ) (h : Matrix (Fin N) (Fin N) R),
      (h.map σ)ᵀ * h = ((ϖ : R) ^ (2 * k)) • (1 : Matrix (Fin N) (Fin N) R) →
      ∃ e f : Matrix (Fin N) (Fin N) R, e * e = e ∧ (e.map σ)ᵀ = 1 - e ∧ e * h = h * f

end PI.SqPair
