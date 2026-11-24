module

public import Formalism.GaussValuationBounds.GaussUnit
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

open scoped ENNReal

namespace Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds

def sigUp (ℓ E M j : ℕ) : ℕ :=
  ⌈((E : ℝ) + (M : ℝ) / (ℓ : ℝ) ^ (j - 1)) * (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2⌉₊ + 1

def SigBoundUp : Prop :=
  ∀ (ℓ : ℕ), 3 ≤ ℓ → ∀ (g h j : ℕ), 1 ≤ j →
    (sigUp ℓ (3 * g) ((h + 2 * g) / (ℓ - 1) + 1) j : ℝ) ≤
      3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (j + 1) + 9 / 4 * g + 11 / 4

def EisE {O : Type} [CommRing O] (ϖ : O) (e : ℕ) (E : Polynomial O) (N : ℕ) : Prop :=
  E.Monic ∧ E.natDegree = N ∧ (∀ i < N, E.coeff i ∈ Ideal.span {ϖ ^ e}) ∧ E.coeff 0 ∉ Ideal.span {ϖ ^ (e + 1)}

def GaussEisRam : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (e : ℕ), 1 ≤ e → ∀ (x : ℝ), 0 ≤ x → ∀ (E : Polynomial O) (N : ℕ), 1 ≤ N → EisE ϖ e E N →
      Formalism.NOK.gaussV x (E : PowerSeries O) = ENNReal.ofReal (min (e : ℝ) (x * N))

def LemmaCValRam : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (e : ℕ), 1 ≤ e → ∀ (ℓ : ℕ), 2 ≤ ℓ →
    ∀ (E : ℕ → Polynomial O) (u : ℕ → PowerSeries O),
      (∀ s, EisE ϖ e (E s) (ℓ ^ s)) → (∀ s, IsUnit (u s)) →
      ∀ (ell g a b₀ b₁ s₀ s₁ k : ℕ), s₀ < s₁ →
        2 * ((a : ℝ) + 2 * e * g * ell) < e * b₁ → 2 * b₀ ≤ ℓ * b₁ →
        PowerSeries.C (ϖ ^ a) *
            (∏ s ∈ Finset.range ell, (u s * (E s : PowerSeries O)) ^ g) ^ 2 *
            (u s₀ * (E s₀ : PowerSeries O)) ^ b₀ ∈
          Ideal.span {PowerSeries.C (ϖ ^ k), (u s₁ * (E s₁ : PowerSeries O)) ^ b₁} →
        (k : ℝ) ≤ ((a : ℝ) + 2 * e * g * ell) * b₁ / (b₁ - b₀ / ℓ) ∧
          (k : ℝ) ≤ 2 * ((a : ℝ) + 2 * e * g * ell)

end Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds
