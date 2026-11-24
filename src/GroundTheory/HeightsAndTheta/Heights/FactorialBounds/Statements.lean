module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter MvPolynomial

noncomputable section

universe u v

def torusTorsion (n m : ℕ) : Set (Fin n → AddCircle (1 : ℝ)) :=
  {x | m • x = 0}

def TorsionEquidistribution.Statement : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (Z : Set (Fin n → AddCircle (1 : ℝ))) (c : ℝ),
    IsClosed Z → volume Z = 0 → (∃ k : ℤ, c = k / 2) →
    ∀ᶠ m : ℕ in atTop,
      (torusTorsion n m \ Z).ncard ≤
        3 * {x ∈ torusTorsion n m \ Z | (1 / 4 : ℝ) ≤ ‖x ⟨0, hn⟩ + (c : AddCircle (1 : ℝ))‖}.ncard

def SupOfOrthonormalSum.Statement : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (ι : Type v) [Fintype ι] (b : ι → V)
    (p : Seminorm ℂ V), (∀ i, p (b i) ≤ 1) →
    ∀ c : ι → ℂ, p (∑ i, c i • b i) ≤ √(Fintype.card ι : ℝ) * √(∑ i, ‖c i‖ ^ 2)

def SlopeParameterChoice.level (g : ℕ) (h : ℝ) : ℕ :=
  3 * ⌈2 + (g : ℝ) ^ 2 + h⌉₊

def SlopeParameterChoice.third (g : ℕ) (h : ℝ) : ℝ :=
  (SlopeParameterChoice.level g h : ℝ) ^ 2 / 3

def SlopeParameterChoice.Statement : Prop :=
  ∀ C₀ C₂ : ℝ, 0 ≤ C₀ → 0 ≤ C₂ → ∃ C₄ : ℝ, ∀ (g : ℕ) (h μ s : ℝ), 1 ≤ g → 0 ≤ h →
    -(h / 2 + C₀ * g) - C₂ * g * Real.log (2 + g + h) ≤ μ →
    s ≤ 1 / 2 * Real.log (3 * Real.exp 1 * SlopeParameterChoice.third g h ^ 2) +
      2 / SlopeParameterChoice.third g h *
        (g * Real.log (SlopeParameterChoice.level g h) - μ) →
    s ≤ C₄ * Real.log (2 + g + h)

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
