module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm

noncomputable section

def ChartBergmanBound.Statement : Prop :=
  ∀ (D : ℕ) (U : Set (Fin D → ℂ)) (ψ ρ : (Fin D → ℂ) → ℝ) (y₀ : Fin D → ℂ), IsOpen U → y₀ ∈ U →
    ContDiffOn ℝ 2 ψ U → ContinuousOn ρ U → 0 < ρ y₀ → (∀ w, 0 ≤ levi ψ y₀ w) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ F : (Fin D → ℂ) → ℂ, AnalyticOnNhd ℂ F U →
      ENNReal.ofReal (‖F y₀‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y₀)) ≤
        ENNReal.ofReal (((((1 / Real.pi : ℝ) : ℂ) • hessC ψ y₀).det.re / ρ y₀ + ε) *
            (n : ℝ) ^ D) *
          ∫⁻ y in U, ENNReal.ofReal (‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) * ρ y)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
