module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenOfPoincareLelongHyperplane
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix
open scoped ContDiff

noncomputable section

def PolydiscLelongLimit.Statement : Prop :=
  ∀ (d m : ℕ) (r ρ : ℝ) (F : (Fin (d + 1) → ℂ) → ℂ) (χ : (Fin (d + 1) → ℂ) → ℝ)
    (ψ : Fin d → (Fin (d + 1) → ℂ) → ℝ),
    ρ < r → VanishesToOrder F r m → ContDiffOn ℝ ∞ χ (Metric.ball 0 r) →
    (∀ τ ∈ Metric.ball (0 : Fin (d + 1) → ℂ) r, χ τ ≠ 0 → τ ∈ Metric.ball 0 ρ) →
    (∀ k, ContDiffOn ℝ ∞ (ψ k) (Metric.ball 0 r)) →
      Tendsto (fun ε : ℝ =>
          ReciprocityTheory.AnForm.maInt (vecCons (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) ψ) χ (Metric.ball 0 r))
        (𝓝[>] 0)
        (𝓝 ((m : ℝ) * ∫ w in Metric.ball (0 : Fin d → ℂ) r,
          χ (ReciprocityTheory.AnForm.A.hypIncl w) * ReciprocityTheory.AnForm.A.densHyp ψ w))

end

end GroundTheory.Heights₂.Heights
