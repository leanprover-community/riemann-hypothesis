module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.GaussSum
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

open MvPolynomial MeasureTheory NumberField

noncomputable section

theorem chowHeightMul_of_mahlerMul (hM : MahlerMul.Statement) : ChowHeightMul.Statement := by
  intro K _ _ n H k δ₁ δ₂ f₁ f₂ h₁ h₂
  unfold chowHt
  have hmah : ∀ σ : K →+* ℂ, mahler (H.normAt σ) k ((f₁ * f₂).map σ) =
      mahler (H.normAt σ) k (f₁.map σ) + mahler (H.normAt σ) k (f₂.map σ) := by
    intro σ
    rw [map_mul]
    exact hM n k _ _ _ (fun h => h₁ (map_injective σ σ.injective (by rw [h, map_zero])))
      (fun h => h₂ (map_injective σ σ.injective (by rw [h, map_zero])))
  rw [finsum_log_gaussNorm_mul h₁ h₂]
  simp_rw [hmah]
  rw [← mul_add]
  congr 1
  have hs : ∑ σ : K →+* ℂ, (mahler (H.normAt σ) k (f₁.map σ) + mahler (H.normAt σ) k (f₂.map σ) +
      (k : ℝ) * ((δ₁ + δ₂ : ℕ) : ℝ) * (harmonic (n - 1) : ℝ) / 2) =
      ∑ σ : K →+* ℂ, (mahler (H.normAt σ) k (f₁.map σ) + (k : ℝ) * δ₁ * (harmonic (n - 1) : ℝ) / 2) +
      ∑ σ : K →+* ℂ, (mahler (H.normAt σ) k (f₂.map σ) + (k : ℝ) * δ₂ * (harmonic (n - 1) : ℝ) / 2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    push_cast
    ring
  rw [hs]
  ring

end

end GroundTheory.Heights₂.Heights
