module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesHasSumBoundFrobenius
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.Per GlobalTheory.PSer Filter Topology
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem summable_Lam_terms (l : ℕ) [Fact l.Prime] (h i : ℕ) (y : ℕ → Fl l) (ρ : ℝ)
    (hh : 1 ≤ h) (hρ : ρ < 1) (hy : ∀ k, ‖sh (y k)‖ ≤ ρ) :
    Summable fun k : ℕ => (l : ℂ_[l]) ^ k * lam h i (y k) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have h2 : Tendsto (fun k : ℕ => ((l : ℝ)⁻¹) ^ k * gam l h i ρ) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.2 (by linarith))
      (inv_lt_one_of_one_lt₀ hl)).mul_const (gam l h i ρ)
    simpa using this
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) h2
  rw [norm_mul, norm_pow, Laws.norm_l]
  exact mul_le_mul_of_nonneg_left (lam_hasSum_norm_le_frob l h i ρ (y k) hh hρ (hy k)).2.1
    (pow_nonneg (inv_nonneg.2 (by linarith)) _)

theorem sum_mul_Lam_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]) (i : ℕ) (y : ℕ → Fin h → Fl l) (ρ : ℝ),
    1 ≤ h → ρ < 1 → (∀ k j, ‖sh (y k j)‖ ≤ ρ) →
    HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * ∑ j, μ j * lam h i (y k j)) 0 →
    ∑ j, μ j * abelian₂ h i (fun k => y k j) = 0 := by
  intro l _ h μ i y ρ hh hρ hy hs
  have hsum : ∀ j, Summable fun k : ℕ => μ j * ((l : ℂ_[l]) ^ k * lam h i (y k j)) := fun j =>
    (summable_Lam_terms l h i (fun k => y k j) ρ hh hρ (fun k => hy k j)).mul_left (μ j)
  calc ∑ j, μ j * abelian₂ h i (fun k => y k j)
      = ∑ j, ∑' k : ℕ, μ j * ((l : ℂ_[l]) ^ k * lam h i (y k j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        unfold abelian₂
        rw [tsum_mul_left]
    _ = ∑' k : ℕ, ∑ j, μ j * ((l : ℂ_[l]) ^ k * lam h i (y k j)) :=
        (Summable.tsum_finsetSum fun j _ => hsum j).symm
    _ = ∑' k : ℕ, (l : ℂ_[l]) ^ k * ∑ j, μ j * lam h i (y k j) := by
        refine tsum_congr fun k => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = 0 := hs.tsum_eq

end GlobalTheory.PSer

end
