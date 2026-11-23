module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthProdMkConst
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp

namespace GlobalTheory.SchwartzFstOp

theorem norm_iteratedFDeriv_sliceCLM_le {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V'] (f : 𝓢(V × V', ℂ)) (x' : V') (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (sliceCLM x' f) x‖ ≤ ‖iteratedFDeriv ℝ n f (x, x')‖ := by
  have e : (⇑(sliceCLM x' f) : V → ℂ) =
      (fun q => f (q + ((0 : V), x'))) ∘ (ContinuousLinearMap.inl ℝ V V') := by
    funext y; simp
  have hc : ContDiff ℝ n (fun q : V × V' => f (q + ((0 : V), x'))) :=
    ((f.smooth ⊤).comp (contDiff_id.add contDiff_const)).of_le (by exact_mod_cast le_top)
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hc _ le_rfl, iteratedFDeriv_comp_add_right]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ∏ _i : Fin n, ‖ContinuousLinearMap.inl ℝ V V'‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_inl_le_one ℝ V V')
  have h2 : (ContinuousLinearMap.inl ℝ V V') x + ((0 : V), x') = (x, x') := by simp
  rw [h2]
  exact (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans (le_of_eq (mul_one _))

theorem norm_pow_mul_seminorm_sliceCLM_le {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V'] (f : 𝓢(V × V', ℂ)) (x' : V') (j k n : ℕ) :
    ‖x'‖ ^ k * SchwartzMap.seminorm ℂ j n (sliceCLM x' f) ≤ SchwartzMap.seminorm ℂ (j + k) n f := by
  set M := SchwartzMap.seminorm ℂ (j + k) n f
  have hM : 0 ≤ M := apply_nonneg _ _
  have hpt : ∀ x : V, ‖x'‖ ^ k * (‖x‖ ^ j * ‖iteratedFDeriv ℝ n (sliceCLM x' f) x‖) ≤ M := by
    intro x
    have hw : ‖x'‖ ^ k * ‖x‖ ^ j ≤ ‖(x, x')‖ ^ (j + k) := by
      rw [pow_add, mul_comm]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (norm_fst_le (x, x')) _)
        (pow_le_pow_left₀ (norm_nonneg _) (norm_snd_le (x, x')) _) (by positivity) (by positivity)
    calc ‖x'‖ ^ k * (‖x‖ ^ j * ‖iteratedFDeriv ℝ n (sliceCLM x' f) x‖)
        = (‖x'‖ ^ k * ‖x‖ ^ j) * ‖iteratedFDeriv ℝ n (sliceCLM x' f) x‖ := by ring
      _ ≤ ‖(x, x')‖ ^ (j + k) * ‖iteratedFDeriv ℝ n f (x, x')‖ :=
          mul_le_mul hw (norm_iteratedFDeriv_sliceCLM_le f x' n x) (norm_nonneg _) (by positivity)
      _ ≤ M := SchwartzMap.le_seminorm ℂ (j + k) n f (x, x')
  rcases eq_or_lt_of_le (pow_nonneg (norm_nonneg x') k : (0 : ℝ) ≤ ‖x'‖ ^ k) with h0 | hpos
  · rw [← h0, zero_mul]; exact hM
  · rw [mul_comm, ← le_div_iff₀ hpos]
    refine SchwartzMap.seminorm_le_bound ℂ j n _ (div_nonneg hM hpos.le) (fun x => ?_)
    rw [le_div_iff₀ hpos, mul_comm]
    exact hpt x

end GlobalTheory.SchwartzFstOp
