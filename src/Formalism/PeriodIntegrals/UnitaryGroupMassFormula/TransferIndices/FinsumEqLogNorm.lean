import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.DvTransferIdxOf

noncomputable section

namespace PI.Dv.TIW

open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped WithZero

private theorem log_nonpos_of_le_one (m : ℤᵐ⁰) (h : m ≤ 1) : WithZero.log m ≤ 0 := by
  rcases eq_or_ne m 0 with h0 | h0
  · rw [h0, WithZero.log_zero]
  · rw [← WithZero.exp_log h0, ← WithZero.exp_zero] at h
    exact WithZero.exp_le_exp.mp h

theorem volume_nonneg : VNonneg := by
  intro K _ _ w x
  unfold vAdd
  have h := log_nonpos_of_le_one (w.valuation K (algebraMap (𝓞 K) K x)) (w.valuation_le_one x)
  omega



theorem unzero_toAdd (m : ℤᵐ⁰) (h : m ≠ 0) : Multiplicative.toAdd (WithZero.unzero h) = WithZero.log m := by
  obtain ⟨a, rfl⟩ := WithZero.ne_zero_iff_exists.mp h
  first
  | rfl
  | simp [WithZero.log]
  | simp

theorem norm_embedding_eq {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) :
    ‖FinitePlace.embedding v x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(vAdd v x)) := by
  have hv : v.valuation K x ≠ 0 := by simpa using hx
  have he : Valued.v (FinitePlace.embedding v x) = v.valuation K x := by
    first
    | exact v.valuedAdicCompletion_eq_valuation' x
    | exact v.valuedAdicCompletion_eq_valuation x
    | rfl
  rw [FinitePlace.norm_def, he, WithZeroMulInt.toNNReal_neg_apply _ hv, unzero_toAdd _ hv]
  simp [vAdd]



theorem abs_norm_le {K : Type} [Field K] [NumberField K] (x : 𝓞 K) (B : ℝ) (hB : 0 ≤ B)
    (hσ : ∀ σ : K →+* ℂ, ‖σ (algebraMap (𝓞 K) K x)‖ ≤ B) :
    |((Algebra.norm ℤ x : ℤ) : ℝ)| ≤ B ^ Module.finrank ℚ K := by
  have h1 : |((Algebra.norm ℤ x : ℤ) : ℝ)| =
      ∏ w : InfinitePlace K, w (algebraMap (𝓞 K) K x) ^ w.mult := by
    rw [InfinitePlace.prod_eq_abs_norm, ← Algebra.coe_norm_int]
    first
    | simp
    | norm_cast
  rw [h1, ← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun w _ => pow_nonneg (AbsoluteValue.nonneg _ _) _) (fun w _ => ?_)
  refine pow_le_pow_left₀ (AbsoluteValue.nonneg _ _) ?_ _
  rw [← InfinitePlace.norm_embedding_eq]
  exact hσ _


end PI.Dv.TIW
