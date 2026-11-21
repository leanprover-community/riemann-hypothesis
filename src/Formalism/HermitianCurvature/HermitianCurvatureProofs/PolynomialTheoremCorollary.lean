import Formalism.HermitianCurvature.HermitianCurvatureProofs.PolynomialDegreeExpansion

namespace Formalism.FourierDecayAlt.P.WordNormLpLemmas

open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas Formalism.FourierDecayAlt.P.RealWeightedForms
  Formalism.FourierDecayAlt.P.PolynomialDegreeExpansion
open scoped Matrix




theorem key (a b Q W N N' T c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hQ : 0 < Q) (hW : 0 < W)
    (hN : 0 < N) (hN' : 0 < N') (hT : 0 ≤ T) (hc : 0 ≤ c) (hNT : N * N' / Q ≤ T ^ 2) :
    c * Real.sqrt (a * b / Q) / W ≤ c * T * ((a / (N * W) + b / (N' * W)) / 2) := by
  have hA : 0 ≤ a / (N * W) := by positivity
  have hB : 0 ≤ b / (N' * W) := by positivity
  have e : a * b / Q = W ^ 2 * ((a / (N * W)) * (b / (N' * W))) * (N * N' / Q) := by
    field_simp
  have hAB : (a / (N * W)) * (b / (N' * W)) ≤ ((a / (N * W) + b / (N' * W)) / 2) ^ 2 := by
    nlinarith [sq_nonneg (a / (N * W) - b / (N' * W))]
  have h1 : a * b / Q ≤ (W * T * ((a / (N * W) + b / (N' * W)) / 2)) ^ 2 := by
    rw [e]
    calc W ^ 2 * ((a / (N * W)) * (b / (N' * W))) * (N * N' / Q)
        ≤ W ^ 2 * ((a / (N * W)) * (b / (N' * W))) * T ^ 2 :=
          mul_le_mul_of_nonneg_left hNT (by positivity)
      _ ≤ W ^ 2 * ((a / (N * W) + b / (N' * W)) / 2) ^ 2 * T ^ 2 := by gcongr
      _ = (W * T * ((a / (N * W) + b / (N' * W)) / 2)) ^ 2 := by ring
  have h2 : Real.sqrt (a * b / Q) ≤ W * T * ((a / (N * W) + b / (N' * W)) / 2) :=
    (Real.sqrt_le_left (by positivity)).mpr h1
  calc c * Real.sqrt (a * b / Q) / W ≤ c * (W * T * ((a / (N * W) + b / (N' * W)) / 2)) / W := by
        gcongr
    _ = c * T * ((a / (N * W) + b / (N' * W)) / 2) := by field_simp

theorem lagCo_ne {d : ℕ} (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) (j : Fin (d + 1)) :
    F7.lagCo y j ≠ 0 := by
  unfold F7.lagCo
  refine Finset.prod_ne_zero_iff.mpr fun i hi => inv_ne_zero (sub_ne_zero.mpr fun h => ?_)
  exact (Finset.ne_of_mem_erase hi) (hy h).symm

theorem cg_pos {d : ℕ} (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) : 0 < cg y := by
  unfold cg
  have h0 : 0 < |F7.lagCo y 0| := abs_pos.mpr (lagCo_ne y hy 0)
  exact lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun k => |F7.lagCo y k|)
    (fun k _ => abs_nonneg _) (Finset.mem_univ 0))







end Formalism.FourierDecayAlt.P.WordNormLpLemmas

