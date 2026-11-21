import Formalism.FlagUnipotentLattices.UnitSumBound

open Finset Formalism.HermitianLatticeCounting.LocalIntegralStructure

namespace Formalism.HermitianLatticeCounting.P

lemma volU_pos_minkowski_factorial_bounds (j : ℕ) : 0 < volU j := by
  unfold volU; apply prod_pos; intro i _; positivity

lemma volU_succ' (j : ℕ) : volU (j + 1) = volU j * ((2 * Real.pi) ^ (j + 1) / (j.factorial : ℝ)) := by
  unfold volU
  rw [Finset.prod_Icc_succ_top (by omega)]
  simp


theorem volume_ratio_formula : Formalism.HermitianLatticeCounting.LocalIntegralStructure.VolRatio := by
  intro k p
  induction p with
  | zero => simp [(volU_pos_minkowski_factorial_bounds k).ne']
  | succ p ih =>
    rw [← add_assoc, volU_succ', Finset.prod_Ico_succ_top (by omega)]
    have e : (p + 1) * k + (p + 1) * (p + 1 + 1) / 2 = (p * k + p * (p + 1) / 2) + (k + p + 1) := by
      have h1 : (p + 1) * (p + 1 + 1) = p * (p + 1) + 2 * (p + 1) := by ring
      rw [h1, Nat.add_mul_div_left _ _ (by norm_num)]; ring
    rw [e, pow_add _ (p * k + p * (p + 1) / 2), ← ih]
    have := volU_pos_minkowski_factorial_bounds k
    have h3 : ((k + p).factorial : ℝ) ≠ 0 := by positivity
    field_simp



end Formalism.HermitianLatticeCounting.P
