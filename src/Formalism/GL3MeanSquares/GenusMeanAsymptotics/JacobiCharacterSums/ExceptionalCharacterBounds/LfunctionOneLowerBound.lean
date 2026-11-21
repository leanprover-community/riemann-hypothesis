import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ExceptionalCharacterBounds.EffAbel
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ExceptionalCharacterBounds.EffSmooth

open Formalism.ZeroFreeDirichlet

noncomputable section

namespace Formalism.HermitianLattices.Ext.SupplyAP

theorem tail_small {x : ℝ} (hx : 1 ≤ x) : x ^ 3 * (x + 1) * Real.exp (-(x ^ 3) / x) ≤ 48 / x ^ 4 := by
  have hx0 : 0 < x := by linarith
  have hdiv : -(x ^ 3) / x = -(x ^ 2) := by field_simp
  rw [hdiv, Real.exp_neg]
  have he := Real.pow_div_factorial_le_exp (x ^ 2) (sq_nonneg x) 4
  have h24 : ((4 : ℕ).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [h24] at he
  have hE : 0 < Real.exp (x ^ 2) := Real.exp_pos _
  rw [le_div_iff₀ (by positivity), mul_assoc, mul_assoc]
  have hx1 : x + 1 ≤ 2 * x := by linarith
  have hpos : 0 < (Real.exp (x ^ 2))⁻¹ := inv_pos.mpr hE
  have key : x ^ 3 * (x + 1) * x ^ 4 ≤ 2 * x ^ 8 := by nlinarith [pow_pos hx0 7]
  have h8 : x ^ 8 ≤ 24 * Real.exp (x ^ 2) := by
    have : (x ^ 2) ^ 4 = x ^ 8 := by ring
    rw [this] at he
    rw [div_le_iff₀ (by norm_num)] at he; linarith
  calc x ^ 3 * ((x + 1) * ((Real.exp (x ^ 2))⁻¹ * x ^ 4))
      = (x ^ 3 * (x + 1) * x ^ 4) * (Real.exp (x ^ 2))⁻¹ := by ring
    _ ≤ (2 * x ^ 8) * (Real.exp (x ^ 2))⁻¹ := mul_le_mul_of_nonneg_right key hpos.le
    _ ≤ (2 * (24 * Real.exp (x ^ 2))) * (Real.exp (x ^ 2))⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith) hpos.le
    _ = 48 := by field_simp; ring


end Formalism.HermitianLattices.Ext.SupplyAP
