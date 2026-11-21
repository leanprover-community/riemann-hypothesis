import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.MeasurableSetImageOfIsLocalHomeomorph

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff

noncomputable section

def shG {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (s : V n → M) (y : V n) : V n :=
  WithLp.toLp 2 (fun i => g i (s y))








theorem sh_val (n j : ℕ) (S r a b : ℝ) (hS : 0 < S) (hr : 0 < r) :
    Real.exp (-b - ((n : ℝ) + j) * a) * (S * Real.exp (-a) / r ^ 2) ^ (-(n : ℝ)) =
      r ^ (2 * n) * Real.exp (-b - (j : ℝ) * a) * S ^ (-(n : ℝ)) := by
  have hX : 0 < Real.exp (-a) / r ^ 2 := by positivity
  rw [mul_div_assoc, Real.mul_rpow hS.le hX.le, Real.rpow_neg hX.le, Real.rpow_natCast,
    div_pow, ← Real.exp_nat_mul, pow_mul]
  have hE : Real.exp (-b - ((n : ℝ) + j) * a) =
      Real.exp (-b - (j : ℝ) * a) * Real.exp (↑n * -a) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hE]
  have h1 : 0 < Real.exp (↑n * -a) := Real.exp_pos _
  have h2 : 0 < (r ^ 2) ^ n := by positivity
  field_simp

end

end ReciprocityTheory.L2DbarEstimates.I
