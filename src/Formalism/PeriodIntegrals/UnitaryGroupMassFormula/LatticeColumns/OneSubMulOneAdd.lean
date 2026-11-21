import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HAdaptGen

noncomputable section

namespace PIW.MassDataColumns

open Matrix Formalism.FourierDecayAlt.S3
open scoped Matrix

variable {K : Type} [Field K] (O : Subring K) {r k : ℕ}




theorem one_sub_mul_one_add (N : Matrix (Idx r k) (Idx r k) K) (hN : N * N = 0) : (1 - N) * (1 + N) = 1 := by
  rw [sub_mul, one_mul, mul_add, mul_one, hN, add_zero, add_sub_cancel_right]

theorem one_add_mul_one_sub (N : Matrix (Idx r k) (Idx r k) K) (hN : N * N = 0) : (1 + N) * (1 - N) = 1 := by
  rw [add_mul, one_mul, mul_sub, mul_one, hN, sub_zero, sub_add_cancel]







end PIW.MassDataColumns
