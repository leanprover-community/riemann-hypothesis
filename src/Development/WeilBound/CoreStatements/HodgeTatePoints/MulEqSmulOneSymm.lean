module

public import Mathlib

@[expose] public section

open scoped Matrix TensorProduct
open Matrix

namespace PositivityTheory.HtPt.Rh

theorem mul_eq_smul_one_symm {R n : Type} [CommRing R] [IsDomain R] [Fintype n] [DecidableEq n]
    {A B : Matrix n n R} {c : R} (hc : c ≠ 0) (h : A * B = c • (1 : Matrix n n R)) :
    B * A = c • (1 : Matrix n n R) := by
  have hd : B.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h
    rw [det_mul, h0, mul_zero, det_smul, det_one, mul_one] at this
    exact pow_ne_zero _ hc this.symm
  have h1 : (B * A - c • (1 : Matrix n n R)) * B = 0 := by
    rw [sub_mul, Matrix.mul_assoc, h]; simp
  have h2 : B.det • (B * A - c • (1 : Matrix n n R)) = 0 := by
    have := congrArg (· * B.adjugate) h1
    simpa only [Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul, Matrix.mul_one, Matrix.zero_mul]
      using this
  exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_left hd)

end PositivityTheory.HtPt.Rh
