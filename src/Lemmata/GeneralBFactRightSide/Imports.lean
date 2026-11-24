module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

@[expose] public section

namespace Bl.general_b_fact_right_side

theorem goal1 :
  ∀ (x : Real),
  Iff
    (Eq.{1}
      (Complex.exp
        (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} 2 (Complex.ofReal Real.pi)) Complex.I)
          (Complex.ofReal x)))
      1)
    (Exists.{1} fun (n : Int) ↦ Eq.{1} x (Int.cast.{0} n)) := by
  intro x
  rw [Complex.exp_eq_one_iff]
  refine exists_congr fun n => ?_
  rw [mul_comm (n : ℂ), mul_right_inj' Complex.two_pi_I_ne_zero,
    ← Complex.ofReal_intCast, Complex.ofReal_inj]

end Bl.general_b_fact_right_side
