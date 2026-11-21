import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootShift.SumLeProdOfTwoLe

open Finset

noncomputable section

namespace PI.SqfRootShift.W

theorem geom_part (G : ℝ) (r : ℕ) (hr : 1 ≤ r) :
    ∑ k ∈ Finset.Ioc 1 r, (G - 1) * G ^ (r - k) = G ^ (r - 1) - 1 := by
  induction r, hr using Nat.le_induction with
  | base => simp
  | succ r hr ih =>
    rw [Finset.sum_Ioc_succ_top (by omega : 1 ≤ r), Nat.sub_self, pow_zero, mul_one]
    have h : ∑ k ∈ Finset.Ioc 1 r, (G - 1) * G ^ (r + 1 - k) =
        G * ∑ k ∈ Finset.Ioc 1 r, (G - 1) * G ^ (r - k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Ioc] at hk
      rw [show r + 1 - k = (r - k) + 1 by omega, pow_succ]; ring
    rw [h, ih, show r + 1 - 1 = (r - 1) + 1 by omega, pow_succ]; ring



end PI.SqfRootShift.W
