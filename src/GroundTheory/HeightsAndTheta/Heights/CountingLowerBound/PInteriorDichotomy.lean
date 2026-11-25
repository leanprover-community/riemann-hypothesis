module

public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Statements
import Mathlib.Algebra.Order.Star.Real

@[expose] public section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real

theorem InteriorDichotomy.proof : InteriorDichotomy.Statement := by
  intro C0 C1 C2 hC0 hC1 hC2
  refine ⟨C0 * (log (3 + C2) + 2) + C1, ?_⟩
  rintro h hmu g fj La ⟨hg, hfj, hgexp, hLa, hlow, hup⟩
  have ⟨hg0, hfj0, hLa0⟩ : 0 ≤ g ∧ 0 ≤ fj ∧ 0 ≤ La := ⟨by linarith, by linarith, by linarith⟩
  have hlog3 : 0 ≤ log (3 + C2) := Real.log_nonneg (by linarith)
  by_cases hm : 0 ≤ hmu
  · linarith [show 0 ≤ (C0 * (log (3 + C2) + 2) + C1) * fj * La by positivity]
  suffices hlog : log (2 + g + max h 0) ≤ (log (3 + C2) + 2) * La by
    nlinarith [mul_le_mul_of_nonneg_left hlog (mul_nonneg hfj0 hC0)]
  calc
    _ ≤ log ((3 + C2) * exp (2 * La)) := by
      apply Real.log_le_log (by linarith [le_max_right h 0])
      calc
        _ ≤ (3 + C2) * (g * La) := by
          nlinarith [show max h 0 ≤ C2 * g * La from max_le (by linarith [lt_of_not_ge hm]) (by positivity),
            one_le_mul_of_one_le_of_one_le hg hLa, le_mul_of_one_le_right hg0 hLa]
        _ ≤ _ := by
          rw [two_mul, Real.exp_add]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul hgexp (by linarith [Real.add_one_le_exp La]) hLa0 (exp_pos La).le) (by linarith)
    _ = log (3 + C2) + 2 * La := by rw [Real.log_mul (by linarith) (exp_pos _).ne', Real.log_exp]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hLa hlog3]

end GroundTheory.Heights₂.Heights.LowerBound
