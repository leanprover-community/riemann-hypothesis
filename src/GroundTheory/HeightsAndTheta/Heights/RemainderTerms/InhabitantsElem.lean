import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsElem
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Inhabitants
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Elementary
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section


def inhQ : ℕ → Fin 1 → RootRing 1 (1 + 1) :=
  fun k _ => if k = 1 then C (2⁻¹) * (flagTwoSecondRoot - flagTwoFirstRoot) else if k = 2 then C (2⁻¹) else 0


theorem flagIntegral_C_mul (f N : ℕ) (b : ℚ) (Φ : RootRing f N) :
    flagIntegral f N (C b * Φ) = b * flagIntegral f N Φ := by
  simp only [flagIntegral, coeff_C_mul, Finset.mul_sum, mul_assoc]





end

end RestTerms

end GroundTheory.Heights₂.Heights
