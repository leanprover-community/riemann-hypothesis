import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg

section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

namespace GlobalTheory.FormalCalc

theorem lin_formalLog (Q : Type) [CommRing Q] [Algebra ℚ Q] (d : ℕ) (g : MvPowerSeries (Fin d) Q) :
    constantCoeff g = 1 → ∀ i, lin (formalLog g) i = lin g i := by
  intro hg i
  have h := congrArg (coeff (0 : Fin d →₀ ℕ)) (mul_pderiv_formalLog hg i)
  rw [coeff_zero_eq_constantCoeff_apply, map_mul, hg, one_mul, ← coeff_zero_eq_constantCoeff_apply,
    coeff_pderiv, coeff_pderiv] at h
  simpa [lin] using h

end GlobalTheory.FormalCalc
end

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeriesLinearCoefficients_mvPowerSeriesFormalLog : ∀ (Q : Type) [CommRing Q] [Algebra ℚ Q] (d : ℕ) (g : MvPowerSeries (Fin d) Q), constantCoeff g = 1 → ∀ i, lin (formalLog g) i = lin g i := by
  atlas_forward_decl GlobalTheory.FormalCalc.lin_formalLog
