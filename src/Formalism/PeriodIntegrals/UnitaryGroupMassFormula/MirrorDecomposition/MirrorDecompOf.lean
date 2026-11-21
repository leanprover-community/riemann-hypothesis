import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirrorDecomposition.HpkRowEsI
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirrorDecomposition.IsMonomialConjTranspose
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.Forward

open Matrix

noncomputable section

namespace PI.MirrorSection₂

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW

section Gen

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem frame_inv {s : Matrix n n ℂ} {x : Matrix m m ℂ} {F : Matrix n m ℂ}
    (hs : IsUnit s.det) (hx : IsUnit x.det) (h : s * F = F * x) : s⁻¹ * F = F * x⁻¹ := by
  calc s⁻¹ * F = s⁻¹ * (F * x * x⁻¹) := by rw [Matrix.mul_assoc F, mul_nonsing_inv x hx, Matrix.mul_one]
    _ = s⁻¹ * (s * F) * x⁻¹ := by rw [h]; simp only [Matrix.mul_assoc]
    _ = F * x⁻¹ := by rw [← Matrix.mul_assoc s⁻¹, nonsing_inv_mul s hs, Matrix.one_mul]

end Gen

variable {k r : ℕ}


theorem pair_lt {m : ℕ} {P b u' : Matrix (Fin m) (Fin m) ℂ} (hb : b ∈ UTset m) (h : bᴴ * P * u' = P)
    (hP : IsUnit P.det) : P * u' * P⁻¹ ∈ LTset m := by
  have iL := lt_inv (ut_conjTranspose hb)
  have e : P * u' * P⁻¹ = (bᴴ)⁻¹ := by
    calc P * u' * P⁻¹ = (bᴴ)⁻¹ * (bᴴ * P * u') * P⁻¹ := by
          rw [show (bᴴ)⁻¹ * (bᴴ * P * u') = ((bᴴ)⁻¹ * bᴴ) * P * u' by simp only [Matrix.mul_assoc], iL.2.1,
            Matrix.one_mul]
      _ = (bᴴ)⁻¹ := by rw [h, Matrix.mul_assoc, mul_nonsing_inv P hP, Matrix.mul_one]
  rw [e]; exact iL.2.2



end PI.MirrorSection₂
