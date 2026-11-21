import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
import BuildAid.ForwardExisting

section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory.SnMass.VolN

theorem absNorm_dInv_eq_abs_discr_pow_inv :
    ∀ (K : Type) [Field K] [NumberField K] (j : ℕ),
      (FractionalIdeal.absNorm (dInv K j) : ℝ) = (|(discr K : ℝ)| ^ j)⁻¹ := by
  intro K _ _ j

  rw [dInv, map_pow, map_inv₀, FractionalIdeal.coeIdeal_absNorm (K := K),
    NumberField.absNorm_differentIdeal K (𝓞 K), Nat.cast_natAbs]
  push_cast
  rw [inv_pow]

end GlobalTheory.SnMass.VolN
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absNorm_inverseDifferentIdealPow_eq_discr : ∀ (K : Type) [Field K] [NumberField K] (j : ℕ), (FractionalIdeal.absNorm (dInv K j) : ℝ) = (|(discr K : ℝ)| ^ j)⁻¹ := by
  atlas_forward_decl GlobalTheory.SnMass.VolN.absNorm_dInv_eq_abs_discr_pow_inv
