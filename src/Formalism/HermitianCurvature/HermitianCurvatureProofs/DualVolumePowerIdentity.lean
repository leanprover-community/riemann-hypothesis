import Formalism.HermitianCurvature.Statement

namespace Formalism.FourierDecayAlt.P

open Finset Real

namespace Easy


end Easy


theorem omega_norm_formula : Formalism.FourierDecayAlt.OmNorm := by
  intro V _ _ ip hadd hsmul hconj z x T T' Dr hT hzz hxx
  have hadd2 : ∀ w x y, ip w (x + y) = ip w x + ip w y := by
    intro w x y
    rw [hconj (x + y) w, hadd, map_add, ← hconj, ← hconj]
  have hsmul2 : ∀ (s : ℂ) w y, ip w (s • y) = starRingEnd ℂ s * ip w y := by
    intro s w y
    rw [hconj (s • y) w, hsmul, map_mul, ← hconj]
  have hT0 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  set ζ := ip x z with hζ
  have hzx : ip z x = starRingEnd ℂ ζ := hconj x z
  constructor
  · rw [hsmul, hadd, hsmul, hzz]
    field_simp
    ring
  · rw [hsmul, hsmul2, hadd, hadd2, hadd2, hsmul, hsmul, hsmul2, hsmul2, hxx, hzz, hzx, ← hζ]
    apply Complex.ext
    · simp [Complex.normSq_apply, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
      field_simp
      ring
    · simp [Complex.normSq_apply, Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im]
      field_simp
      ring

end Formalism.FourierDecayAlt.P
