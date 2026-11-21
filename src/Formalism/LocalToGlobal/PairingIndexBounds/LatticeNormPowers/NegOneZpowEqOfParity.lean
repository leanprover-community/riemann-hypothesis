import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.RecursiveLatticeMembership.MemLamOfIff

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Xf

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

variable {D : D7} {N N' : ℕ}

theorem delta_ne_zero (D : D7) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hcc : IsCurveIdeal D cc)
    (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : δ ≠ 0 := by
  rintro rfl
  apply Formalism.L2.PairingIndexBounds.Rec.discrNZ D cc hcc
  unfold IsDiscriminantTwelfthRootOfIdealLattice at hδ
  rw [← hδ]
  norm_num


theorem Hf_nsmul_left (T : Tor D) (n : ℕ) (x y : VC D N N') :
    Hf D T (n • x) y = (n : ℂ) * Hf D T x y := by
  simp only [Hf, Pi.smul_apply, nsmul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_div_assoc]

theorem Hf_nsmul_right (T : Tor D) (n : ℕ) (x y : VC D N N') :
    Hf D T x (n • y) = (n : ℂ) * Hf D T x y := by
  rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_herm T (n • y) x, Hf_nsmul_left, map_mul, Complex.conj_natCast,
    ← Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_herm]

theorem qH_nsmul (T : Tor D) (n : ℕ) (x : VC D N N') :
    qH D T (n • x) = (n : ℝ) ^ 2 * qH D T x := by
  simp only [qH, Hf_nsmul_left, Hf_nsmul_right]
  have : ((n : ℂ) * ((n : ℂ) * Hf D T x x)).re = (n : ℝ) ^ 2 * (Hf D T x x).re := by
    rw [← mul_assoc, ← Nat.cast_mul]
    rw [show ((n * n : ℕ) : ℂ) = (((n * n : ℕ) : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
    push_cast; ring
  rw [this]; ring





theorem exp_pi_int (m : ℤ) : Complex.exp ((Real.pi : ℂ) * Complex.I * (m : ℂ)) = (-1 : ℂ) ^ m := by
  rw [show (Real.pi : ℂ) * Complex.I * (m : ℂ) = (m : ℂ) * ((Real.pi : ℂ) * Complex.I) by ring,
    Complex.exp_int_mul, Complex.exp_pi_mul_I]




end Formalism.L2.PairingIndexBounds.Xf

namespace Formalism.L2.PairingIndexBounds.Xf

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

variable {D : D7} {N N' : ℕ}


theorem cf_sq (T : Tor D) (x y : VC D N N') :
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.cf T x y ^ 2 = kap D T x y := by
  unfold Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.cf kap
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring



end Formalism.L2.PairingIndexBounds.Xf
