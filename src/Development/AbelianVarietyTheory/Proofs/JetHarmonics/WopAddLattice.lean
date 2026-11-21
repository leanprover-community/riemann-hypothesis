import Mathlib
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.JetMomTA
import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsTraceNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOddPrimePhaseConjInvariant
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.ParabolicPointMembership

namespace GlobalTheory.ThetaShift

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO

variable {D : D7} {N N' : ℕ}

theorem Hf_nsmul_left (T : Tor D) (n : ℕ) (x y : VC D N N') :
    Hf D T (n • x) y = (n : ℂ) * Hf D T x y := by
  induction n with
  | zero => simp [Hf]
  | succ n ih => rw [succ_nsmul, Hf_add_left, ih]; push_cast; ring

theorem Hf_nsmul_right (T : Tor D) (n : ℕ) (x y : VC D N N') :
    Hf D T x (n • y) = (n : ℂ) * Hf D T x y := by
  induction n with
  | zero => simp [Hf]
  | succ n ih => rw [succ_nsmul, Hf_add_right, ih]; push_cast; ring

theorem qH_nsmul (T : Tor D) (n : ℕ) (x : VC D N N') :
    qH D T (n • x) = (n : ℝ) ^ 2 * qH D T x := by
  unfold qH
  rw [Hf_nsmul_left, Hf_nsmul_right, ← Complex.ofReal_natCast, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul]
  ring


theorem qH_add (T : Tor D) (x w : VC D N N') :
    qH D T (x + w) = qH D T x + qH D T w + Real.sqrt D.host.d * (Hf D T x w).re := by
  unfold qH
  rw [Hf_add_left, Hf_add_right, Hf_add_right, Complex.add_re, Complex.add_re, Complex.add_re,
    Hf_re_swap T x w]
  ring



end GlobalTheory.ThetaShift
