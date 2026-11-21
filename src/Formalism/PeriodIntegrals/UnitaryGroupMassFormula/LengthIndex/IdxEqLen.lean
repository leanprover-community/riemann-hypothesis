import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LengthIndex.MemDualLat

noncomputable section

namespace PI.Dv.ProjAW

open NumberField IsDedekindDomain Formalism.BasicNotions

section

variable {K : Type} [Field K] [NumberField K] [StarRing K] (A : HLat K)

lemma idx_le (hI : IdxCalc) (hG : A.Good) {f : Module.End K A.V} (hf : f * f = f) {n : ℕ}
    (hn0 : 0 < n) (hn : ∀ x ∈ A.L, ((n : ℕ) : 𝓞 K) • f x ∈ A.L) (w : HeightOneSpectrum (𝓞 K)) :
    idxAt w (imgE A f A.L) (cutE A f A.L) ≤ (dimE A f : ℤ) * vAdd w ((n : ℕ) : K) := by
  have h := (hI K A.V w (imgE A f A.L) (cutE A f A.L) (fg_img A hG f) (fg_cut A hG f)
    (span_cut_eq A hf hn0 hn)).2.2.2.2.2 n hn0 (part2 A hf) (part1 A hn)
  rwa [rk_img A hG f] at h


end


end PI.Dv.ProjAW

