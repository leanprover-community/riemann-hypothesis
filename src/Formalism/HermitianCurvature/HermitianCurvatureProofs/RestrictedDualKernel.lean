import Formalism.HermitianCurvature.HermitianCurvatureProofs.DualKernelLemmas

namespace Formalism.FourierDecayAlt.P.RestrictedDualKernel

open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas
open scoped Matrix ComplexOrder

section Rep

variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
  [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]


theorem pos_mul {c u : ℂ} (hc : 0 < c) (hu : 0 ≤ u.re ∧ u.im = 0) : 0 ≤ (c * u).re ∧ (c * u).im = 0 := by
  obtain ⟨h1, h2⟩ := Complex.pos_iff.mp hc
  have hci : c.im = 0 := by linarith
  rw [Complex.mul_re, Complex.mul_im, hci, hu.2]
  constructor
  · nlinarith [hu.1]
  · ring

end Rep



end Formalism.FourierDecayAlt.P.RestrictedDualKernel

