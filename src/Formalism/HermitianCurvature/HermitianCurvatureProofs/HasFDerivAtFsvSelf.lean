module

public import Formalism.HermitianCurvature.TopEntryWaveEquation
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FsvMulFsvNeg

@[expose] public section

open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem contDiff_fsv (s : ℂ) : ContDiff ℝ ∞ (fsv s) := by
  have hL : ContDiff ℝ ∞ (fun t : ℂ => s * t - conj s * conj t) :=
    (contDiff_const.mul contDiff_id).sub (contDiff_const.mul Complex.conjCLE.contDiff)
  exact Complex.contDiff_exp.comp hL

section PairNeg

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

end PairNeg

end Formalism.FourierDecayAlt.P5
