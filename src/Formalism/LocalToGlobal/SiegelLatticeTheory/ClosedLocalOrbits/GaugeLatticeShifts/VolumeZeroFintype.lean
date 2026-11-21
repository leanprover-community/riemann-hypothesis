import Mathlib

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

def PF (ι : Type*) : Subalgebra ℂ ((ι → ℝ) → ℂ) :=
  (MvPolynomial.aeval (R := ℂ) (fun i (y : ι → ℝ) => (y i : ℂ))).range





end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames
