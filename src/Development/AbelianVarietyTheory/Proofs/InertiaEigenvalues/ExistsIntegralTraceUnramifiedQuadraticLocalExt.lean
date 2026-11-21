import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceIntOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralIntegersUnramifiedInvolutionExtStatement
import BuildAid.ForwardExisting

section
namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem trace_int : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ y : K'.O,
    ∃ a : K.O, @Algebra.trace K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E y) = algebraMap K.O K.E a :=
  fun K K' d φ hU y => trace_int_of_isIntegral hU _ (GlobalTheory.T.isIntegral_integers_unramifiedInvolutionExt K K' d φ hU hU.ne_zero y)

end GlobalTheory.UnitLemma.Unr
end

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_trace_unramifiedQuadraticLocalExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ y : K'.O, ∃ a : K.O, @Algebra.trace K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E y) = algebraMap K.O K.E a := by
  atlas_forward_decl GlobalTheory.UnitLemma.Unr.trace_int
