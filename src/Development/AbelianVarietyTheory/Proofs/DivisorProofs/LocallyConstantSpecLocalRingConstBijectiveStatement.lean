import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem locallyConstant_spec_local_eq_closedPoint {R A : Type} [CommRing A] [IsLocalRing A]
    (f : LocallyConstant (Spec (CommRingCat.of A)) R) (x : Spec (CommRingCat.of A)) :
    f x = f (IsLocalRing.closedPoint A : PrimeSpectrum A) := by
  have hx : (x : PrimeSpectrum A) ⤳ IsLocalRing.closedPoint A :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal (x : PrimeSpectrum A).isPrime.ne_top)
  have ho : IsOpen (f ⁻¹' {f (IsLocalRing.closedPoint A : PrimeSpectrum A)}) := f.isLocallyConstant _
  exact hx.mem_open ho rfl

theorem locallyConstant_spec_local_bijective :
    ∀ (R : Type) (A : Type) [CommRing A] [IsLocalRing A],
      Function.Bijective (fun c : R => LocallyConstant.const (Spec (CommRingCat.of A)) c) := by
  intro R A _ _
  refine ⟨fun c d h => ?_, fun f => ⟨f (IsLocalRing.closedPoint A : PrimeSpectrum A), ?_⟩⟩
  · have := congrArg (fun g : LocallyConstant (Spec (CommRingCat.of A)) R =>
      g (IsLocalRing.closedPoint A : PrimeSpectrum A)) h
    exact this
  · ext x
    simp only [LocallyConstant.coe_const, Function.const_apply]
    exact (locallyConstant_spec_local_eq_closedPoint f x).symm

end GlobalTheory
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locallyConstant_spec_localRing_const_bijective : ∀ (R : Type) (A : Type) [CommRing A] [IsLocalRing A], Function.Bijective (fun c : R => LocallyConstant.const (Spec (CommRingCat.of A)) c) := by
  first | (exact @GlobalTheory.locallyConstant_spec_local_bijective) | (exact GlobalTheory.locallyConstant_spec_local_bijective) | (intros; apply GlobalTheory.locallyConstant_spec_local_bijective  <;> assumption)
end
