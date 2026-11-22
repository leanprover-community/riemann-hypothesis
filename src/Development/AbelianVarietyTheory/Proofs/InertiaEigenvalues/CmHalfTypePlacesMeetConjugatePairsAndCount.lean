module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SplitPlaceTypes
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.SplitRowIffOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimePlaceCmTypeConjugateStatement

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.SplitCount

theorem locDeg_mul_ncard (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] {l : ℕ} (hl : l.Prime) :
    (placesOver E l).Finite ∧
      ∀ w ∈ placesOver E l, locDeg E w * (placesOver E l).ncard = Module.finrank ℚ E := by
  have : IsGaloisGroup Gal(E/ℚ) ℤ (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ E
  have hp : (Ideal.span {(l : ℤ)}).IsPrime :=
    (PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible).isPrime
  have hinj : Function.Injective (HeightOneSpectrum.asIdeal : HeightOneSpectrum (𝓞 E) → _) :=
    fun _ _ h => HeightOneSpectrum.ext h
  have him : HeightOneSpectrum.asIdeal '' placesOver E l = (Ideal.span {(l : ℤ)}).primesOver (𝓞 E) := by
    ext P
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.isPrime, GlobalTheory.HubLoc.liesOver_of_mem hl hv⟩
    · rintro ⟨hP, hlo⟩
      have hm : ((l : ℕ) : 𝓞 E) ∈ P := by
        have : (l : ℤ) ∈ P.under ℤ := by
          rw [← hlo.over]; exact Ideal.mem_span_singleton_self _
        simpa [Ideal.under, Ideal.mem_comap] using this
      refine ⟨⟨P, hP, ?_⟩, hm, rfl⟩
      rintro rfl
      exact hl.ne_zero (by simpa using hm)
  refine ⟨Set.Finite.of_finite_image (him ▸ Algebra.QuasiFinite.finite_primesOver _) hinj.injOn, fun w hw => ?_⟩
  have := GlobalTheory.HubLoc.liesOver_of_mem hl hw
  have := w.isPrime
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (Ideal.span {(l : ℤ)}) (𝓞 E) Gal(E/ℚ)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(l : ℤ)}) w.asIdeal Gal(E/ℚ),
    Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(l : ℤ)}) w.asIdeal Gal(E/ℚ), ← him,
    Set.ncard_image_of_injective _ hinj, IsGalois.card_aut_eq_finrank] at h
  rw [← h, mul_comm]
  rfl

section Host
variable {R : Ranks} (H : Host R)

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  obtain ⟨φ⟩ : Nonempty (H.E →+* ℂ) := inferInstance
  apply φ.injective
  rw [GlobalTheory.SplitRowProbe.conj_sqrt, GlobalTheory.SplitRowProbe.conj_sqrt, starRingEnd_self_apply]

def cInt : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv

theorem cInt_coe (x : 𝓞 H.E) : (cInt H x : H.E) = H.conj (x : H.E) := rfl

theorem cInt_cInt (x : 𝓞 H.E) : cInt H (cInt H x) = x :=
  RingOfIntegers.ext (by rw [cInt_coe, cInt_coe, conj_conj])

def cPl (w : HeightOneSpectrum (𝓞 H.E)) : HeightOneSpectrum (𝓞 H.E) :=
  HeightOneSpectrum.comap (cInt H).toRingHom (cInt H).surjective w

theorem mem_cPl (w : HeightOneSpectrum (𝓞 H.E)) (x : 𝓞 H.E) :
    x ∈ (cPl H w).asIdeal ↔ cInt H x ∈ w.asIdeal := Iff.rfl

theorem cPl_cPl (w : HeightOneSpectrum (𝓞 H.E)) : cPl H (cPl H w) = w :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [mem_cPl, mem_cPl, cInt_cInt])

theorem isConjPl_cPl (w : HeightOneSpectrum (𝓞 H.E)) : IsConjPl H w (cPl H w) := by
  intro x y h
  have : y = cInt H x := RingOfIntegers.ext h
  rw [this, mem_cPl, cInt_cInt]

theorem mem_placesOver_of_conj {l : ℕ} {w w' : HeightOneSpectrum (𝓞 H.E)} (hw : w ∈ placesOver H.E l)
    (h : IsConjPl H w w') : w' ∈ placesOver H.E l :=
  (h (l : 𝓞 H.E) (l : 𝓞 H.E) (by simp)).1 hw

end Host

end GlobalTheory.SplitCount

end
