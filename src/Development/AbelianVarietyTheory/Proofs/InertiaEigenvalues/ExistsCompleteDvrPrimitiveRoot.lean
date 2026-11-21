import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing

namespace GlobalTheory.CyclotomicCompletion

theorem exists_place_above (K : Type) [Field K] [NumberField K] {l : ℕ} (hl : l.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 K), (l : 𝓞 K) ∈ v.asIdeal := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl
  have : (Ideal.span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  obtain ⟨Q, hQ, hQ'⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
    (S := 𝓞 K) (Ideal.span {(l : ℤ)}) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int (algebraMap ℤ (𝓞 K)))]; exact bot_le)
  have hmem : (l : 𝓞 K) ∈ Q := by
    have : (l : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      rw [hQ']; exact Ideal.mem_span_singleton_self _
    simpa [Ideal.mem_comap] using this
  refine ⟨⟨Q, hQ, ?_⟩, hmem⟩
  rintro rfl
  exact hl.ne_zero (by simpa using hmem)


end GlobalTheory.CyclotomicCompletion
