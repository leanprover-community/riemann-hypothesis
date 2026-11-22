module

public import Formalism.SharpRestriction.InertJacobiLevels.HostFam
public import Formalism.SharpRestriction.FamCore
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleNewtypesIdempotentZero
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.CyclotomicNorms.IrreducibilityOfGoodTuple

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition NumberField IsDedekindDomain
open scoped Pointwise

section General

variable {R : Ranks} (H : Host R)

theorem primesOver_ncard (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) :
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = (placesOver E p).ncard := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  have hpM : (Ideal.span {(p : ℤ)}).IsMaximal :=
    hpI.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpZ.ne_zero)
  have himg : (fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal) '' placesOver E p =
      (Ideal.span {(p : ℤ)}).primesOver (𝓞 E) := by
    ext I
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨v.isPrime, ⟨?_⟩⟩
      have hle : Ideal.span {(p : ℤ)} ≤ v.asIdeal.under ℤ := by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        change algebraMap ℤ (𝓞 E) p ∈ v.asIdeal
        have hv' : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal := hv
        simpa using hv'
      exact hpM.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top hle
    · rintro ⟨hI, hIl⟩
      have hmem : ((p : ℕ) : 𝓞 E) ∈ I := by
        have : (p : ℤ) ∈ I.under ℤ := by rw [← hIl.over]; exact Ideal.mem_span_singleton_self _
        simpa using this
      have hne : I ≠ ⊥ := by
        rintro rfl
        have h0 : ((p : ℕ) : 𝓞 E) = 0 := by simpa using hmem
        exact hp.ne_zero (by exact_mod_cast h0)
      exact ⟨⟨I, hI, hne⟩, hmem, rfl⟩
  rw [← himg, Set.ncard_image_of_injective _ (fun v w h => HeightOneSpectrum.ext h)]

end General

variable {R : Ranks} {x eps Cp CT : ℝ} (B : Base R x eps Cp CT)

namespace Base

end Base

end Formalism.MainNotions.Inhab

end
