import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.ValSurjective

section
open NumberField IsDedekindDomain

namespace PI.LocalEndW

theorem localEndHomeo_of (hA : HenselRoot) (hB1 : IntOfHensel) (hB2 : ValOfInt)
    (hC1 : ValContinuous) (hC2 : ValSurjective) : PI.LocalEndHomeo := by
  have hV : ValPreserved := hB2 (hB1 hA)
  intro F _ _ v τ
  have hτv : ∀ x, Valued.v (τ x) = Valued.v x := hV F v τ
  have hsurj := hC2 F v τ hτv
  let e := RingEquiv.ofBijective τ ⟨τ.injective, hsurj⟩
  refine ⟨hC1 F v τ hτv, e.symm.toRingHom, ?_, fun a => e.apply_symm_apply a⟩
  apply hC1 F v
  intro x
  have := hτv (e.symm x)
  rw [show τ (e.symm x) = x from e.apply_symm_apply x] at this
  exact this.symm

end PI.LocalEndW
end

section
open NumberField IsDedekindDomain Uniformity

namespace PI.LocalEndW

theorem isUniformInducing_of_val {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    (τ : v.adicCompletion F →+* v.adicCompletion F) (hτ : ∀ x, Valued.v (τ x) = Valued.v x) :
    IsUniformInducing τ := by
  have hb := Valued.hasBasis_uniformity (v.adicCompletion F) _
  have hτ' : ∀ y, Valued.v.restrict (τ y) = Valued.v.restrict y := fun y =>
    le_antisymm
      (not_lt.1 fun h => lt_irrefl (Valued.v y) (by rw [Valuation.restrict_lt_iff, hτ] at h; exact h))
      (not_lt.1 fun h => lt_irrefl (Valued.v y) (by rw [Valuation.restrict_lt_iff, hτ] at h; exact h))
  refine ⟨(hb.comap _).ext hb (fun γ _ => ⟨γ, trivial, ?_⟩) (fun γ _ => ⟨γ, trivial, ?_⟩)⟩
  · intro p hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hp ⊢
    rw [← map_sub, hτ']
    exact hp
  · intro p hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hp ⊢
    rwa [← map_sub, hτ'] at hp

theorem valContinuous : ValContinuous := fun _ _ _ _ τ hτ => (isUniformInducing_of_val τ hτ).uniformContinuous.continuous

end PI.LocalEndW
end

section
open NumberField IsDedekindDomain Polynomial

namespace PI.LocalEndW

private theorem aeval_ringHom_apply_lemma {L M : Type*} [Field L] [Field M] [Algebra ℚ L] [Algebra ℚ M]
    (φ : L →+* M) (p : ℚ[X]) (x : L) : aeval (φ x) p = φ (aeval x p) := by
  rw [aeval_def, aeval_def, hom_eval₂, RingHom.ext_rat (φ.comp (algebraMap ℚ L)) (algebraMap ℚ M)]

theorem algebraMap_mem_range {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    (τ : v.adicCompletion F →+* v.adicCompletion F) (a : F) :
    algebraMap F (v.adicCompletion F) a ∈ Set.range τ := by
  set K := v.adicCompletion F
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  let _ : Algebra ℚ K := DivisionRing.toRatAlgebra
  set p := minpoly ℚ a with hp
  have hp0 : p ≠ 0 := minpoly.ne_zero (IsIntegral.of_finite ℚ a)
  set S : Set K := p.rootSet K
  have hmem : ∀ x : K, x ∈ S ↔ aeval x p = 0 := fun x => by
    rw [mem_rootSet]
    exact ⟨fun h => h.2, fun h => ⟨hp0, h⟩⟩
  have haS : algebraMap F K a ∈ S := by
    rw [hmem, aeval_ringHom_apply_lemma (algebraMap F K) p a, hp, minpoly.aeval, map_zero]
  have hmaps : Set.MapsTo τ S S := fun x hx => by
    rw [hmem] at hx ⊢
    rw [aeval_ringHom_apply_lemma τ p x, hx, map_zero]
  have : Finite S := (rootSet_finite p K).to_subtype
  let g : S → S := hmaps.restrict τ S S
  have hg : Function.Injective g := fun x y h => Subtype.ext (τ.injective (congrArg Subtype.val h))
  obtain ⟨r, hr⟩ := Finite.surjective_of_injective hg ⟨algebraMap F K a, haS⟩
  exact ⟨r.1, congrArg Subtype.val hr⟩

private theorem denseRange_algebraMap_adicCompletion_lemma_2 {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : DenseRange (algebraMap F (v.adicCompletion F)) := by
  exact HeightOneSpectrum.denseRange_algebraMap F v

theorem valSurjective : ValSurjective := by
  intro F _ _ v τ hτ y
  have hclosed : IsClosed (Set.range τ) :=
    (isUniformInducing_of_val τ hτ).isComplete_range.isClosed
  have hdense : Dense (Set.range τ) :=
    (denseRange_algebraMap_adicCompletion_lemma_2 v).mono (by
      rintro _ ⟨a, rfl⟩
      exact algebraMap_mem_range τ a)
  have huniv := hdense.closure_eq
  rw [hclosed.closure_eq] at huniv
  have hy : y ∈ Set.range τ := huniv ▸ Set.mem_univ y
  exact hy

end PI.LocalEndW
end

section
namespace PI.LocalEndW

theorem localEndHomeo_of_three (hA : HenselRoot) (hB1 : IntOfHensel) (hB2 : ValOfInt) :
    PI.LocalEndHomeo :=
  localEndHomeo_of hA hB1 hB2 valContinuous valSurjective

end PI.LocalEndW
end
