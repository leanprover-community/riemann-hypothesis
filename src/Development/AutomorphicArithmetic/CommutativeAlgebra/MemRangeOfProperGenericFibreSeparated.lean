import Mathlib
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField

section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

private lemma aux {W S T U : Scheme.{0}} (w : W ⟶ S) (i : T ⟶ S) (j : U ⟶ T) (g : U ⟶ S)
    (hg : j ≫ i = g) [Flat j] [IsPreimmersion i] (y' : ↑(pullback w g)) (x : W)
    (hx : x ⤳ (pullback.fst w g) y') (hxr : x ∈ Set.range (pullback.fst w i)) :
    ∃ x' : ↑(pullback w g), x' ⤳ y' ∧ (pullback.fst w g) x' = x := by
  subst hg
  have hfst : ∀ p, (pullback.fst w (j ≫ i)) ((pullbackLeftPullbackSndIso w i j).hom p) =
      (pullback.fst w i) ((pullback.fst (pullback.snd w i) j) p) := by
    intro p
    show ((pullbackLeftPullbackSndIso w i j).hom ≫ pullback.fst w (j ≫ i)).base p =
      (pullback.fst (pullback.snd w i) j ≫ pullback.fst w i).base p
    rw [pullbackLeftPullbackSndIso_hom_fst]
  have hy : (pullbackLeftPullbackSndIso w i j).hom ((pullbackLeftPullbackSndIso w i j).inv y') = y' := by
    show ((pullbackLeftPullbackSndIso w i j).inv ≫ (pullbackLeftPullbackSndIso w i j).hom).base y' = y'
    rw [Iso.inv_hom_id]
    rfl
  obtain ⟨z, hz⟩ := hxr
  have hxz : z ⤳ (pullback.fst (pullback.snd w i) j) ((pullbackLeftPullbackSndIso w i j).inv y') := by
    rw [← (IsPreimmersion.isEmbedding (pullback.fst w i)).isInducing.specializes_iff, hz, ← hfst, hy]
    exact hx
  obtain ⟨x'', hx'', hx''z⟩ := Flat.generalizingMap (pullback.fst (pullback.snd w i) j) hxz
  refine ⟨(pullbackLeftPullbackSndIso w i j).hom x'', ?_, ?_⟩
  · rw [← hy]
    exact hx''.map (Scheme.Hom.continuous _)
  · rw [hfst, hx''z, hz]

private lemma spec_bot {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    (f : A →+* B) (hf : Function.Injective f) :
    Spec.map (CommRingCat.ofHom f) (⊥ : PrimeSpectrum B) = (⊥ : PrimeSpectrum A) := by
  apply PrimeSpectrum.ext
  exact Ideal.comap_bot_of_injective f hf

private lemma spec_field {F : Type} [Field F] (z : PrimeSpectrum F) : z = ⊥ :=
  PrimeSpectrum.ext (Ideal.eq_bot_of_prime _)

private lemma spec_gen {A : Type} [CommRing A] [IsDomain A] (a : PrimeSpectrum A)
    (h : a ⤳ (⊥ : PrimeSpectrum A)) : a = ⊥ :=
  le_bot_iff.1 ((PrimeSpectrum.le_iff_specializes _ _).2 h)

theorem UpperTheory.exists_specializes_lift_generic_base_change :
    ∀ (R Ω : Type) [CommRing R] [IsDomain R] [Field Ω] [Algebra R Ω], Function.Injective (algebraMap R Ω) → ∀ {W : Scheme.{0}} (w : W ⟶ Sp R) (y' : ↑(pullback w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))) (x : W), x ⤳ (pullback.fst w (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) y' → ∃ x' : ↑(pullback w (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))), x' ⤳ y' ∧ (pullback.fst w (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) x' = x := by
  intro R Ω _ _ _ _ hinj W w y' x hx
  have hRK : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  letI : Algebra (FractionRing R) Ω := (IsFractionRing.lift hinj : FractionRing R →+* Ω).toAlgebra
  haveI : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have hcomp : (algebraMap (FractionRing R) Ω).comp (algebraMap R (FractionRing R)) =
      algebraMap R Ω := IsLocalization.lift_comp _
  have hg : Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) Ω)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R Ω)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  apply aux w (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) Ω))) _ hg y' x hx
  have hwx : (show PrimeSpectrum R from w x) = ⊥ := by
    apply spec_gen
    have h1 := hx.map w.continuous
    have h2 : w (pullback.fst w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) y') =
        Spec.map (CommRingCat.ofHom (algebraMap R Ω))
          (pullback.snd w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) y') := by
      show (pullback.fst w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ≫ w).base y' =
        (pullback.snd w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R Ω))).base y'
      rw [pullback.condition]
    rw [h2, spec_field (pullback.snd w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) y'),
      spec_bot _ hinj] at h1
    exact h1
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := w)
    (g := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) x
    (⊥ : PrimeSpectrum (FractionRing R)) (by
      show (show PrimeSpectrum R from w x) = _
      rw [hwx, spec_bot _ hRK])
  exact ⟨z, hz⟩
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

set_option maxHeartbeats 400000 in
theorem UpperTheory.mem_range_of_proper_generic_fibre_separated :
    ∀ (R Ω : Type) [CommRing R] [IsDomain R] [Field Ω] [Algebra R Ω], Function.Injective (algebraMap R Ω) → ∀ {B Y D C : Scheme.{0}} (ι : Sp R ⟶ B) [IsOpenImmersion ι] (π : Y ⟶ B) [IsSeparated π] [IrreducibleSpace Y] (j : D ⟶ Y) [IsOpenImmersion j], Dense (Set.range j) → ∀ (q : D ⟶ Sp R), j ≫ π = q ≫ ι → ∀ (c : C ⟶ Sp Ω) [IsProper c] (v : C ⟶ D), IsPullback v c q (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) → ∀ (y : Y), π y ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap R Ω)) ≫ ι) → y ∈ Set.range j := by
  intro R Ω _ _ _ _ hinj B Y D C ι _ π _ _ j _ hd q hq c _ v hpb y hy
  set g := Spec.map (CommRingCat.ofHom (algebraMap R Ω)) with hg
  let U' : Y.Opens := π ⁻¹ᵁ ι.opensRange
  have hjU : Set.range j ⊆ Set.range U'.ι := by
    rintro _ ⟨d, rfl⟩
    rw [Scheme.Opens.range_ι]
    show π (j d) ∈ ι.opensRange
    rw [← Scheme.Hom.comp_apply, hq, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let jU : D ⟶ U' := IsOpenImmersion.lift U'.ι j hjU
  have hjUf : jU ≫ U'.ι = j := IsOpenImmersion.lift_fac _ _ _
  have hπU : Set.range (U'.ι ≫ π) ⊆ Set.range ι := by
    rintro _ ⟨z, rfl⟩
    exact z.2
  let w : (U' : Scheme) ⟶ Sp R := IsOpenImmersion.lift ι (U'.ι ≫ π) hπU
  have hw : w ≫ ι = U'.ι ≫ π := IsOpenImmersion.lift_fac _ _ _
  have hjw : jU ≫ w = q := by
    rw [← cancel_mono ι, Category.assoc, hw, ← Category.assoc, hjUf, hq]
  haveI : IsSeparated (w ≫ ι) := by rw [hw]; infer_instance
  haveI : IsSeparated w := IsSeparated.of_comp w ι
  let m : C ⟶ pullback w g := pullback.lift (v ≫ jU) c (by rw [Category.assoc, hjw, hpb.w])
  have hm : m ≫ pullback.snd w g = c := pullback.lift_snd _ _ _
  haveI : UniversallyClosed (m ≫ pullback.snd w g) := by rw [hm]; infer_instance
  haveI : UniversallyClosed m := UniversallyClosed.of_comp_of_isSeparated m (pullback.snd w g)
  have hleft : IsPullback m v (pullback.fst w g) jU := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback w g).flip
    rw [hm, hjw]
    exact hpb.flip
  have hI : hleft.isoPullback.inv ≫ m = pullback.fst (pullback.fst w g) jU :=
    (Iso.inv_comp_eq _).mpr hleft.isoPullback_hom_fst.symm
  have hrange : (pullback.fst w g) ⁻¹' Set.range jU ⊆ Set.range m := by
    intro z hz
    have e := IsOpenImmersion.range_pullbackFst jU (pullback.fst w g)
    have hz' : z ∈ Set.range (pullback.fst (pullback.fst w g) jU) := by
      rw [e]
      exact hz
    obtain ⟨t, rfl⟩ := hz'
    refine ⟨hleft.isoPullback.inv t, ?_⟩
    rw [← Scheme.Hom.comp_apply, hI]
  obtain ⟨p, hp⟩ := hy
  have hyU : y ∈ U' := by
    show π y ∈ ι.opensRange
    rw [← hp, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let yU : U' := ⟨y, hyU⟩
  have e1 : ι (w yU) = π y := by
    show (w ≫ ι) yU = π y
    rw [hw]
    rfl
  have hwy : w yU = g p := by
    apply ι.isOpenEmbedding.injective
    rw [e1, ← hp]
    rfl
  obtain ⟨y', hy'1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := w) (g := g) yU p hwy
  have hξ : genericPoint Y ∈ Set.range j := by
    rw [(genericPoint_spec Y).mem_open_set_iff j.isOpenEmbedding.isOpen_range, Set.univ_inter]
    exact hd.nonempty
  obtain ⟨d, hdξ⟩ := hξ
  have hsp : jU d ⤳ yU := by
    apply (U'.ι.isOpenEmbedding.isInducing.specializes_iff).mp
    have e2 : U'.ι (jU d) = genericPoint Y := by
      rw [← Scheme.Hom.comp_apply, hjUf, hdξ]
    rw [e2]
    exact (genericPoint_spec Y).specializes (Set.mem_univ _)
  obtain ⟨x', hx'sp, hx'fst⟩ := UpperTheory.exists_specializes_lift_generic_base_change R Ω hinj w y' (jU d) (by rw [hy'1]; exact hsp)
  have hx'm : x' ∈ Set.range m := hrange ⟨d, hx'fst.symm⟩
  have hy'm : y' ∈ Set.range m := hx'sp.mem_closed m.isClosedMap.isClosed_range hx'm
  obtain ⟨c0, hc0⟩ := hy'm
  refine ⟨v c0, ?_⟩
  have h1 : pullback.fst w g (m c0) = jU (v c0) := by
    rw [← Scheme.Hom.comp_apply, hleft.w, Scheme.Hom.comp_apply]
  rw [← hjUf, Scheme.Hom.comp_apply, ← h1, hc0, hy'1]
  rfl
end
