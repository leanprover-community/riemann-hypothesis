import Development.EtaleCohomology.CohomologicalPurity.LeafThomCut

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

theorem sqw {R : Type} [CommRing R] {K L K' L' : Cx R} {f : K ⟶ L} {f' : K' ⟶ L'} {a : K ⟶ K'} {b : L ⟶ L'}
    (comm : f ≫ b = a ≫ f') (n : ℤ) : f.f n ≫ b.f n = a.f n ≫ f'.f n := by
  rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, comm]

theorem chains_sq (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) :
    (chains R).map P'.hom ≫ (chains R).map φ.right = (chains R).map φ.left ≫ (chains R).map P.hom := by
  rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg (chains R).map (Arrow.w φ).symm

def coneMap (R : Type) [CommRing R] {P' P : Arrow Spc} (φ : P' ⟶ P) :
    CochainComplex.mappingCone ((chains R).map P'.hom) ⟶ CochainComplex.mappingCone ((chains R).map P.hom) :=
  CochainComplex.mappingCone.map _ _ ((chains R).map φ.left) ((chains R).map φ.right) (chains_sq R φ)

def LeafConeQI : Prop := ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P), IsPullback P'.hom φ.left φ.right P.hom →
  Cover2 (ZMod q) φ.right P.hom → QuasiIso (coneMap (ZMod q) φ)

def LeafHsRel : Prop := A1 → ∀ (q : ℕ) (i : ℤ), ∃ e : ∀ (P : Arrow Spc) (n : ℤ), Mono P.hom →
    (Hs q P n i ≃+ Hrel (ZMod q) P.hom (tw q i) n),
  ∀ (P' P : Arrow Spc) (φ : P' ⟶ P) (h' : Mono P'.hom) (h : Mono P.hom) (n : ℤ) (x : Hs q P n i),
    e P' n h' (Hs.pull q φ n i x) = HK.pull (ZMod q) (coneMap (ZMod q) φ) (tw q i) n (e P n h x)

def LeafChainsMono : Prop := ∀ (R : Type) [CommRing R] {E' E : Spc} (f : E' ⟶ E), Mono f → ∀ n : ℤ, Mono (((chains R).map f).f n)

def LeafCokIso : Prop := ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P), IsPullback P'.hom φ.left φ.right P.hom →
  Cover2 (ZMod q) φ.right P.hom → ∀ n : ℤ,
  IsIso (cokernel.map _ _ _ _ (sqw (chains_sq (ZMod q) φ) n))

def LeafConeCok : Prop := ∀ (R : Type) [CommRing R] {K L K' L' : Cx R} (f : K ⟶ L) (f' : K' ⟶ L')
  (a : K ⟶ K') (b : L ⟶ L') (comm : f ≫ b = a ≫ f'), (∀ n, Mono (f.f n)) → (∀ n, Mono (f'.f n)) →
  (∀ n, IsIso (cokernel.map _ _ _ _ (sqw comm n))) → QuasiIso (CochainComplex.mappingCone.map f f' a b comm)

theorem leafExcSp_of (hQ : LeafConeQI) (hR : LeafHsRel) : LeafExcSp := by
  intro h1 q P' P φ hpb hc n i
  have hm : Mono P.hom := hc.2.1
  have hm' : Mono P'.hom := hpb.mono_fst_of_mono
  obtain ⟨e, he⟩ := hR h1 q i
  have := hQ q φ hpb hc
  have hb : Function.Bijective (HK.pull (ZMod q) (coneMap (ZMod q) φ) (tw q i) n) := h1 (ZMod q) _ (tw q i) n
  have : (Hs.pull q φ n i : Hs q P n i → Hs q P' n i) =
      (e P' n hm').symm ∘ HK.pull (ZMod q) (coneMap (ZMod q) φ) (tw q i) n ∘ e P n hm := by
    funext x
    simp [← he P' P φ hm' hm n x]
  rw [this]
  exact (e P' n hm').symm.bijective.comp (hb.comp (e P n hm).bijective)

theorem leafConeQI_of (hM : LeafChainsMono) (hK : LeafCokIso) (hC : LeafConeCok) : LeafConeQI := by
  intro q P' P φ hpb hc
  have hm : Mono P.hom := hc.2.1
  have hm' : Mono P'.hom := hpb.mono_fst_of_mono
  exact hC (ZMod q) _ _ _ _ (chains_sq (ZMod q) φ) (hM _ _ hm') (hM _ _ hm) (hK q φ hpb hc)

theorem leafExcSp_of' (hM : LeafChainsMono) (hK : LeafCokIso) (hC : LeafConeCok) (hR : LeafHsRel) : LeafExcSp :=
  leafExcSp_of (leafConeQI_of hM hK hC) hR

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end

section
noncomputable section
open CategoryTheory Limits

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

open GlobalTheory.EtC in
theorem leafConeCok : LeafConeCok := by
  intro R _ K L K' L' f f' a b comm hf hf' hi
  have hm : Mono f := HomologicalComplex.mono_of_mono_f _ hf
  have hm' : Mono f' := HomologicalComplex.mono_of_mono_f _ hf'
  let S₁ := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  let S₂ := ShortComplex.mk f' (cokernel.π f') (cokernel.condition f')
  have h₁ : S₁.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)) hm inferInstance
  have h₂ : S₂.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f')) hm' inferInstance
  let τ : S₁ ⟶ S₂ := { τ₁ := a, τ₂ := b, τ₃ := cokernel.map f f' a b comm, comm₁₂ := comm.symm, comm₂₃ := by simp [S₁, S₂] }
  have iso3 : IsIso (cokernel.map f f' a b comm) := by
    have : ∀ n, IsIso ((cokernel.map f f' a b comm).f n) := by
      intro n
      have e₁ := (h₁.map_of_exact (HomologicalComplex.eval _ _ n)).gIsCokernel
      have e₂ := (h₂.map_of_exact (HomologicalComplex.eval _ _ n)).gIsCokernel
      let i₁ : cokernel (f.f n) ≅ (cokernel f).X n := (colimit.isColimit _).coconePointUniqueUpToIso e₁
      let i₂ : cokernel (f'.f n) ≅ (cokernel f').X n := (colimit.isColimit _).coconePointUniqueUpToIso e₂
      have key : (cokernel.map f f' a b comm).f n = i₁.inv ≫ cokernel.map _ _ _ _ (sqw comm n) ≫ i₂.hom := by
        rw [Iso.eq_inv_comp]
        refine (cancel_epi (cokernel.π (f.f n))).1 ?_
        have p₁ : cokernel.π (f.f n) ≫ i₁.hom = (cokernel.π f).f n :=
          (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom e₁ WalkingParallelPair.one
        have p₂ : cokernel.π (f'.f n) ≫ i₂.hom = (cokernel.π f').f n :=
          (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom e₂ WalkingParallelPair.one
        rw [← Category.assoc, p₁, cokernel.π_desc_assoc, Category.assoc, p₂, ← HomologicalComplex.comp_f,
          ← HomologicalComplex.comp_f, cokernel.π_desc]
      rw [key]; infer_instance
    exact HomologicalComplex.Hom.isIso_of_components _
  have q1 := CochainComplex.mappingCone.quasiIso_descShortComplex h₁
  have q2 := CochainComplex.mappingCone.quasiIso_descShortComplex h₂
  have e := CochainComplex.mappingCone.map_descShortComplex S₁ S₂ τ
  have : QuasiIso (CochainComplex.mappingCone.map f f' a b comm ≫ CochainComplex.mappingCone.descShortComplex S₂) := by
    rw [show CochainComplex.mappingCone.map f f' a b comm = CochainComplex.mappingCone.map S₁.f S₂.f τ.τ₁ τ.τ₂ τ.comm₁₂.symm from rfl, e]
    infer_instance
  exact (quasiIso_iff_comp_right _ (CochainComplex.mappingCone.descShortComplex S₂)).1 this

theorem etaleSplitExcision_of_mono_cokernel_relative (hM : LeafChainsMono) (hK : LeafCokIso) (hR : LeafHsRel) : LateralTheory.CohomologicalPurity.Thom.LeafExcSp :=
  leafExcSp_of' hM hK leafConeCok hR

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end

section
noncomputable section
open CategoryTheory Limits Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcSp

theorem free_mono (R : Type) [CommRing R] {A B : PSh} (g : A ⟶ B) [Mono g] : Mono ((free R).map g) := by
  have : Mono ((freeP R).map g) := by
    rw [NatTrans.mono_iff_mono_app]
    intro U
    have hg : Function.Injective (g.app U) := (mono_iff_injective _).1 (inferInstance)
    rw [ModuleCat.mono_iff_injective]
    change Function.Injective ((ModuleCat.free (ULift.{1} R)).map (uliftFunctor.{1}.map (g.app U))).hom
    have hu : Function.Injective (uliftFunctor.{1}.map (g.app U)) := by
      intro a b h
      exact ULift.ext _ _ (hg (congrArg ULift.down h))
    exact Finsupp.mapDomain_injective hu
  change Mono ((presheafToSheaf _ _).map ((freeP R).map g))
  infer_instance

theorem leafChainsMono : LeafChainsMono := by
  intro R _ E' E f hf n
  by_cases hn : ∃ p : ℕ, -(p : ℤ) = n
  · obtain ⟨p, rfl⟩ := hn
    have h : ComplexShape.embeddingDownNat.f p = -(p : ℤ) := rfl
    change Mono ((HomologicalComplex.extendMap ((chainsN R).map f) _).f _)
    rw [HomologicalComplex.extendMap_f _ _ h]
    have : Mono (f.app (op (SimplexCategory.mk p))) := by
      rw [NatTrans.mono_iff_mono_app] at hf
      exact hf _
    have : Mono (((chainsN R).map f).f p) := by
      change Mono ((AlgebraicTopology.AlternatingFaceMapComplex.map _).f p)
      rw [AlgebraicTopology.AlternatingFaceMapComplex.map_f]
      exact free_mono R _
    infer_instance
  · push Not at hn
    refine ⟨fun g h _ => ?_⟩
    exact (HomologicalComplex.isZero_extend_X _ _ _ (fun i => hn i)).eq_of_tgt _ _

theorem etaleSplitExcision_of_cokernel_relative (hK : LeafCokIso) (hR : LeafHsRel) : LateralTheory.CohomologicalPurity.Thom.LeafExcSp :=
  etaleSplitExcision_of_mono_cokernel_relative leafChainsMono hK hR

end LateralTheory.CohomologicalPurity.Thom.ExcSp
end
end
