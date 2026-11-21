import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CompEqOneIffPush
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InverseBundleGeneratorPointOfChartUnitsSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSchemeFunctorIsSheafZariskiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertChartRepresentableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenAffineHilbertChartBasicLocusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineHilbertChartBasicNeighbourhoodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertRepresentingUniversalSubscheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataComapIdealTopOfIsAffine
import BuildAid.ForwardExisting

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbert_representing_universal_subscheme : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ) (H : Scheme.{0}) (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H), ∃ (U : Scheme.{0}) (u : U ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) (R.homEquiv (𝟙 H)).1), IsClosedImmersion u ∧ IsFinite (u ≫ pullback.snd _ (R.homEquiv (𝟙 H)).1) ∧ Flat (u ≫ pullback.snd _ (R.homEquiv (𝟙 H)).1) ∧ (∀ y, (u ≫ pullback.snd _ (R.homEquiv (𝟙 H)).1).finrank y = r) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Spec (CommRingCat.of A)) (V : Scheme.{0}) (v : V ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) g), IsClosedImmersion v → IsFinite (v ≫ pullback.snd _ g) → Flat (v ≫ pullback.snd _ g) → (∀ y, (v ≫ pullback.snd _ g).finrank y = r) → ∃! f : T ⟶ H, ∃ hf : f ≫ (R.homEquiv (𝟙 H)).1 = g, ∃ w : V ⟶ U, IsPullback v w (pullback.map _ g _ (R.homEquiv (𝟙 H)).1 (𝟙 _) f (𝟙 _) (by simp) (by rw [Category.comp_id, hf])) u := by
  first | (exact @GlobalTheory.HilbAff.universal) | (exact GlobalTheory.HilbAff.universal) | (intros; apply GlobalTheory.HilbAff.universal  <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

theorem representing_qc_qs_loft : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (r : ℕ) (H : Scheme.{0})
    (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H),
    QuasiCompact (R.homEquiv (𝟙 H)).1 ∧ QuasiSeparated (R.homEquiv (𝟙 H)).1 ∧
      LocallyOfFiniteType (R.homEquiv (𝟙 H)).1 := by
  intro A B _ _ _ _ _ r H R
  classical
  let e : Module.Basis (Fin (Fintype.card (Module.Free.ChooseBasisIndex A B))) A B :=
    (Module.Free.chooseBasis A B).reindex (Fintype.equivFin _)
  set N := Fintype.card (Module.Free.ChooseBasisIndex A B)
  set ξ := R.homEquiv (𝟙 H) with hξ
  have hR : ∀ {Z : Scheme.{0}} (b : Z ⟶ H), R.homEquiv b = (functor A B r).map b.op ξ := by
    intro Z b
    have := R.homEquiv_comp b (𝟙 H)
    rwa [Category.comp_id] at this
  have hmap : ∀ {Z Z' : Scheme.{0}} (a : Z' ⟶ Z) (b : Z ⟶ H),
      (functor A B r).map a.op ((functor A B r).map b.op ξ) = (functor A B r).map (a ≫ b).op ξ := by
    intro Z Z' a b
    rw [← hR b, ← hR (a ≫ b), R.homEquiv_comp]
  have hrc : ∀ {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z),
      Set.range (a ≫ b) = b '' Set.range a := by
    intro X Y Z a b
    ext p
    simp
  choose W hW hWc using fun σ : Fin r ↪ Fin N => GlobalTheory.T.exists_open_affineHilbertChartBasic_locus A B N r e σ H ξ
  choose X x hXa hXl hXb hXu using fun σ : Fin r ↪ Fin N => GlobalTheory.T.affineHilbertChart_representable A B N r e σ
  have hcov : ⨆ σ, W σ = ⊤ := by
    rw [eq_top_iff]
    intro h _
    obtain ⟨σ, U, hU, hb⟩ := GlobalTheory.T.exists_affineHilbertChartBasic_neighbourhood A B N r e H ξ h
    have := (hW σ _ U.ι).2 hb
    rw [Scheme.Opens.range_ι] at this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨σ, this hU⟩
  have hiso : ∀ σ, ∃ g : (W σ).toScheme ⟶ X σ, IsIso g ∧ (W σ).ι ≫ ξ.1 = g ≫ (x σ).1 := by
    intro σ
    have hb : Basic A B e σ ((functor A B r).map (W σ).ι.op ξ) :=
      (hW σ _ _).1 (by rw [Scheme.Opens.range_ι])
    obtain ⟨g, hg, -⟩ := hXu σ _ _ hb
    obtain ⟨f, hf⟩ : ∃ f, R.homEquiv f = x σ := ⟨_, Equiv.apply_symm_apply _ _⟩
    have hfr : Set.range f ⊆ Set.range (W σ).ι := by
      rw [Scheme.Opens.range_ι]
      exact (hW σ _ f).2 (by rw [← hR, hf]; exact hXb σ)
    let f' := IsOpenImmersion.lift (W σ).ι f hfr
    have hf' : f' ≫ (W σ).ι = f := IsOpenImmersion.lift_fac _ _ _
    have hgf : g ≫ f = (W σ).ι := R.homEquiv.injective (by rw [R.homEquiv_comp, hf, hg, hR])
    have h1 : g ≫ f' = 𝟙 _ := by
      rw [← cancel_mono (W σ).ι, Category.assoc, hf', hgf, Category.id_comp]
    have h2 : f' ≫ g = 𝟙 _ := by
      obtain ⟨g0, -, hu⟩ := hXu σ (X σ) (x σ) (hXb σ)
      have e1 : (functor A B r).map (f' ≫ g).op (x σ) = x σ := by
        rw [← hf, ← R.homEquiv_comp, Category.assoc, hgf, hf']
      have e2 : (functor A B r).map (𝟙 (X σ)).op (x σ) = x σ := by simp
      exact (hu _ e1).trans (hu _ e2).symm
    exact ⟨g, ⟨f', h1, h2⟩, (congrArg Sigma.fst hg).symm⟩
  choose g hg hgx using hiso
  have hWa : ∀ σ, IsAffineOpen (W σ) := fun σ => by
    haveI := hg σ; haveI := hXa σ; exact IsAffine.of_isIso (g σ)
  have hint : ∀ (U : H.Opens), CompactSpace U.toScheme → ∀ τ, IsCompact ((U : Set H) ∩ W τ) := by
    intro U hU τ
    obtain ⟨V, hV, hVc⟩ := GlobalTheory.T.exists_open_affineHilbertChartBasic_locus A B N r e τ U.toScheme ((functor A B r).map U.ι.op ξ)
    have key : ∀ (Z' : Scheme.{0}) (a : Z' ⟶ U.toScheme),
        Set.range a ⊆ V ↔ U.ι '' Set.range a ⊆ W τ := fun Z' a => by
      rw [hV, hmap, ← hW, hrc]
    have hVeq : (V : Set U.toScheme) = U.ι ⁻¹' (W τ) := by
      apply subset_antisymm
      · have := (key _ V.ι).1 (by rw [Scheme.Opens.range_ι])
        rw [Scheme.Opens.range_ι] at this
        exact Set.image_subset_iff.1 this
      · have := (key _ (U.ι ⁻¹ᵁ W τ).ι).2 (by
          rw [Scheme.Opens.range_ι]; exact Set.image_preimage_subset _ _)
        rw [Scheme.Opens.range_ι] at this
        exact this
    have : (U : Set H) ∩ W τ = U.ι '' V := by
      rw [hVeq, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι, Set.inter_comm]
    rw [this]
    exact (hVc hU).image U.ι.continuous
  have hWc' : ∀ σ, CompactSpace (W σ).toScheme := fun σ => by
    haveI : IsAffine (W σ).toScheme := hWa σ
    infer_instance
  refine ⟨?_, ?_, ?_⟩
  · rw [quasiCompact_iff_compactSpace]
    show CompactSpace H
    rw [← isCompact_univ_iff]
    have : (Set.univ : Set H) = ⋃ σ, (W σ : Set H) := by
      rw [← TopologicalSpace.Opens.coe_iSup, hcov]; rfl
    rw [this]
    exact isCompact_iUnion fun σ => (hWa σ).isCompact
  · rw [quasiSeparated_iff_quasiSeparatedSpace]
    exact Scheme.quasiSeparatedSpace_of_isOpenCover W hcov hWa
      (fun σ τ => hint (W σ) (hWc' σ) τ)
  · haveI : IsZariskiLocalAtSource @LocallyOfFiniteType := HasRingHomProperty.instIsZariskiLocalAtSource
    refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @LocallyOfFiniteType) W hcov fun σ => ?_
    rw [hgx σ]
    haveI := hg σ
    haveI := hXl σ
    infer_instance

end GlobalTheory.HilbAff
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbertScheme_representing_qc_qs_finiteType : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B] (r : ℕ) (H : Scheme.{0}) (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H), QuasiCompact (R.homEquiv (𝟙 H)).1 ∧ QuasiSeparated (R.homEquiv (𝟙 H)).1 ∧ LocallyOfFiniteType (R.homEquiv (𝟙 H)).1 := by
  first | (exact @GlobalTheory.HilbAff.representing_qc_qs_loft) | (exact GlobalTheory.HilbAff.representing_qc_qs_loft) | (intros; apply GlobalTheory.HilbAff.representing_qc_qs_loft <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealSheafData_comap_ideal_top_of_isAffine : ∀ (X Y : Scheme.{0}) [IsAffine X] [IsAffine Y] (f : X ⟶ Y) (J : Y.IdealSheafData), (J.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.map f.appTop.hom (J.ideal ⟨⊤, isAffineOpen_top Y⟩) := by
  first | exact @GlobalTheory.IdealSheafData.ideal_comap_top_of_isAffine | exact GlobalTheory.IdealSheafData.ideal_comap_top_of_isAffine | (intros; apply GlobalTheory.IdealSheafData.ideal_comap_top_of_isAffine <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory

theorem closedSub_flat_of_quotient_flat : ∀ (V : Type) [CommRing V] (X : Scheme.{0}) [IsAffine X] (p : X ⟶ Spec (CommRingCat.of V)) (J : X.IdealSheafData), ((Ideal.Quotient.mk (J.ideal ⟨⊤, isAffineOpen_top X⟩)).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).Flat → Flat (J.subschemeι ≫ p) := by
  intro V _ X _ p J h
  have : IsAffine J.subscheme := isAffine_of_isAffineHom J.subschemeι
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
  set U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have e : (J.subschemeι ≫ p).appTop.hom =
      (J.subschemeObjIso U).inv.hom.comp
        (((Ideal.Quotient.mk (J.ideal U)).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).comp
          (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom) := by
    have h2 := J.subschemeι_app U
    have h3 : J.subschemeι.appTop = CommRingCat.ofHom (Ideal.Quotient.mk (J.ideal U)) ≫ (J.subschemeObjIso U).inv := h2
    rw [Scheme.Hom.comp_appTop, h3]
    ext x
    change (J.subschemeObjIso U).inv.hom (Ideal.Quotient.mk (J.ideal U) (p.appTop.hom x)) =
      (J.subschemeObjIso U).inv.hom (Ideal.Quotient.mk (J.ideal U) (p.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom x))))
    rw [Iso.hom_inv_id_apply]
  rw [e]
  refine RingHom.Flat.comp ?_ (RingHom.Flat.of_bijective (J.subschemeObjIso U).commRingCatIsoToRingEquiv.symm.bijective)
  refine RingHom.Flat.comp (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (CommRingCat.of V)).commRingCatIsoToRingEquiv.bijective) h

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_subscheme_of_quotient_flat_affine : ∀ (V : Type) [CommRing V] (X : Scheme.{0}) [IsAffine X] (p : X ⟶ Spec (CommRingCat.of V)) (J : X.IdealSheafData), ((Ideal.Quotient.mk (J.ideal ⟨⊤, isAffineOpen_top X⟩)).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).Flat → Flat (J.subschemeι ≫ p) := by
  first | (exact @GlobalTheory.closedSub_flat_of_quotient_flat) | (exact GlobalTheory.closedSub_flat_of_quotient_flat) | (intros; apply GlobalTheory.closedSub_flat_of_quotient_flat  <;> assumption)
end

section
open scoped TensorProduct

namespace GlobalTheory.ValuativeQuotient

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem main : ∀ (V K B : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] [CommRing B] [Algebra V B] (JK : Ideal (K ⊗[V] B)),
    ∃! J : Ideal B, Module.Flat V (B ⧸ J) ∧
      J.map (Algebra.TensorProduct.includeRight : B →ₐ[V] K ⊗[V] B) = JK := by
  intro V K B _ _ _ _ _ _ _ _ JK
  have hloc := IsLocalization.tensorRight (S := B) K (nonZeroDivisors V)
  set M := Algebra.algebraMapSubmonoid B (nonZeroDivisors V) with hM
  have hmap : ∀ I : Ideal B,
      I.map (Algebra.TensorProduct.includeRight : B →ₐ[V] K ⊗[V] B) =
        I.map (algebraMap B (K ⊗[V] B)) := fun I => rfl
  have hsmul : ∀ (J : Ideal B) (v : V) (b : B),
      v • Ideal.Quotient.mk J b = Ideal.Quotient.mk J (algebraMap V B v * b) := by
    intro J v b
    rw [← Algebra.smul_def, ← Ideal.Quotient.mkₐ_eq_mk V, map_smul]
  have hflat : ∀ J : Ideal B, Module.Flat V (B ⧸ J) ↔ ∀ m ∈ M, ∀ b : B, m * b ∈ J → b ∈ J := by
    intro J
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, Submodule.eq_bot_iff]
    constructor
    · rintro h m ⟨v, hv, rfl⟩ b hb
      have h0 := h (Ideal.Quotient.mk J b) ((Submodule.mem_torsion_iff _).mpr
        ⟨⟨v, hv⟩, by
          show v • Ideal.Quotient.mk J b = 0
          rw [hsmul, Ideal.Quotient.eq_zero_iff_mem]
          exact hb⟩)
      exact Ideal.Quotient.eq_zero_iff_mem.mp h0
    · intro h x hx
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨⟨v, hv⟩, hvb⟩ := (Submodule.mem_torsion_iff _).mp hx
      change v • Ideal.Quotient.mk J b = 0 at hvb
      rw [hsmul, Ideal.Quotient.eq_zero_iff_mem] at hvb
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (h _ ⟨v, hv, rfl⟩ b hvb)
  refine ⟨JK.comap (algebraMap B (K ⊗[V] B)), ⟨?_, ?_⟩, ?_⟩
  · rw [hflat]
    intro m hm b hb
    rw [Ideal.mem_comap, map_mul] at hb
    exact (Ideal.unit_mul_mem_iff_mem JK (IsLocalization.map_units (K ⊗[V] B) ⟨m, hm⟩)).mp hb
  · rw [hmap]
    exact IsLocalization.map_comap M (K ⊗[V] B) JK
  · rintro J' ⟨hJ'f, hJ'⟩
    rw [hmap] at hJ'
    rw [hflat] at hJ'f
    apply le_antisymm
    · rw [← hJ']
      exact Ideal.le_comap_map
    · intro b hb
      rw [Ideal.mem_comap, ← hJ', IsLocalization.mem_map_algebraMap_iff M] at hb
      obtain ⟨⟨x, m⟩, hxm⟩ := hb
      rw [← map_mul, IsLocalization.eq_iff_exists M] at hxm
      obtain ⟨c, hc⟩ := hxm
      apply hJ'f (c * m) (M.mul_mem c.2 m.2)
      have : (c : B) * (m : B) * b = c * x.1 := by rw [← hc]; ring
      rw [this]
      exact J'.mul_mem_left _ x.2

end GlobalTheory.ValuativeQuotient
end

section
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace GlobalTheory.FlatHilbAff

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

theorem exists_flat_ideal : ∀ (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (X X' : Scheme.{0}) [IsAffine X] [IsAffine X'] (p : X ⟶ Spec (CommRingCat.of V)) (p' : X' ⟶ Spec (CommRingCat.of K)) (b : X' ⟶ X), IsPullback b p' p (Spec.map (CommRingCat.ofHom (algebraMap V K))) → ∀ I : Ideal Γ(X', ⊤), ∃ J : Ideal Γ(X, ⊤), ((Ideal.Quotient.mk J).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).Flat ∧ Ideal.map b.appTop.hom J = I := by
  intro V K _ _ _ _ _ _ X X' _ _ p p' b h I
  set φ : V →+* Γ(X, ⊤) := p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom with hφ
  letI : Algebra V Γ(X, ⊤) := φ.toAlgebra
  have H0 := isPushout_appTop_of_isPullback h
  have H : IsPushout (CommRingCat.ofHom (algebraMap V K)) (CommRingCat.ofHom (algebraMap V Γ(X, ⊤)))
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p'.appTop) b.appTop := by
    refine H0.flip.of_iso (Scheme.ΓSpecIso _) (Scheme.ΓSpecIso _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · exact Scheme.ΓSpecIso_naturality _
    · ext x; simp [φ, RingHom.algebraMap_toAlgebra]
    · simp
    · simp
  let e : K ⊗[V] Γ(X, ⊤) ≃+* Γ(X', ⊤) :=
    ((CommRingCat.isPushout_tensorProduct V K Γ(X, ⊤)).isoPushout ≪≫
      H.isoPushout.symm).commRingCatIsoToRingEquiv
  have he : ∀ x : Γ(X, ⊤), e (Algebra.TensorProduct.includeRight x) = b.appTop.hom x := by
    intro x
    have h1 := congr($((CommRingCat.isPushout_tensorProduct V K Γ(X, ⊤)).inr_isoPushout_hom).hom x)
    have h4 := congr($(H.inr_isoPushout_inv).hom x)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1 h4
    have : e (Algebra.TensorProduct.includeRight x) = H.isoPushout.inv.hom
        ((CommRingCat.isPushout_tensorProduct V K Γ(X, ⊤)).isoPushout.hom.hom
          (Algebra.TensorProduct.includeRight x)) := rfl
    rw [this]
    exact (congrArg H.isoPushout.inv.hom h1).trans h4
  obtain ⟨J, ⟨hJf, hJ⟩, -⟩ := GlobalTheory.ValuativeQuotient.main V K Γ(X, ⊤) (I.comap e.toRingHom)
  refine ⟨J, ?_, ?_⟩
  · have : (algebraMap V (Γ(X, ⊤) ⧸ J)) =
        (Ideal.Quotient.mk J).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom) :=
      rfl
    rw [← this, RingHom.flat_algebraMap_iff]
    exact hJf
  · have hb : b.appTop.hom = e.toRingHom.comp
        (Algebra.TensorProduct.includeRight : Γ(X, ⊤) →ₐ[V] K ⊗[V] Γ(X, ⊤)).toRingHom := by
      ext x; exact (he x).symm
    rw [hb, ← Ideal.map_map]
    change Ideal.map e.toRingHom (J.map (Algebra.TensorProduct.includeRight : Γ(X, ⊤) →ₐ[V] K ⊗[V] Γ(X, ⊤))) = I
    rw [hJ]
    exact Ideal.map_comap_of_surjective _ e.surjective I

end GlobalTheory.FlatHilbAff
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flat_ideal_valuationRing_pullback : ∀ (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (X X' : Scheme.{0}) [IsAffine X] [IsAffine X'] (p : X ⟶ Spec (CommRingCat.of V)) (p' : X' ⟶ Spec (CommRingCat.of K)) (b : X' ⟶ X), IsPullback b p' p (Spec.map (CommRingCat.ofHom (algebraMap V K))) → ∀ I : Ideal Γ(X', ⊤), ∃ J : Ideal Γ(X, ⊤), ((Ideal.Quotient.mk J).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)).Flat ∧ Ideal.map b.appTop.hom J = I := by
  atlas_forward_decl GlobalTheory.FlatHilbAff.exists_flat_ideal
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

theorem exists_flat_ideal_extension (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] (X X' : Scheme.{0}) [IsAffine X] [IsAffine X']
    (p : X ⟶ Spec (CommRingCat.of V)) (p' : X' ⟶ Spec (CommRingCat.of K)) (b : X' ⟶ X)
    (h : IsPullback b p' p (Spec.map (CommRingCat.ofHom (algebraMap V K))))
    (I : X'.IdealSheafData) : ∃ J : X.IdealSheafData, Flat (J.subschemeι ≫ p) ∧ J.comap b = I := by
  obtain ⟨J₀, hf, hJ⟩ := GlobalTheory.T.exists_flat_ideal_valuationRing_pullback V K X X' p p' b h (I.ideal ⟨⊤, isAffineOpen_top X'⟩)
  have e : (Scheme.IdealSheafData.ofIdealTop J₀).ideal ⟨⊤, isAffineOpen_top X⟩ = J₀ :=
    Scheme.IdealSheafData.equivOfIsAffine.apply_symm_apply J₀
  refine ⟨Scheme.IdealSheafData.ofIdealTop J₀, GlobalTheory.T.flat_subscheme_of_quotient_flat_affine V X p _ (by rw [e]; exact hf), ?_⟩
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [GlobalTheory.T.idealSheafData_comap_ideal_top_of_isAffine, e, hJ]

theorem finrank_const_of_isLocalRing (V : Type) [CommRing V] [IsLocalRing V] (Z : Scheme.{0})
    (f : Z ⟶ Spec (CommRingCat.of V)) (h1 : IsFinite f) (h2 : Flat f) (x y : Spec (CommRingCat.of V)) :
    f.finrank x = f.finrank y := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.isoSpec.inv ≫ f)
  have ef : f = Z.isoSpec.hom ≫ Spec.map φ := by rw [hφ]; simp
  have hf1 : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hf2 : Flat (Spec.map φ) := by rw [hφ]; infer_instance
  have hr1 := hf1
  have hr2 := hf2
  rw [IsFinite.SpecMap_iff] at hr1
  rw [Flat.SpecMap_iff] at hr2
  rw [ef, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_eq_finrank hr1 hr2]
  algebraize [φ.hom]
  have : Module.Free V Γ(Z, ⊤) := Module.free_of_flat_of_isLocalRing
  rw [← RingHom.algebraMap_toAlgebra φ.hom, RingHom.finrank_algebraMap]
  simp only [Module.rankAtStalk_eq_finrank_of_free]
  rfl

theorem exists_good_extension (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] (r : ℕ) (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] (g : Spec (CommRingCat.of V) ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ g)).IdealSheafData)
    (hI : Good A B r _ I) :
    ∃ J, Good A B r g J ∧ J.comap (bc A B g (Spec.map (CommRingCat.ofHom (algebraMap V K)))) = I := by
  obtain ⟨J, hJf, hJ⟩ := exists_flat_ideal_extension V K _ _ (pullback.snd (str A B) g) (pullback.snd _ _) _
    (isPullback_bc A B g _) I
  have : IsFinite (str A B) := by
    rw [IsFinite.SpecMap_iff]; exact RingHom.finite_algebraMap.mpr inferInstance
  have h1 : IsFinite (J.subschemeι ≫ pullback.snd (str A B) g) := inferInstance
  refine ⟨J, ⟨h1, hJf, fun y => ?_⟩, hJ⟩
  obtain ⟨_, _, h3⟩ := hI
  subst hJ
  set a := Spec.map (CommRingCat.ofHom (algebraMap V K))
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  rw [finrank_const_of_isLocalRing V _ _ h1 hJf y (a pt)]
  have H : IsPullback (pullback.snd (bc A B g a) J.subschemeι)
      (pullback.fst (bc A B g a) J.subschemeι ≫ pullback.snd _ (a ≫ g))
      (J.subschemeι ≫ pullback.snd _ g) a :=
    (IsPullback.of_hasPullback (bc A B g a) J.subschemeι).flip.paste_vert (isPullback_bc A B g a)
  have e : (J.comap (bc A B g a)).subschemeι ≫ pullback.snd _ (a ≫ g) =
      (J.comapIso (bc A B g a)).hom ≫ (pullback.fst (bc A B g a) J.subschemeι ≫
        pullback.snd _ (a ≫ g)) := by
    rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  have f1 : IsFinite (pullback.fst (bc A B g a) J.subschemeι ≫ pullback.snd _ (a ≫ g)) :=
    MorphismProperty.of_isPullback (P := @IsFinite) H h1
  have f2 : Flat (pullback.fst (bc A B g a) J.subschemeι ≫ pullback.snd _ (a ≫ g)) :=
    MorphismProperty.of_isPullback (P := @Flat) H hJf
  have := h3 pt
  rw [e, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_of_isPullback _ _ _ _ H pt]
    at this
  exact this

theorem valuativeExistence (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B]
    [Module.Finite A B] (r : ℕ) (H : Scheme.{0}) (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H) :
    ValuativeCriterion.Existence (R.homEquiv (𝟙 H)).1 := by
  intro S
  have key : ∀ {T : Scheme.{0}} (f : T ⟶ H), (R.homEquiv f).1 = f ≫ (R.homEquiv (𝟙 H)).1 := by
    intro T f
    have h := R.homEquiv_comp f (𝟙 H)
    rw [Category.comp_id] at h
    rw [h]; rfl
  set ι := Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) with hι
  have gen : ∀ x : (functor A B r).obj (op (Spec (CommRingCat.of S.K))), x.1 = ι ≫ S.i₂ →
      ∃ y : (functor A B r).obj (op (Spec (CommRingCat.of S.R))),
        y.1 = S.i₂ ∧ (functor A B r).map ι.op y = x := by
    rintro ⟨g', I, hI⟩ hx
    dsimp only at hx
    subst hx
    obtain ⟨J, hJ, hJI⟩ := exists_good_extension A B r S.R S.K S.i₂ I hI
    subst hJI
    exact ⟨⟨S.i₂, J, hJ⟩, rfl, rfl⟩
  obtain ⟨y, hy1, hy2⟩ := gen (R.homEquiv S.i₁) ((key S.i₁).trans S.commSq.w)
  refine ⟨⟨{ l := R.homEquiv.symm y, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply R.homEquiv.injective
    rw [R.homEquiv_comp, Equiv.apply_symm_apply, hy2]
  · rw [← key, Equiv.apply_symm_apply, hy1]

end GlobalTheory.HilbAff
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbertScheme_valuativeCriterion_existence : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B] (r : ℕ) (H : Scheme.{0}) (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H), ValuativeCriterion.Existence (R.homEquiv (𝟙 H)).1 := by
  first | (exact @GlobalTheory.HilbAff.valuativeExistence) | (exact GlobalTheory.HilbAff.valuativeExistence) | (intros; apply GlobalTheory.HilbAff.valuativeExistence  <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

theorem pushout_inl_injective {R S R' P : CommRingCat.{0}} {f : R ⟶ S} {g : R ⟶ R'}
    {inl : S ⟶ P} {inr : R' ⟶ P} (h : IsPushout f g inl inr) (hf : f.hom.Flat)
    (hg : Function.Injective g.hom) : Function.Injective inl.hom := by
  letI := f.hom.toAlgebra
  letI := g.hom.toAlgebra
  haveI : Module.Flat R S := hf
  have ht := CommRingCat.isPushout_tensorProduct R R' S
  let e := IsPushout.isoIsPushout _ _ h.flip ht
  have he : inl ≫ e.hom = CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom :=
    IsPushout.inr_isoIsPushout_hom _ _ h.flip ht
  intro x y hxy
  have hi : Function.Injective (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := S)) :=
    Algebra.TensorProduct.includeRight_injective hg
  apply hi
  have h1 := congrArg (fun φ => φ.hom x) he
  have h2 := congrArg (fun φ => φ.hom y) he
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h1 h2
  change _ = Algebra.TensorProduct.includeRight.toRingHom x at h1
  change _ = Algebra.TensorProduct.includeRight.toRingHom y at h2
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1 h2
  rw [← h1, ← h2, hxy]

theorem ker_eq_bot_of_isPullback {Z ZK Y Y' : Scheme.{0}} [IsAffine Z] [IsAffine Y] [IsAffine Y']
    {p : ZK ⟶ Z} {q : ZK ⟶ Y'} {π : Z ⟶ Y} {j : Y' ⟶ Y} (H : IsPullback p q π j) [Flat π]
    (hj : Function.Injective j.appTop.hom) : p.ker = ⊥ := by
  haveI : IsAffine ZK := .of_isPullback H
  have hP := isPushout_appTop_of_isPullback H
  have hf : π.appTop.hom.Flat := (HasRingHomProperty.iff_of_isAffine (P := @Flat)).mp inferInstance
  have hinj := pushout_inl_injective hP hf hj
  rw [Scheme.ker_of_isAffine, (RingHom.injective_iff_ker_eq_bot _).mp hinj]
  first | exact map_bot (Scheme.IdealSheafData.equivOfIsAffine (X := Z)).symm | simp

theorem appTop_spec_injective {R S : CommRingCat.{0}} (f : R ⟶ S) (hf : Function.Injective f.hom) :
    Function.Injective (Spec.map f).appTop.hom := by
  intro x y hxy
  have e := Scheme.ΓSpecIso_naturality f
  have h1 := congrArg (fun φ => φ.hom x) e
  have h2 := congrArg (fun φ => φ.hom y) e
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h1 h2
  rw [hxy] at h1
  have := hf (h1.symm.trans h2)
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).hom).1 this

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

theorem map_comap_bc_eq (r : ℕ) {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K]
    [IsFractionRing V K] (g : Spec (CommRingCat.of V) ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) (hI : Good A B r g I) :
    (I.comap (bc A B g (Spec.map (CommRingCat.ofHom (algebraMap V K))))).map
      (bc A B g (Spec.map (CommRingCat.ofHom (algebraMap V K)))) = I := by
  set a := Spec.map (CommRingCat.ofHom (algebraMap V K))
  obtain ⟨-, h2, -⟩ := hI
  haveI : IsAffine I.subscheme := isAffine_of_isAffineHom I.subschemeι
  have H : IsPullback (pullback.snd (bc A B g a) I.subschemeι)
      (pullback.fst (bc A B g a) I.subschemeι ≫ pullback.snd _ (a ≫ g))
      (I.subschemeι ≫ pullback.snd _ g) a :=
    (IsPullback.of_hasPullback (bc A B g a) I.subschemeι).flip.paste_vert (isPullback_bc A B g a)
  have hk : (pullback.snd (bc A B g a) I.subschemeι).ker = ⊥ :=
    ker_eq_bot_of_isPullback H (appTop_spec_injective _ (IsFractionRing.injective V K))
  rw [Scheme.IdealSheafData.comap, Scheme.IdealSheafData.map_ker, pullback.condition,
    Scheme.Hom.ker_comp, hk, Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι]

theorem eq_of_comap_bc_eq (r : ℕ) {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K]
    [IsFractionRing V K] (g : Spec (CommRingCat.of V) ⟶ Spec (CommRingCat.of A))
    (I I' : (pullback (str A B) g).IdealSheafData) (hI : Good A B r g I) (hI' : Good A B r g I')
    (h : I.comap (bc A B g (Spec.map (CommRingCat.ofHom (algebraMap V K)))) =
      I'.comap (bc A B g (Spec.map (CommRingCat.ofHom (algebraMap V K))))) : I = I' := by
  rw [← map_comap_bc_eq A B r (K := K) g I hI, ← map_comap_bc_eq A B r (K := K) g I' hI', h]

end GlobalTheory.HilbAff

namespace GlobalTheory.HilbAff

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

theorem eq_of_map_eq (r : ℕ) {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K]
    [IsFractionRing V K] (x x' : (functor A B r).obj (op (Spec (CommRingCat.of V))))
    (h1 : x.1 = x'.1)
    (h2 : (functor A B r).map (Spec.map (CommRingCat.ofHom (algebraMap V K))).op x =
      (functor A B r).map (Spec.map (CommRingCat.ofHom (algebraMap V K))).op x') : x = x' := by
  rw [functor_map, functor_map] at h2
  have h3 := (Sigma.ext_iff.mp h2).2
  obtain ⟨g, I, hI⟩ := x
  obtain ⟨g', I', hI'⟩ := x'
  dsimp only at h1 h3
  subst h1
  have h4 := congrArg Subtype.val (eq_of_heq h3)
  have := eq_of_comap_bc_eq A B r (K := K) g I I' hI hI' h4
  subst this
  rfl

theorem valuativeCriterion_uniqueness : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (r : ℕ) (H : Scheme.{0})
    (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H),
    ValuativeCriterion.Uniqueness (R.homEquiv (𝟙 H)).1 := by
  intro A B _ _ _ _ _ r H Rep S
  refine ⟨fun l₁ l₂ => CommSq.LiftStruct.ext ?_⟩
  apply Rep.homEquiv.injective
  have e : ∀ l : Spec (CommRingCat.of S.R) ⟶ H,
      Rep.homEquiv l = (functor A B r).map l.op (Rep.homEquiv (𝟙 H)) := fun l => by
    rw [← Rep.homEquiv_comp, Category.comp_id]
  apply eq_of_map_eq A B r (K := S.K)
  · rw [e l₁.l, e l₂.l, functor_map, functor_map]
    dsimp only
    rw [l₁.fac_right, l₂.fac_right]
  · rw [← Rep.homEquiv_comp, ← Rep.homEquiv_comp, l₁.fac_left, l₂.fac_left]

end GlobalTheory.HilbAff
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbert_valuativeCriterion_uniqueness : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B] (r : ℕ) (H : Scheme.{0}) (R : (GlobalTheory.HilbAff.functor A B r).RepresentableBy H), ValuativeCriterion.Uniqueness (R.homEquiv (𝟙 H)).1 := by
  atlas_forward_decl GlobalTheory.HilbAff.valuativeCriterion_uniqueness
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace GlobalTheory.HilbAff

theorem exists_basis_fin (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B]
    [Module.Finite A B] : ∃ N, Nonempty (Module.Basis (Fin N) A B) := by
  by_cases hA : Nontrivial A
  · exact ⟨_, ⟨Module.finBasis A B⟩⟩
  · rw [not_nontrivial_iff_subsingleton] at hA
    have : Subsingleton B := Module.subsingleton A B
    exact ⟨0, ⟨Module.Basis.empty B⟩⟩

theorem hilbertScheme_exists : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B] (r : ℕ), ∃ (H : Scheme.{0}) (h : H ⟶ Spec (CommRingCat.of A)) (U : Scheme.{0}) (u : U ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) h), IsProper h ∧ IsClosedImmersion u ∧ IsFinite (u ≫ pullback.snd _ h) ∧ Flat (u ≫ pullback.snd _ h) ∧ (∀ y, (u ≫ pullback.snd _ h).finrank y = r) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Spec (CommRingCat.of A)) (V : Scheme.{0}) (v : V ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) g), IsClosedImmersion v → IsFinite (v ≫ pullback.snd _ g) → Flat (v ≫ pullback.snd _ g) → (∀ y, (v ≫ pullback.snd _ g).finrank y = r) → ∃! f : T ⟶ H, ∃ hf : f ≫ h = g, ∃ w : V ⟶ U, IsPullback v w (pullback.map _ g _ h (𝟙 _) f (𝟙 _) (by simp) (by rw [Category.comp_id, hf])) u := by
  intro A B _ _ _ _ _ r
  obtain ⟨N, ⟨e⟩⟩ := exists_basis_fin A B
  let F := GlobalTheory.HilbAff.functor A B r
  choose X x hX hlft hbas huniv using fun σ : Fin r ↪ Fin N => GlobalTheory.T.affineHilbertChart_representable A B N r e σ
  choose W hW _ using fun (σ : Fin r ↪ Fin N) (Z : Scheme.{0}) (y : F.obj (op Z)) =>
    GlobalTheory.T.exists_open_affineHilbertChartBasic_locus A B N r e σ Z y
  have stab : ∀ σ (Z : Scheme.{0}) (g : Z ⟶ X σ), GlobalTheory.HilbAff.Basic A B e σ (F.map g.op (x σ)) := by
    intro σ Z g
    have htop : Set.range (𝟙 (X σ)) ⊆ (W σ (X σ) (x σ) : Set (X σ)) :=
      (hW σ _ _ _ (𝟙 _)).2 (by rw [op_id, F.map_id]; exact hbas σ)
    exact (hW σ _ _ _ g).1 (fun z _ => htop ⟨z, rfl⟩)
  have hrep : F.IsRepresentable := by
    refine GlobalTheory.GeneratorFunctor.isRepresentable_of_charts F (GlobalTheory.T.affineHilbertSchemeFunctor_isSheaf_zariski A B r) X x W ?_ ?_ ?_
    · intro σ Z y Z' a
      rw [hW]
      constructor
      · intro hb
        obtain ⟨g, hg, -⟩ := huniv σ Z' _ hb
        exact ⟨g, hg⟩
      · rintro ⟨g, hg⟩
        rw [← hg]
        exact stab σ Z' g
    · intro σ Z g g' h
      obtain ⟨g₀, -, hu⟩ := huniv σ Z _ (stab σ Z g)
      exact (hu g rfl).trans (hu g' h.symm).symm
    · intro Z y z
      obtain ⟨σ, U, hz, hb⟩ := GlobalTheory.T.exists_affineHilbertChartBasic_neighbourhood A B N r e Z y z
      refine ⟨σ, (hW σ Z y U U.ι).2 hb ?_⟩
      simpa using hz
  let R := F.representableBy
  obtain ⟨U, u, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.affineHilbert_representing_universal_subscheme A B r F.reprX R
  obtain ⟨q1, q2, q3⟩ := GlobalTheory.T.affineHilbertScheme_representing_qc_qs_finiteType A B r F.reprX R
  refine ⟨F.reprX, (R.homEquiv (𝟙 _)).1, U, u, ?_, h1, h2, h3, h4, h5⟩
  rw [IsProper.eq_valuativeCriterion, ValuativeCriterion.eq]
  exact ⟨⟨⟨⟨GlobalTheory.T.affineHilbertScheme_valuativeCriterion_existence A B r F.reprX R, GlobalTheory.T.affineHilbert_valuativeCriterion_uniqueness A B r F.reprX R⟩, q1⟩, q2⟩, q3⟩

end GlobalTheory.HilbAff
end
end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_scheme_finite_free_algebra_affine_exists : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B] (r : ℕ), ∃ (H : Scheme.{0}) (h : H ⟶ Spec (CommRingCat.of A)) (U : Scheme.{0}) (u : U ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) h), IsProper h ∧ IsClosedImmersion u ∧ IsFinite (u ≫ pullback.snd _ h) ∧ Flat (u ≫ pullback.snd _ h) ∧ (∀ y, (u ≫ pullback.snd _ h).finrank y = r) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Spec (CommRingCat.of A)) (V : Scheme.{0}) (v : V ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) g), IsClosedImmersion v → IsFinite (v ≫ pullback.snd _ g) → Flat (v ≫ pullback.snd _ g) → (∀ y, (v ≫ pullback.snd _ g).finrank y = r) → ∃! f : T ⟶ H, ∃ hf : f ≫ h = g, ∃ w : V ⟶ U, IsPullback v w (pullback.map _ g _ h (𝟙 _) f (𝟙 _) (by simp) (by rw [Category.comp_id, hf])) u := by
  first | (exact @GlobalTheory.HilbAff.hilbertScheme_exists) | (exact GlobalTheory.HilbAff.hilbertScheme_exists) | (intros; apply GlobalTheory.HilbAff.hilbertScheme_exists <;> assumption)
end
