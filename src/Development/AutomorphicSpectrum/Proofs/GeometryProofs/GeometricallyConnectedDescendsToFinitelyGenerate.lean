import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentOfClopen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenConnectedComponentOfNoetherianSpace
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemeNsmulSurjective

section
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Approx

private theorem eq_of_sp_complex_pts {K : Type} [Field K] (a b : ↥(Sp K)) : a = b := by
  revert a b
  change ∀ a b : PrimeSpectrum K, a = b
  intro a b
  exact PrimeSpectrum.ext ((Ideal.eq_bot_of_prime a.asIdeal).trans (Ideal.eq_bot_of_prime b.asIdeal).symm)

private theorem nonempty_sp (K : Type) [Field K] : Nonempty ↥(Sp K) := by
  change Nonempty (PrimeSpectrum K)
  infer_instance

theorem connectedSpace_pullback_of_fieldHom {k K K' : Type} [CommRing k] [Field K] [Field K']
    {X : Scheme.{0}} (p : X ⟶ Sp k) (f : k →+* K) (j : K →+* K')
    (h : ConnectedSpace ↥(pullback p (spMap (j.comp f)))) :
    ConnectedSpace ↥(pullback p (spMap f)) := by
  rw [spMap_comp] at h
  let e := pullbackLeftPullbackSndIso p (spMap f) (spMap j)
  let g : pullback p (spMap j ≫ spMap f) ⟶ pullback p (spMap f) :=
    e.inv ≫ pullback.fst (pullback.snd p (spMap f)) (spMap j)
  refine Function.Surjective.connectedSpace (f := ⇑g) ?_ g.continuous
  intro z
  obtain ⟨y'⟩ := nonempty_sp K'
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := pullback.snd p (spMap f)) (g := spMap j) z y' (eq_of_sp_complex_pts _ _)
  refine ⟨e.hom w, ?_⟩
  have h2 : e.hom ≫ g = pullback.fst (pullback.snd p (spMap f)) (spMap j) := by
    simp [g, e]
  rw [← hw, ← h2]
  rfl

private theorem connectedSpace_of_iso {A B : Scheme.{0}} (e : A ≅ B) [ConnectedSpace A] :
    ConnectedSpace B := by
  refine Function.Surjective.connectedSpace (f := ⇑e.hom) (fun b => ⟨e.inv b, ?_⟩) e.hom.continuous
  rw [← Scheme.Hom.comp_apply, e.inv_hom_id]
  rfl

theorem geometricallyConnected_pullback_snd_iff {X S T : Scheme.{0}} (p : X ⟶ S) (g : T ⟶ S) :
    GeometricallyConnected (pullback.snd p g) ↔
      ∀ (K : Type) [Field K] (y : Spec (CommRingCat.of K) ⟶ T),
        ConnectedSpace ↥(pullback p (y ≫ g)) := by
  rw [geometricallyConnected_iff]
  constructor
  · intro H K _ y
    haveI : ConnectedSpace ↥(pullback (pullback.snd p g) y) :=
      H y (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
    exact connectedSpace_of_iso (pullbackLeftPullbackSndIso p g y)
  · intro H K _ y Z fst snd hpb
    haveI := H K y
    exact connectedSpace_of_iso (hpb.isoPullback ≪≫ pullbackLeftPullbackSndIso p g y).symm

theorem geometricallyConnected_pullback_snd_spMap_iff {k R : Type} [CommRing k] [CommRing R]
    {X : Scheme.{0}} (p : X ⟶ Sp k) (a : k →+* R) :
    GeometricallyConnected (pullback.snd p (spMap a)) ↔
      ∀ (K : Type) [Field K] (φ : R →+* K), ConnectedSpace ↥(pullback p (spMap (φ.comp a))) := by
  rw [geometricallyConnected_pullback_snd_iff]
  constructor
  · intro H K _ φ
    have := H K (spMap φ)
    rwa [← spMap_comp] at this
  · intro H K _ y
    obtain ⟨φ, rfl⟩ : ∃ φ : R →+* K, spMap φ = y :=
      ⟨(Spec.preimage (y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))).hom, Spec.map_preimage _⟩
    rw [← spMap_comp]
    exact H K φ

theorem exists_field_amalgam {F K₁ K₂ : Type} [Field F] [Field K₁] [Field K₂]
    (a : F →+* K₁) (b : F →+* K₂) :
    ∃ (L : Type) (_ : Field L) (i : K₁ →+* L) (j : K₂ →+* L), i.comp a = j.comp b := by
  letI := a.toAlgebra
  letI := b.toAlgebra
  haveI : Nontrivial (K₁ ⊗[F] K₂) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K₁ ⊗[F] K₂)
  letI := Ideal.Quotient.field m
  refine ⟨K₁ ⊗[F] K₂ ⧸ m, inferInstance,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeRight.toRingHom, ?_⟩
  ext x
  simp only [RingHom.comp_apply]
  congr 1
  exact (Algebra.TensorProduct.algebraMap_apply x).symm.trans (Algebra.TensorProduct.algebraMap_apply' x)

theorem exists_residueField_lift {k K : Type} [CommRing k] [Field K] (f : k →+* K)
    (x : PrimeSpectrum k) (hx : x.asIdeal = RingHom.ker f) :
    ∃ ψ : x.asIdeal.ResidueField →+* K, ψ.comp (algebraMap k x.asIdeal.ResidueField) = f := by
  have h2 : x.asIdeal.primeCompl ≤ Submonoid.comap f (IsUnit.submonoid K) := by
    intro r hr
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
    refine isUnit_iff_ne_zero.mpr fun h0 => Ideal.mem_primeCompl_iff.mp hr ?_
    rw [hx]
    exact RingHom.mem_ker.mpr h0
  refine ⟨Ideal.ResidueField.lift x.asIdeal f hx.le h2, ?_⟩
  ext r
  exact Ideal.ResidueField.lift_algebraMap x.asIdeal f hx.le h2 r

theorem geometricallyConnected_pullback_snd_spMap_iff_residueField :
    ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (X : Scheme.{0}) (p : X ⟶ Sp k),
      GeometricallyConnected (pullback.snd p (spMap (algebraMap k V))) ↔
        ∀ x ∈ Set.range (PrimeSpectrum.comap (algebraMap k V)),
          GeometricallyConnected (pullback.snd p (spMap (algebraMap k x.asIdeal.ResidueField))) := by
  intro k V _ _ _ X p
  rw [geometricallyConnected_pullback_snd_spMap_iff]
  constructor
  · rintro H x ⟨q, rfl⟩
    rw [geometricallyConnected_pullback_snd_spMap_iff]
    intro K _ ψ
    have hker : (PrimeSpectrum.comap (algebraMap k V) q).asIdeal =
        RingHom.ker ((algebraMap V q.asIdeal.ResidueField).comp (algebraMap k V)) := by
      rw [← RingHom.comap_ker, Ideal.ker_algebraMap_residueField]
      rfl
    obtain ⟨ψ', hψ'⟩ := exists_residueField_lift _ _ hker
    obtain ⟨L, hL, i, j', hij⟩ := exists_field_amalgam ψ ψ'
    apply connectedSpace_pullback_of_fieldHom p _ i
    have e : i.comp (ψ.comp (algebraMap k (PrimeSpectrum.comap (algebraMap k V) q).asIdeal.ResidueField)) =
        (j'.comp (algebraMap V q.asIdeal.ResidueField)).comp (algebraMap k V) := by
      rw [← RingHom.comp_assoc, hij, RingHom.comp_assoc, hψ', RingHom.comp_assoc]
    rw [e]
    exact H L _
  · intro H K _ φ
    haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
    let q : PrimeSpectrum V := ⟨RingHom.ker φ, inferInstance⟩
    have hx : (PrimeSpectrum.comap (algebraMap k V) q).asIdeal =
        RingHom.ker (φ.comp (algebraMap k V)) := by
      rw [← RingHom.comap_ker]
      rfl
    obtain ⟨ψ, hψ⟩ := exists_residueField_lift _ _ hx
    have := (geometricallyConnected_pullback_snd_spMap_iff p _).mp (H _ ⟨q, rfl⟩) K ψ
    rwa [hψ] at this

end GlobalTheory.CompanionTheory.Ar.Approx
end

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyConnected_baseChange_iff_fibers : ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (X : Scheme.{0}) (p : X ⟶ Sp k), GeometricallyConnected (pullback.snd p (spMap (algebraMap k V))) ↔ ∀ x ∈ Set.range (PrimeSpectrum.comap (algebraMap k V)), GeometricallyConnected (pullback.snd p (spMap (algebraMap k x.asIdeal.ResidueField))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_pullback_snd_spMap_iff_residueField
end

section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem exists_comp_residue_eq (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    (K : Type) [Field K] (φ : A →+* K) :
    ∃ ψ : IsLocalRing.ResidueField A →+* K, ψ.comp (IsLocalRing.residue A) = φ := by
  have hm : (RingHom.ker φ).IsMaximal := by
    have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
    exact IsArtinianRing.isMaximal_of_isPrime _
  have he : RingHom.ker φ = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal hm
  have H : ∀ a ∈ IsLocalRing.maximalIdeal A, φ a = 0 := fun a ha => by
    rw [← he] at ha
    exact (RingHom.mem_ker).1 ha
  exact ⟨Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) φ H,
    RingHom.ext fun a => Ideal.Quotient.lift_mk (IsLocalRing.maximalIdeal A) φ H⟩

theorem geometricallyIntegral_of_closedFibre (A : Type) [CommRing A] [IsLocalRing A]
    [IsArtinianRing A] (X : Scheme.{0}) (p : X ⟶ Sp A)
    (h : GeometricallyIntegral (pullback.snd p (spMap (IsLocalRing.residue A)))) :
    GeometricallyIntegral p := by
  constructor
  intro K _ y Z fst snd hpb
  obtain ⟨ψ, hψ⟩ := exists_comp_residue_eq A K (Spec.preimage y).hom
  have hy : Spec.map (CommRingCat.ofHom ψ) ≫ spMap (IsLocalRing.residue A) = y := by
    rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ, CommRingCat.ofHom_hom]
    exact Spec.map_preimage y
  have hw : fst ≫ p = (snd ≫ Spec.map (CommRingCat.ofHom ψ)) ≫ spMap (IsLocalRing.residue A) := by
    rw [Category.assoc, hy]
    exact hpb.w
  have hbig : IsPullback (pullback.lift fst (snd ≫ Spec.map (CommRingCat.ofHom ψ)) hw ≫
      pullback.fst p (spMap (IsLocalRing.residue A))) snd p
      (Spec.map (CommRingCat.ofHom ψ) ≫ spMap (IsLocalRing.residue A)) := by
    rw [pullback.lift_fst, hy]
    exact hpb
  have hsq : IsPullback (pullback.lift fst (snd ≫ Spec.map (CommRingCat.ofHom ψ)) hw) snd
      (pullback.snd p (spMap (IsLocalRing.residue A))) (Spec.map (CommRingCat.ofHom ψ)) :=
    IsPullback.of_right hbig (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  exact h.geometrically_isIntegral (Spec.map (CommRingCat.ofHom ψ)) _ snd hsq

theorem isIso_appTop_of_artinian : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    (X : Scheme.{0}) (p : X ⟶ Sp A), Flat p → IsProper p →
    GeometricallyIntegral (pullback.snd p (spMap (IsLocalRing.residue A))) → IsIso p.appTop := by
  intro A _ _ _ X p hflat hprop hgi
  haveI : IsAffine (Sp A) := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  haveI : IsLocallyNoetherian (Sp A) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of A)))
  haveI := hflat
  haveI := hprop
  haveI : GeometricallyIntegral p := geometricallyIntegral_of_closedFibre A X p hgi
  exact GlobalTheory.ProperFunctions.isIso_appTop_of_isAffine p

end GlobalTheory.CompanionTheory.Ar.Approx
end

section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

open IsLocalRing GlobalTheory.ProperFunctions

theorem isClosed_germ_ne_zero (X : Scheme.{0}) (f : Γ(X, ⊤)) :
    IsClosed {x : X | X.presheaf.germ ⊤ x trivial f ≠ 0} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hx
  have hx' : X.presheaf.germ ⊤ x trivial f = X.presheaf.germ ⊤ x trivial 0 := by
    rw [hx, map_zero]
  obtain ⟨W, hxW, iU, iV, h⟩ := TopCat.Presheaf.germ_eq X.presheaf (U := ⊤) (V := ⊤) x trivial trivial f 0 hx'
  refine Filter.mem_of_superset (W.2.mem_nhds hxW) fun y hy ↦ ?_
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not]
  rw [← X.presheaf.germ_res_apply iU y hy, h, map_zero, map_zero]

theorem germ_mem_maximalIdeal {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}}
    (p : X ⟶ Sp A) (x : X) (hx : p x = closedPoint A) {a : A} (ha : a ∈ maximalIdeal A) :
    X.presheaf.germ ⊤ x trivial (p.appTop ((Scheme.ΓSpecIso (.of A)).inv a)) ∈
      maximalIdeal (X.presheaf.stalk x) := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h1 := (X.mem_basicOpen (U := ⊤) _ x trivial).mpr hu
  have h2 : x ∈ p ⁻¹ᵁ (Sp A).basicOpen ((Scheme.ΓSpecIso (.of A)).inv a) := by
    rw [Scheme.preimage_basicOpen]
    exact h1
  have h3 : p x ∈ (Sp A).basicOpen ((Scheme.ΓSpecIso (.of A)).inv a) := h2
  rw [basicOpen_eq_of_affine, hx] at h3
  exact h3 ha

theorem eq_zero_of_mem_pow {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X : Scheme.{0}} (p : X ⟶ Sp A) [UniversallyClosed p] [LocallyOfFiniteType p]
    (f : Γ(X, ⊤))
    (h : ∀ (n : ℕ) (U : X.affineOpens), X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op f ∈
      (((maximalIdeal A) ^ (n + 1)).map (Scheme.ΓSpecIso (.of A)).inv.hom).map
        (p.appLE ⊤ U.1 (le_preimage_top p _)).hom) : f = 0 := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  by_contra hf
  have hne : ∃ z : X, X.presheaf.germ ⊤ z trivial f ≠ 0 := by
    by_contra hall
    push_neg at hall
    refine hf (TopCat.Presheaf.section_ext X.sheaf ⊤ f 0 fun x _ ↦ ?_)
    rw [map_zero]
    exact hall x
  obtain ⟨z, hz⟩ := hne
  have hcl := p.isClosedMap _ (isClosed_germ_ne_zero X f)
  have hmem : closedPoint A ∈ p '' {x : X | X.presheaf.germ ⊤ x trivial f ≠ 0} :=
    (specializes_closedPoint (p z)).mem_closed hcl ⟨z, hz, rfl⟩
  obtain ⟨x, hxZ, hx⟩ := hmem
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  refine hxZ ?_
  have hθ : ∀ a : A, X.presheaf.germ U x hxU
      (p.appLE ⊤ U (le_preimage_top p _) ((Scheme.ΓSpecIso (.of A)).inv a)) =
      X.presheaf.germ ⊤ x trivial (p.appTop ((Scheme.ΓSpecIso (.of A)).inv a)) := by
    intro a
    have e1 : p.appLE ⊤ U (le_preimage_top p _) =
        p.appTop ≫ X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op := rfl
    rw [e1, CommRingCat.comp_apply]
    exact X.presheaf.germ_res_apply _ x hxU _
  have hpow : ∀ n : ℕ, X.presheaf.germ ⊤ x trivial f ∈
      maximalIdeal (X.presheaf.stalk x) ^ (n + 1) := by
    intro n
    have h1 := Ideal.mem_map_of_mem (X.presheaf.germ U x hxU).hom (h n ⟨U, hU⟩)
    rw [Ideal.map_map, Ideal.map_map, Ideal.map_pow] at h1
    have h2 : X.presheaf.germ ⊤ x trivial f = X.presheaf.germ U x hxU
        (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f) :=
      (X.presheaf.germ_res_apply _ x hxU f).symm
    rw [h2]
    refine Ideal.pow_right_mono ?_ _ h1
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap]
    change X.presheaf.germ U x hxU
      (p.appLE ⊤ U (le_preimage_top p _) ((Scheme.ΓSpecIso (.of A)).inv a)) ∈ _
    rw [hθ]
    exact germ_mem_maximalIdeal p x hx ha
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (X.presheaf.stalk x))
    Ideal.IsPrime.ne_top'
  have : X.presheaf.germ ⊤ x trivial f ∈ (⊥ : Ideal (X.presheaf.stalk x)) := by
    rw [← hbot, Ideal.mem_iInf]
    intro i
    exact Ideal.pow_le_pow_right (Nat.le_succ i) (hpow i)
  simpa using this

theorem geometricallyIntegral_fibre {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsLocalRing B] (π : A →+* B) (hπ : Function.Surjective π) [IsLocalHom π] {X : Scheme.{0}}
    (p : X ⟶ Sp A) (hG : GeometricallyIntegral (pullback.snd p (spMap (residue A)))) :
    GeometricallyIntegral
      (pullback.snd (pullback.snd p (spMap π)) (spMap (residue B))) := by
  let φ : ResidueField A →+* ResidueField B := ResidueField.map π
  have hφ : Function.Bijective φ := by
    refine ⟨φ.injective, fun y ↦ ?_⟩
    obtain ⟨b, rfl⟩ := residue_surjective y
    obtain ⟨a, rfl⟩ := hπ b
    exact ⟨residue A a, ResidueField.map_residue π a⟩
  have : IsIso (CommRingCat.ofHom φ) := (ConcreteCategory.isIso_iff_bijective _).mpr hφ
  have : IsIso (spMap φ) := inferInstanceAs (IsIso (Spec.map _))
  have e1 : φ.comp (residue A) = (residue B).comp π := by
    ext a
    exact ResidueField.map_residue π a
  have hw : spMap (residue B) ≫ spMap π = spMap φ ≫ spMap (residue A) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e1]
  have H := (IsPullback.of_hasPullback (pullback.snd p (spMap π)) (spMap (residue B))).paste_horiz
    (IsPullback.of_hasPullback p (spMap π))
  rw [hw] at H
  have R := IsPullback.of_hasPullback p (spMap (residue A))
  have w : (pullback.fst (pullback.snd p (spMap π)) (spMap (residue B)) ≫
      pullback.fst p (spMap π)) ≫ p =
      (pullback.snd (pullback.snd p (spMap π)) (spMap (residue B)) ≫ spMap φ) ≫
        spMap (residue A) := H.w.trans (Category.assoc _ _ _).symm
  have H2 : IsPullback (R.lift _ _ w) (pullback.snd (pullback.snd p (spMap π)) (spMap (residue B)))
      (pullback.snd p (spMap (residue A))) (spMap φ) := by
    refine IsPullback.of_right (h₁₂ := pullback.fst p (spMap (residue A))) (v₁₃ := p)
      (h₂₂ := spMap (residue A)) ?_ (R.lift_snd _ _ w) R
    rw [R.lift_fst]
    exact H
  exact MorphismProperty.of_isPullback (P := @GeometricallyIntegral) H2 hG

theorem appTop_fst_eq_zero {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsLocalRing B] [IsArtinianRing B] (π : A →+* B) (hπ : Function.Surjective π) [IsLocalHom π]
    {X : Scheme.{0}} (p : X ⟶ Sp A) (e : Sp A ⟶ X) (he : e ≫ p = 𝟙 _) (hF : Flat p)
    (hP : IsProper p) (hG : GeometricallyIntegral (pullback.snd p (spMap (residue A))))
    (f : Γ(X, ⊤)) (hf : e.appTop f = 0) : (pullback.fst p (spMap π)).appTop f = 0 := by
  have H := IsPullback.of_hasPullback p (spMap π)
  have hqF : Flat (pullback.snd p (spMap π)) := MorphismProperty.of_isPullback H hF
  have hqP : IsProper (pullback.snd p (spMap π)) := MorphismProperty.of_isPullback H hP
  have hiso := isIso_appTop_of_artinian B _ (pullback.snd p (spMap π)) hqF hqP
    (geometricallyIntegral_fibre π hπ p hG)
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso (pullback.snd p (spMap π)).appTop).2
    ((pullback.fst p (spMap π)).appTop f)
  let e' : Sp B ⟶ pullback p (spMap π) :=
    pullback.lift (spMap π ≫ e) (𝟙 _) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have h1 : e'.appTop ((pullback.snd p (spMap π)).appTop c) = c := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.lift_snd,
      Scheme.Hom.id_appTop]
    rfl
  have h2 : e'.appTop ((pullback.fst p (spMap π)).appTop f) = 0 := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.lift_fst,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hf, map_zero]
  have hc0 : c = 0 := by
    rw [hc, h2] at h1
    exact h1.symm
  rw [← hc, hc0, map_zero]

theorem ker_appTop_le {A : Type} [CommRing A] (I : Ideal A) :
    RingHom.ker (spMap (Ideal.Quotient.mk I)).appTop.hom ≤
      I.map (Scheme.ΓSpecIso (.of A)).inv.hom := by
  intro r hr
  obtain ⟨a, rfl⟩ : ∃ a, (Scheme.ΓSpecIso (.of A)).inv a = r :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).2 r
  refine Ideal.mem_map_of_mem _ ?_
  have h1 := congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I))) a)
  simp only [CommRingCat.comp_apply] at h1
  have h2 : (Scheme.ΓSpecIso (.of (A ⧸ I))).inv (Ideal.Quotient.mk I a) = 0 :=
    h1.trans hr
  have h3 : Ideal.Quotient.mk I a = 0 :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (A ⧸ I))).inv).1
      (h2.trans (map_zero _).symm)
  exact Ideal.Quotient.eq_zero_iff_mem.mp h3

theorem quotient_pow_facts (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (n : ℕ) :
    ∃ (_ : IsLocalRing (A ⧸ maximalIdeal A ^ (n + 1)))
      (_ : IsArtinianRing (A ⧸ maximalIdeal A ^ (n + 1))),
      IsLocalHom (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))) := by
  have hle : maximalIdeal A ^ (n + 1) ≤ maximalIdeal A := Ideal.pow_le_self (Nat.succ_ne_zero n)
  have hI : maximalIdeal A ^ (n + 1) ≠ ⊤ := fun h ↦
    Ideal.IsPrime.ne_top' (top_le_iff.mp (h ▸ hle))
  have : Nontrivial (A ⧸ maximalIdeal A ^ (n + 1)) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hL : IsLocalRing (A ⧸ maximalIdeal A ^ (n + 1)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hH : IsLocalHom (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))) := by
    refine ⟨fun a ha ↦ ?_⟩
    by_contra hna
    have ham : a ∈ maximalIdeal A := (mem_maximalIdeal a).mpr hna
    have h0 : (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)) a) ^ (n + 1) = 0 := by
      rw [← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow ham _)
    have := (ha.pow (n + 1))
    rw [h0] at this
    exact not_isUnit_zero this
  have hK : Ring.KrullDimLE 0 (A ⧸ maximalIdeal A ^ (n + 1)) := by
    refine Ring.krullDimLE_zero_iff.mpr fun Q hQ ↦ ?_
    have : Q = maximalIdeal _ := by
      refine le_antisymm (le_maximalIdeal hQ.ne_top) fun b hb ↦ ?_
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
      have ham : a ∈ maximalIdeal A := by
        rw [mem_maximalIdeal] at hb ⊢
        exact fun hu ↦ hb (hu.map _)
      have h0 : (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)) a) ^ (n + 1) ∈ Q := by
        rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow ham _)]
        exact Q.zero_mem
      exact hQ.mem_of_pow_mem _ h0
    rw [this]
    exact maximalIdeal.isMaximal _
  exact ⟨hL, IsNoetherianRing.isArtinianRing_of_krullDimLE_zero, hH⟩

theorem isIso_appTop_of_closedFibre : ∀ (A : Type) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (X : Scheme.{0}) (p : X ⟶ Sp A) (e : Sp A ⟶ X), e ≫ p = 𝟙 _ → Flat p →
    IsProper p → GeometricallyIntegral (pullback.snd p (spMap (IsLocalRing.residue A))) →
    IsIso p.appTop := by
  intro A _ _ _ X p e he hF hP hG
  have h1 : p.appTop ≫ e.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, he, Scheme.Hom.id_appTop]
  have h2 : Function.Injective e.appTop := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    refine eq_zero_of_mem_pow p f fun n U ↦ ?_
    obtain ⟨_, _, _⟩ := quotient_pow_facts A n
    have h0 := appTop_fst_eq_zero (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1)))
      Ideal.Quotient.mk_surjective p e he hF hP hG f hf
    have h3 := mem_map_ker_of_app_eq_zero
      (IsPullback.of_hasPullback p (spMap (Ideal.Quotient.mk (maximalIdeal A ^ (n + 1))))) U.2
      (X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op f) (by
        rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
        erw [h0]
        exact map_zero _)
    exact Ideal.map_mono (ker_appTop_le _) h3
  have : Mono e.appTop := ConcreteCategory.mono_of_injective _ h2
  exact ⟨e.appTop, h1, by rw [← cancel_mono e.appTop, Category.assoc, h1]; simp⟩

end GlobalTheory.CompanionTheory.Ar.Approx
end

section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem connectedSpace_of_isField_globalFunctions (Z : Scheme.{0}) (h : IsField Γ(Z, ⊤)) :
    ConnectedSpace Z := by
  have hne : Nonempty Z := by
    by_contra hZ
    have hb : (⊤ : Z.Opens) = ⊥ := by
      ext x
      exact (hZ ⟨x⟩).elim
    have hs : Subsingleton Γ(Z, ⊤) := by
      rw [hb]
      infer_instance
    obtain ⟨a, b, hab⟩ := h.exists_pair_ne
    exact hab (Subsingleton.elim a b)
  have hp : PreconnectedSpace Z := by
    refine preconnectedSpace_iff_clopen.2 fun U hU => ?_
    obtain ⟨e, he, hUe⟩ := GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen Z U hU
    by_cases h0 : e = 0
    · left
      rw [← hUe, h0, Z.basicOpen_zero]
      rfl
    · right
      obtain ⟨b, hb⟩ := h.mul_inv_cancel h0
      have h1 : e = 1 := by
        calc e = e * e * b := by rw [_root_.mul_assoc, hb, _root_.mul_one]
          _ = e * b := by rw [he]
          _ = 1 := hb
      rw [← hUe, h1, Z.basicOpen_of_isUnit isUnit_one]
      rfl
  exact { toPreconnectedSpace := hp, toNonempty := hne }

theorem geometricallyConnected_of_isIso_appTop :
    ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K), QuasiCompact p → QuasiSeparated p →
      IsIso p.appTop → GeometricallyConnected p := by
  intro K _ X p _ _ _
  refine ⟨fun L _ y Z a q H => ?_⟩
  have hy : Flat y := by
    obtain ⟨φ, rfl⟩ := Spec.map_surjective y
    rw [Flat.SpecMap_iff]
    algebraize [φ.hom]
    exact inferInstanceAs (Module.Flat K L)
  have hq : IsIso q.appTop := GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback H
  let e₁ : Γ(Spec (.of L), ⊤) ≃+* Γ(Z, ⊤) := (asIso q.appTop).commRingCatIsoToRingEquiv
  let e₂ : Γ(Spec (.of L), ⊤) ≃+* L := (Scheme.ΓSpecIso (.of L)).commRingCatIsoToRingEquiv
  have hL : IsField Γ(Spec (.of L), ⊤) := MulEquiv.isField (Field.toIsField L) e₂.toMulEquiv
  exact connectedSpace_of_isField_globalFunctions Z (MulEquiv.isField hL e₁.symm.toMulEquiv)

end GlobalTheory.CompanionTheory.Ar.Approx
end

section
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem exists_isPullback_left {P Q X S T U : Scheme.{0}} {t : P ⟶ X} {v : P ⟶ U} {p : X ⟶ S}
    {g : U ⟶ T} {f : T ⟶ S} {t' : Q ⟶ X} {v' : Q ⟶ T}
    (h : IsPullback t v p (g ≫ f)) (h' : IsPullback t' v' p f) :
    ∃ u : P ⟶ Q, IsPullback u v v' g := by
  refine ⟨h'.lift t (v ≫ g) (by simpa using h.w), ?_⟩
  refine IsPullback.of_right (h₁₂ := t') (h₂₂ := f) (v₁₃ := p) ?_ (by simp) h'
  simpa using h

theorem spMap_comp_spMap {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S)
    (g : S →+* T) : spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, CommRingCat.ofHom_comp]

theorem geometricallyConnected_of_local {k A E L K : Type} [CommRing k] [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [Field E] [Field L] [Field K] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (e : Sp k ⟶ X) (hs : e ≫ p = 𝟙 _) [Smooth p] [IsProper p] (φ : k →+* A) (a : k →+* E)
    (b : E →+* IsLocalRing.ResidueField A)
    (hb : b.comp a = (IsLocalRing.residue A).comp φ)
    (hE : GeometricallyConnected (pullback.snd p (spMap a)))
    (j : A →+* L) (hj : j.Flat) (c : k →+* K) (d : K →+* L) (hd : d.comp c = j.comp φ) :
    GeometricallyConnected (pullback.snd p (spMap c)) := by
  have hPA : IsPullback (pullback.fst p (spMap φ)) (pullback.snd p (spMap φ)) p (spMap φ) :=
    .of_hasPullback _ _
  haveI : Smooth (pullback.snd p (spMap φ)) := MorphismProperty.of_isPullback hPA ‹_›
  haveI : IsProper (pullback.snd p (spMap φ)) := MorphismProperty.of_isPullback hPA ‹_›
  haveI : Flat (pullback.snd p (spMap φ)) := inferInstance
  let eA : Sp A ⟶ pullback p (spMap φ) :=
    pullback.lift (spMap φ ≫ e) (𝟙 _) (by rw [Category.assoc, hs]; simp)
  have heA : eA ≫ pullback.snd p (spMap φ) = 𝟙 _ := pullback.lift_snd _ _ _

  have hW : IsPullback (pullback.fst (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A)))
      (pullback.snd (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A)))
      (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A)) := .of_hasPullback _ _
  have hbot : spMap (IsLocalRing.residue A) ≫ spMap φ = spMap b ≫ spMap a := by
    rw [spMap_comp_spMap, spMap_comp_spMap, hb]
  have hW' := hW.paste_horiz hPA
  rw [hbot] at hW'
  obtain ⟨u, hu⟩ := exists_isPullback_left hW' (.of_hasPullback p (spMap a))
  haveI : Smooth (pullback.snd (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A))) :=
    MorphismProperty.of_isPullback hW ‹_›
  haveI : GeometricallyConnected
      (pullback.snd (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A))) :=
    MorphismProperty.of_isPullback hu hE
  have hGI : GeometricallyIntegral
      (pullback.snd (pullback.snd p (spMap φ)) (spMap (IsLocalRing.residue A))) :=
    GlobalTheory.geometricallyIntegral_of_smooth _
  haveI hA : IsIso (pullback.snd p (spMap φ)).appTop :=
    isIso_appTop_of_closedFibre A _ _ eA heA inferInstance inferInstance hGI

  have hL : IsPullback (pullback.fst (pullback.snd p (spMap φ)) (spMap j))
      (pullback.snd (pullback.snd p (spMap φ)) (spMap j))
      (pullback.snd p (spMap φ)) (spMap j) := .of_hasPullback _ _
  haveI : Flat (spMap j) := Flat.SpecMap_iff.2 hj
  haveI hL1 : IsIso (pullback.snd (pullback.snd p (spMap φ)) (spMap j)).appTop :=
    GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback hL
  have hbot' : spMap j ≫ spMap φ = spMap d ≫ spMap c := by
    rw [spMap_comp_spMap, spMap_comp_spMap, hd]
  have hL' := hL.paste_horiz hPA
  rw [hbot'] at hL'
  obtain ⟨w, hw⟩ := exists_isPullback_left hL' (.of_hasPullback p (spMap c))
  haveI : Flat (spMap d) := Flat.SpecMap_iff.2 (by
    algebraize [d]
    exact RingHom.flat_algebraMap_iff.2 inferInstance)
  haveI : Surjective (spMap d) := by
    refine ⟨fun x => ?_⟩
    have y : PrimeSpectrum L := ⟨⊥, Ideal.isPrime_bot⟩
    exact ⟨y, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩
  haveI hK : IsIso (pullback.snd p (spMap c)).appTop :=
    GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback_of_surjective hw
  exact geometricallyConnected_of_isIso_appTop K _ _ inferInstance inferInstance hK

theorem geometricallyConnected_of_localDomain {k B A E K : Type} [CommRing k] [CommRing B]
    [IsDomain B] [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [Field E] [Field K]
    [Algebra B K] [IsFractionRing B K] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (e : Sp k ⟶ X) (hs : e ≫ p = 𝟙 _) [Smooth p] [IsProper p] (q : k →+* B) (ψ : B →+* A)
    (hψ : Function.Injective ψ) (a : k →+* E) (b : E →+* IsLocalRing.ResidueField A)
    (hb : b.comp a = (IsLocalRing.residue A).comp (ψ.comp q))
    (hE : GeometricallyConnected (pullback.snd p (spMap a))) :
    GeometricallyConnected (pullback.snd p (spMap ((algebraMap B K).comp q))) := by
  have hinj : Function.Injective ((algebraMap A (FractionRing A)).comp ψ) :=
    (IsFractionRing.injective A (FractionRing A)).comp hψ
  refine geometricallyConnected_of_local (A := A) (E := E) (L := FractionRing A) X p e hs (ψ.comp q)
    a b hb hE (algebraMap A (FractionRing A)) (RingHom.flat_algebraMap_iff.2 inferInstance) _
    (IsFractionRing.lift hinj) ?_
  ext r
  simp only [RingHom.comp_apply]
  exact IsFractionRing.lift_algebraMap hinj (q r)

theorem stableUnderGeneralization_geometricallyConnected_fibre :
    ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
      (e : Sp k ⟶ X), e ≫ p = 𝟙 _ → Smooth p → IsProper p →
      StableUnderGeneralization {x : PrimeSpectrum k | GeometricallyConnected
        (pullback.snd p (spMap (algebraMap k x.asIdeal.ResidueField)))} := by
  intro k _ _ X p e hs _ _ x y hyx hx
  have hle : y.asIdeal ≤ x.asIdeal := (PrimeSpectrum.le_iff_specializes y x).2 hyx
  have hq : Function.Surjective (Ideal.Quotient.mk y.asIdeal) := Ideal.Quotient.mk_surjective
  obtain ⟨Q, hQ, hcomap⟩ : ∃ Q : Ideal (k ⧸ y.asIdeal), ∃ _ : Q.IsPrime,
      x.asIdeal = Q.comap (Ideal.Quotient.mk y.asIdeal) := by
    refine ⟨x.asIdeal.map (Ideal.Quotient.mk y.asIdeal),
      Ideal.map_isPrime_of_surjective hq (by rw [Ideal.mk_ker]; exact hle), ?_⟩
    rw [Ideal.comap_map_of_surjective _ hq, eq_comm, sup_eq_left]
    refine le_trans ?_ hle
    rw [show Ideal.comap (Ideal.Quotient.mk y.asIdeal) ⊥ = RingHom.ker (Ideal.Quotient.mk y.asIdeal)
      from rfl, Ideal.mk_ker]
  haveI : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  haveI : IsDomain (Localization.AtPrime Q) :=
    IsLocalization.isDomain_localization Q.primeCompl_le_nonZeroDivisors
  have := geometricallyConnected_of_localDomain (K := y.asIdeal.ResidueField) X p e hs
    (Ideal.Quotient.mk y.asIdeal) (algebraMap (k ⧸ y.asIdeal) (Localization.AtPrime Q))
    (IsLocalization.injective _ Q.primeCompl_le_nonZeroDivisors)
    (algebraMap k x.asIdeal.ResidueField)
    (Ideal.ResidueField.map x.asIdeal Q (Ideal.Quotient.mk y.asIdeal) hcomap)
    (by
      ext r
      simp only [RingHom.comp_apply, Ideal.ResidueField.map_algebraMap]
      rfl) hx
  exact this

end GlobalTheory.CompanionTheory.Ar.Approx
end

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_connectedness_generalizes : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (e : Sp k ⟶ X), e ≫ p = 𝟙 _ → Smooth p → IsProper p → StableUnderGeneralization {x : PrimeSpectrum k | GeometricallyConnected (pullback.snd p (spMap (algebraMap k x.asIdeal.ResidueField)))} := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Approx.stableUnderGeneralization_geometricallyConnected_fibre
end

section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem eq_one_of_divisible {P Q : Type*} [CommGroup P] [Finite Q] (c : P → Q)
    (hc : ∀ a b t : P, c a = c b → c (a * t) = c (b * t))
    (hd : ∀ n : ℕ, n ≠ 0 → ∀ x : P, ∃ y : P, y ^ n = x) (x : P) : c x = c 1 := by
  let H : Subgroup P :=
    { carrier := {a | c a = c 1}
      one_mem' := rfl
      mul_mem' := fun {a b} ha hb => by
        have := hc a 1 b ha
        rw [_root_.one_mul] at this
        exact this.trans hb
      inv_mem' := fun {a} ha => by
        have := hc a 1 a⁻¹ ha
        rw [_root_.mul_inv_cancel, _root_.one_mul] at this
        exact this.symm }
  have hinj : Function.Injective (fun q : P ⧸ H => c q.out) := by
    intro q r hqr
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' r, QuotientGroup.eq]
    have := hc _ _ (q.out)⁻¹ hqr
    simp only [mul_inv_cancel] at this
    change c _ = c 1
    rw [mul_comm, this.symm]
  have : Finite (P ⧸ H) := Finite.of_injective _ hinj
  have hi : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain ⟨y, rfl⟩ := hd _ hi x
  exact Subgroup.pow_index_mem H y

theorem connectedSpace_of_divisible : ∀ (K : Type) [Field K] [IsAlgClosed K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G], LocallyOfFiniteType G.hom → QuasiCompact G.hom → (∀ n : ℕ, n ≠ 0 → ∀ x : 𝟙_ (Over (Sp K)) ⟶ G, ∃ y : 𝟙_ (Over (Sp K)) ⟶ G, y ^ n = x) → ConnectedSpace G.left := by
  intro K _ _ G _ _ hl hq hd
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : IsNoetherian G.left := {}
  have := LocallyOfFiniteType.jacobsonSpace G.hom
  let pt : (𝟙_ (Over (Sp K))).left := IsLocalRing.closedPoint K
  let F : (𝟙_ (Over (Sp K)) ⟶ G) → G.left := fun x => x.left pt
  have hopen : ∀ x : G.left, IsOpen (connectedComponent x) :=
    fun x => isOpen_connectedComponent_of_noetherianSpace x
  have : DiscreteTopology (_root_.ConnectedComponents G.left) :=
    ConnectedComponents.discreteTopology_iff.2 hopen
  have : Finite (_root_.ConnectedComponents G.left) := finite_of_compact_of_discrete
  let c : (𝟙_ (Over (Sp K)) ⟶ G) → _root_.ConnectedComponents G.left := fun x => F x
  have htr : ∀ a t : 𝟙_ (Over (Sp K)) ⟶ G,
      F (a * t) = (GrpObj.mulRight t).hom.left (F a) := by
    intro a t
    have h : a ≫ (GrpObj.mulRight t).hom = a * t := by
      simp [comp_lift_assoc, Hom.mul_def]
    simp only [F, ← h, Over.comp_left, Scheme.Hom.comp_apply]
  have hc : ∀ a b t, c a = c b → c (a * t) = c (b * t) := by
    intro a b t hab
    have := congrArg (Continuous.connectedComponentsMap (GrpObj.mulRight t).hom.left.continuous) hab
    simpa [c, htr] using this
  have hall := eq_one_of_divisible c hc hd
  have hsurj : ∀ x : G.left, IsClosed {x} → ∃ a, F a = x := by
    intro x hx
    refine ⟨Over.homMk (pointOfClosedPoint G.hom x hx) (pointOfClosedPoint_comp G.hom x hx), ?_⟩
    exact pointOfClosedPoint_apply G.hom x hx _
  have huniv : connectedComponent (F 1) = Set.univ := by
    by_contra hne
    obtain ⟨x, hx, hcl⟩ := nonempty_inter_closedPoints (Set.nonempty_compl.2 hne)
      (IsOpen.isLocallyClosed isClosed_connectedComponent.isOpen_compl)
    obtain ⟨a, rfl⟩ := hsurj x hcl
    apply hx
    have h1 : connectedComponent (F a) = connectedComponent (F 1) :=
      ConnectedComponents.coe_eq_coe.1 (hall a)
    rw [← h1]
    exact mem_connectedComponent
  exact connectedSpace_iff_connectedComponent.2 ⟨F 1, huniv⟩

end GlobalTheory.CompanionTheory.Ar.Approx
end

section
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem exists_section_of_nonempty {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (f : X ⟶ Sp K) [LocallyOfFiniteType f] [Nonempty X] : ∃ s : Sp K ⟶ X, s ≫ f = 𝟙 _ := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, -, hc⟩ := nonempty_inter_closedPoints (Set.univ_nonempty (α := X))
    isClosed_univ.isLocallyClosed
  exact ⟨pointOfClosedPoint (K := K) f x hc, pointOfClosedPoint_comp (K := K) f x hc⟩

theorem exists_comp_eq_of_surjective {K : Type} [Field K] [IsAlgClosed K] (H : Over (Sp K))
    [LocallyOfFiniteType H.hom] (m : H ⟶ H) [Surjective m.left] (x : 𝟙_ (Over (Sp K)) ⟶ H) :
    ∃ y : 𝟙_ (Over (Sp K)) ⟶ H, y ≫ m = x := by
  have h1 : LocallyOfFiniteType (m.left ≫ H.hom) := by rw [Over.w m]; infer_instance
  have h2 : LocallyOfFiniteType m.left := locallyOfFiniteType_of_comp m.left H.hom
  let q : pullback m.left x.left ⟶ Sp K := pullback.snd m.left x.left
  have h3 : LocallyOfFiniteType q := inferInstanceAs (LocallyOfFiniteType (pullback.snd m.left x.left))
  have h4 : Surjective q := inferInstanceAs (Surjective (pullback.snd m.left x.left))
  have h5 : Nonempty ↥(pullback m.left x.left) := by
    obtain ⟨w, -⟩ := q.surjective (default : PrimeSpectrum K)
    exact ⟨w⟩
  obtain ⟨s, hs⟩ := exists_section_of_nonempty q
  refine ⟨Over.homMk (s ≫ pullback.fst m.left x.left) ?_, ?_⟩
  · have hx : x.left ≫ H.hom = 𝟙 _ := Over.w x
    have hm := Over.w m
    calc (s ≫ pullback.fst m.left x.left) ≫ H.hom
        = s ≫ pullback.fst m.left x.left ≫ m.left ≫ H.hom := by rw [hm]; simp
      _ = s ≫ q ≫ x.left ≫ H.hom := by
          rw [← Category.assoc (pullback.fst m.left x.left), pullback.condition]; simp [q]
      _ = 𝟙 _ := by
          rw [hx]
          change s ≫ q ≫ 𝟙 (Sp K) = _
          rw [Category.comp_id]; exact hs
  · ext1
    change (s ≫ pullback.fst m.left x.left) ≫ m.left = x.left
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (s ≫ q) ≫ x.left = x.left
    rw [hs]
    exact Category.id_comp _

theorem geometricallyConnected_of_surjective_pow : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], LocallyOfFiniteType G.hom → QuasiCompact G.hom → (∀ n : ℕ, n ≠ 0 → Surjective ((𝟙 G) ^ n : G ⟶ G).left) → GeometricallyConnected G.hom := by
  intro S G _ _ hl hq hn
  refine ⟨fun k _ y Z a b hZ => ?_⟩
  let L := AlgebraicClosure k
  let j : Sp L ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let t : Sp L ⟶ S := j ≫ y
  let H : Over (Sp L) := (Over.pullback t).obj G
  have hlH : LocallyOfFiniteType H.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom t))
  have hqH : QuasiCompact H.hom := inferInstanceAs (QuasiCompact (pullback.snd G.hom t))
  have hconn : ConnectedSpace H.left := by
    refine GlobalTheory.CompanionTheory.Ar.Approx.connectedSpace_of_divisible L H hlH hqH fun n hn0 x => ?_
    have e : (Over.pullback t).map ((𝟙 G) ^ n) = (𝟙 H) ^ n := by
      have := map_pow (Over.pullback t).homMonoidHom (𝟙 G) n
      simpa using this
    have hs : Surjective ((𝟙 H) ^ n : H ⟶ H).left := by
      have hG := hn n hn0
      have sq : IsPullback ((Over.pullback t).map ((𝟙 G) ^ n)).left (pullback.fst G.hom t)
          (pullback.fst G.hom t) ((𝟙 G) ^ n : G ⟶ G).left := by
        have hA : ((Over.pullback t).map ((𝟙 G) ^ n)).left ≫ pullback.fst G.hom t =
            pullback.fst G.hom t ≫ ((𝟙 G) ^ n : G ⟶ G).left := pullback.lift_fst _ _ _
        have hB : ((Over.pullback t).map ((𝟙 G) ^ n)).left ≫ pullback.snd G.hom t =
            pullback.snd G.hom t := Over.w ((Over.pullback t).map ((𝟙 G) ^ n))
        have rect : IsPullback (((Over.pullback t).map ((𝟙 G) ^ n)).left ≫ pullback.snd G.hom t)
            (pullback.fst G.hom t) t (((𝟙 G) ^ n : G ⟶ G).left ≫ G.hom) := by
          rw [hB, Over.w ((𝟙 G) ^ n : G ⟶ G)]
          exact (IsPullback.of_hasPullback _ _).flip
        exact IsPullback.of_right rect hA (IsPullback.of_hasPullback _ _).flip
      rw [← e]
      exact MorphismProperty.of_isPullback (P := @Surjective) sq.flip hG
    obtain ⟨w, hw⟩ := exists_comp_eq_of_surjective H ((𝟙 H) ^ n) x
    refine ⟨w, ?_⟩
    rw [← hw, MonObj.comp_pow, Category.comp_id]
  have hj : Surjective j := ⟨fun z => ⟨default, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  have big : IsPullback (pullback.fst b j ≫ a) (pullback.snd b j) G.hom t :=
    (IsPullback.of_hasPullback b j).paste_horiz hZ
  have hc' : ConnectedSpace ↥(pullback G.hom t) := hconn
  have hsurj : Surjective (big.isoPullback.inv ≫ pullback.fst b j) := inferInstance
  exact (big.isoPullback.inv ≫ pullback.fst b j).surjective.connectedSpace
    (big.isoPullback.inv ≫ pullback.fst b j).continuous

end GlobalTheory.CompanionTheory.Ar.Approx
end
end

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyConnected_of_commGroup_nsmul_surjective : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], LocallyOfFiniteType G.hom → QuasiCompact G.hom → (∀ n : ℕ, n ≠ 0 → Surjective ((𝟙 G) ^ n : G ⟶ G).left) → GeometricallyConnected G.hom := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_of_surjective_pow
end

section
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem dense_range_fst_generic (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {X : Scheme.{0}} (p : X ⟶ Sp R) (hp : IsOpenMap p) :
    Dense (Set.range (pullback.fst p (spMap (algebraMap R K)))) := by
  classical
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  let y : PrimeSpectrum K := ⟨⊥, Ideal.isPrime_bot⟩
  have hy : ∀ z : PrimeSpectrum R, PrimeSpectrum.comap (algebraMap R K) y ⤳ z := by
    intro z
    rw [← PrimeSpectrum.le_iff_specializes]
    intro a ha
    have h0 : algebraMap R K a = 0 := ha
    have : a = 0 := hinj (by rw [h0, map_zero])
    rw [this]
    exact z.asIdeal.zero_mem
  have hyy : (spMap (algebraMap R K)) y = PrimeSpectrum.comap (algebraMap R K) y := rfl
  rw [Scheme.Pullback.range_fst, dense_iff_inter_open]
  rintro U hU ⟨x, hx⟩
  have hmem : (spMap (algebraMap R K)) y ∈ p '' U := by
    rw [hyy]
    exact (hy (p x)).mem_open (hp U hU) ⟨x, hx, rfl⟩
  obtain ⟨x', hx'U, hx'⟩ := hmem
  exact ⟨x', hx'U, ⟨y, hx'.symm⟩⟩

theorem geometricallyConnected_of_generic : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsProper G.hom → GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap R K))) → GeometricallyConnected G.hom := by
  intro R K _ _ _ _ _ G _ _ hsm hpr hgc
  set f := spMap (algebraMap R K) with hf
  let F := Over.pullback f
  let GK := F.obj G
  have hab : IsAbelianScheme GK := by
    refine IsAbelianScheme.mk inferInstance ?_ ?_ hgc
    · show Smooth (pullback.snd G.hom f)
      infer_instance
    · show IsProper (pullback.snd G.hom f)
      infer_instance
  refine GlobalTheory.T.geometricallyConnected_of_commGroup_nsmul_surjective (Sp R) G inferInstance inferInstance ?_
  intro n hn
  have hK := GlobalTheory.T.abelianScheme_nsmul_surjective K GK hab n hn
  have hmap : F.map (𝟙 G ^ n) = 𝟙 GK ^ n := by
    rw [← F.map_id]
    exact (Functor.homMonoidHom F (X := G) (M := G)).map_pow _ n
  set φ := (𝟙 G ^ n).left with hφ
  have hsq : (𝟙 GK ^ n).left ≫ pullback.fst G.hom f = pullback.fst G.hom f ≫ φ := by
    rw [← hmap]
    simp [F, φ] <;> exact pullback.lift_fst _ _ _
  have hw : φ ≫ G.hom = G.hom := Over.w (𝟙 G ^ n)
  have hcomp : IsProper (φ ≫ G.hom) := by rw [hw]; exact hpr
  have hsep : IsSeparated G.hom := inferInstance
  have hprop : UniversallyClosed φ := by
    first
    | exact (MorphismProperty.of_postcomp (W := @IsProper) (W' := @IsSeparated) φ G.hom hsep hcomp).toUniversallyClosed
    | exact MorphismProperty.of_postcomp (W := @UniversallyClosed) (W' := @IsSeparated) φ G.hom hsep inferInstance
    | exact UniversallyClosed.of_comp_of_isSeparated φ G.hom
    | exact (IsProper.of_comp φ G.hom).toUniversallyClosed
  have hcl : IsClosed (Set.range φ) := φ.isClosedMap.isClosed_range
  have hop : IsOpenMap G.hom := G.hom.isOpenMap
  have hdense := dense_range_fst_generic R K G.hom hop
  have hsub : Set.range (pullback.fst G.hom f) ⊆ Set.range φ := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨w, rfl⟩ := hK.surj z
    refine ⟨pullback.fst G.hom f w, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply]
  have huniv : Set.range φ = Set.univ :=
    (hdense.mono hsub).closure_eq ▸ hcl.closure_eq.symm
  exact ⟨fun x => by
    have : x ∈ Set.range φ := huniv ▸ Set.mem_univ x
    exact this⟩

end GlobalTheory.CompanionTheory.Ar.Approx
end

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
theorem _root_.GlobalTheory.T.geometricallyConnected_of_generic_fiber_smooth_proper : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsProper G.hom → GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap R K))) → GeometricallyConnected G.hom := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_of_generic
end

section
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem geometricallyConnected_snd_snd_iff {X S S' S'' : Scheme.{0}} (g : X ⟶ S) (f : S' ⟶ S)
    (b : S'' ⟶ S') :
    GeometricallyConnected (pullback.snd (pullback.snd g f) b) ↔
      GeometricallyConnected (pullback.snd g (b ≫ f)) := by
  haveI : MorphismProperty.RespectsIso @GeometricallyConnected :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [← pullbackLeftPullbackSndIso_hom_snd g f b]
  exact MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected _ _

private theorem spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) : spMap g ≫ spMap f = spMap (g.comp f) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem stableUnderSpecialization_geometricallyConnected :
    ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G],
      Smooth G.hom → IsProper G.hom →
      StableUnderSpecialization {x : PrimeSpectrum k | GeometricallyConnected
        (pullback.snd G.hom (spMap (algebraMap k x.asIdeal.ResidueField)))} := by
  intro k _ _ G _ _ hsm hpr x y hxy hx
  haveI := hsm
  haveI := hpr
  have hle : x.asIdeal ≤ y.asIdeal := (PrimeSpectrum.le_iff_specializes x y).mpr hxy
  have hs' : Smooth ((Over.pullback (spMap (algebraMap k (k ⧸ x.asIdeal)))).obj G).hom := by
    show Smooth (pullback.snd G.hom (spMap (algebraMap k (k ⧸ x.asIdeal))))
    infer_instance
  have hp' : IsProper ((Over.pullback (spMap (algebraMap k (k ⧸ x.asIdeal)))).obj G).hom := by
    show IsProper (pullback.snd G.hom (spMap (algebraMap k (k ⧸ x.asIdeal))))
    infer_instance
  have hgen : GeometricallyConnected (pullback.snd
      ((Over.pullback (spMap (algebraMap k (k ⧸ x.asIdeal)))).obj G).hom
      (spMap (algebraMap (k ⧸ x.asIdeal) x.asIdeal.ResidueField))) := by
    show GeometricallyConnected (pullback.snd (pullback.snd G.hom (spMap (algebraMap k (k ⧸ x.asIdeal))))
      (spMap (algebraMap (k ⧸ x.asIdeal) x.asIdeal.ResidueField)))
    rw [geometricallyConnected_snd_snd_iff, spMap_comp_moduli_spaces, ← IsScalarTower.algebraMap_eq]
    exact hx
  have hG' : GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k (k ⧸ x.asIdeal)))) :=
    GlobalTheory.T.geometricallyConnected_of_generic_fiber_smooth_proper (k ⧸ x.asIdeal) x.asIdeal.ResidueField
      ((Over.pullback (spMap (algebraMap k (k ⧸ x.asIdeal)))).obj G) hs' hp' hgen
  have hker : ∀ a ∈ x.asIdeal, algebraMap k y.asIdeal.ResidueField a = 0 := fun a ha =>
    Ideal.algebraMap_residueField_eq_zero.mpr (hle ha)
  have hφ : (Ideal.Quotient.lift x.asIdeal (algebraMap k y.asIdeal.ResidueField) hker).comp
      (algebraMap k (k ⧸ x.asIdeal)) = algebraMap k y.asIdeal.ResidueField := by
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.lift_comp_mk _ _ _
  show GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k y.asIdeal.ResidueField)))
  rw [← hφ, ← spMap_comp_moduli_spaces, ← geometricallyConnected_snd_snd_iff]
  infer_instance

end GlobalTheory.CompanionTheory.Ar.Approx
end

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
theorem _root_.GlobalTheory.T.connected_fibers_stableUnderSpecialization : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsProper G.hom → StableUnderSpecialization {x : PrimeSpectrum k | GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k x.asIdeal.ResidueField)))} := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Approx.stableUnderSpecialization_geometricallyConnected
end

section
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem isClosed_of_stable_of_noetherian {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] [QuasiSober X] (V : Set X)
    (hg : StableUnderGeneralization V) (hs : StableUnderSpecialization V) : IsClosed V := by
  have key : ∀ x ∈ V, irreducibleComponent x ⊆ V := by
    intro x hx y hy
    have hS : IsGenericPoint (isIrreducible_irreducibleComponent (x := x)).genericPoint
        (irreducibleComponent x) :=
      (isIrreducible_irreducibleComponent (x := x)).isGenericPoint_genericPoint
        isClosed_irreducibleComponent
    exact hs (hS.specializes hy) (hg (hS.specializes mem_irreducibleComponent) hx)
  have hV : V = ⋃₀ {C | C ∈ irreducibleComponents X ∧ C ⊆ V} := by
    apply Set.Subset.antisymm
    · intro x hx
      exact ⟨irreducibleComponent x,
        ⟨irreducibleComponent_mem_irreducibleComponents x, key x hx⟩, mem_irreducibleComponent⟩
    · exact Set.sUnion_subset fun C hC => hC.2
  rw [hV, Set.sUnion_eq_biUnion]
  exact Set.Finite.isClosed_biUnion
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset fun C hC => hC.1)
    fun C hC => isClosed_of_mem_irreducibleComponents C hC.1

theorem isOpen_of_stable (k : Type) [CommRing k] [IsNoetherianRing k] (U : Set (PrimeSpectrum k))
    (hg : StableUnderGeneralization U) (hs : StableUnderSpecialization U) : IsOpen U := by
  rw [← isClosed_compl_iff]
  exact isClosed_of_stable_of_noetherian Uᶜ
    (stableUnderGeneralization_compl_iff.mpr hs) (stableUnderSpecialization_compl_iff.mpr hg)

end GlobalTheory.CompanionTheory.Ar.Approx
end

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_of_stable_under_generalization_specialization : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (U : Set (PrimeSpectrum k)), StableUnderGeneralization U → StableUnderSpecialization U → IsOpen U := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Approx.isOpen_of_stable
end

section
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem isOpen_geometricallyConnected_fibres :
    ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G],
      Smooth G.hom → IsProper G.hom →
      IsOpen {x : PrimeSpectrum k | GeometricallyConnected
        (pullback.snd G.hom (spMap (algebraMap k x.asIdeal.ResidueField)))} := by
  intro k _ _ G _ _ hs hp
  have hgen := GlobalTheory.T.geometric_connectedness_generalizes k G.left G.hom (η[G]).left (Over.w η[G]) hs hp
  have hspec := GlobalTheory.T.connected_fibers_stableUnderSpecialization k G hs hp
  exact GlobalTheory.T.isOpen_of_stable_under_generalization_specialization k _ hgen hspec

end GlobalTheory.CompanionTheory.Ar.Approx
end

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
theorem _root_.GlobalTheory.T.isOpen_geometricallyConnected_fibers : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsProper G.hom → IsOpen {x : PrimeSpectrum k | GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k x.asIdeal.ResidueField)))} := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Approx.isOpen_geometricallyConnected_fibres
end

section
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem geometricallyConnected_descends_to_fg :
    ∀ (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V] [Algebra k V] (G : Over (Sp k))
      [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsProper G.hom →
      GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k V))) →
      ∃ R : Subalgebra k V, R.FG ∧
        GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k R))) := by
  intro k V _ _ _ _ G _ _ hs hp hV
  classical
  set U : Set (PrimeSpectrum k) := {x | GeometricallyConnected
      (pullback.snd G.hom (spMap (algebraMap k x.asIdeal.ResidueField)))} with hUdef
  have hU : IsOpen U := GlobalTheory.T.isOpen_geometricallyConnected_fibers k G hs hp
  have hVU : ∀ x ∈ Set.range (PrimeSpectrum.comap (algebraMap k V)), x ∈ U :=
    (GlobalTheory.T.geometricallyConnected_baseChange_iff_fibers k V G.left G.hom).1 hV
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1 hU.isClosed_compl
  have htop : Ideal.map (algebraMap k V) I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hx := hVU (PrimeSpectrum.comap (algebraMap k V) ⟨M, hM.isPrime⟩) ⟨_, rfl⟩
    have hx' : PrimeSpectrum.comap (algebraMap k V) ⟨M, hM.isPrime⟩ ∈ Uᶜ := by
      rw [hI, PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.comap_asIdeal]
      exact Ideal.map_le_iff_le_comap.1 hle
    exact hx' hx
  have h1 : (1 : V) ∈ Submodule.span V (algebraMap k V '' (I : Set k)) := by
    have h := (Ideal.eq_top_iff_one _).1 htop
    exact h
  obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.1 h1
  choose f hfI hfg using fun i => (g i).2
  let s : Finset V := Finset.univ.image c
  have hc : ∀ i, c i ∈ Algebra.adjoin k (s : Set V) := fun i =>
    Algebra.subset_adjoin (by simp [s])
  refine ⟨Algebra.adjoin k (s : Set V), Subalgebra.fg_adjoin_finset s, ?_⟩
  apply (GlobalTheory.T.geometricallyConnected_baseChange_iff_fibers k (Algebra.adjoin k (s : Set V)) G.left G.hom).2
  rintro x ⟨y, rfl⟩
  by_contra hx
  have hx' : PrimeSpectrum.comap (algebraMap k (Algebra.adjoin k (s : Set V))) y ∈ Uᶜ := hx
  rw [hI, PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.comap_asIdeal] at hx'
  have hmem : (∑ i, (⟨c i, hc i⟩ : Algebra.adjoin k (s : Set V)) *
      algebraMap k (Algebra.adjoin k (s : Set V)) (f i)) ∈ y.asIdeal :=
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hx' (hfI i))
  have hone : (∑ i, (⟨c i, hc i⟩ : Algebra.adjoin k (s : Set V)) *
      algebraMap k (Algebra.adjoin k (s : Set V)) (f i)) = 1 := by
    apply Subtype.ext
    have key : (Algebra.adjoin k (s : Set V)).val (∑ i, (⟨c i, hc i⟩ : Algebra.adjoin k (s : Set V)) *
        algebraMap k (Algebra.adjoin k (s : Set V)) (f i)) = ∑ i, c i • (g i : V) := by
      simp only [map_sum, map_mul, AlgHom.commutes, Subalgebra.coe_val, hfg, smul_eq_mul]
    exact key.trans (hsum.trans (by simp))
  exact y.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hone ▸ hmem))

end GlobalTheory.CompanionTheory.Ar.Approx
end

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
theorem _root_.GlobalTheory.T.geometricallyConnected_descends_to_finitelyGenerated : ∀ (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V] [Algebra k V] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → IsProper G.hom → GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k V))) → ∃ R : Subalgebra k V, R.FG ∧ GeometricallyConnected (pullback.snd G.hom (spMap (algebraMap k R))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_descends_to_fg
end
