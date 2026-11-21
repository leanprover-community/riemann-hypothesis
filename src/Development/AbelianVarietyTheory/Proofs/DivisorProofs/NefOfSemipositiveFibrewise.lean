import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineBundleIntersectionNumberGroundFieldChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EulerCharLineBundleFibreModpEqRatProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeModLProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeNonnegOfCurveDegreeNonnegOverZmod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveDegreeNonnegZmodFibreOfNefOnFiniteFieldFibr

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CurveClosure

open TensorProduct

theorem isReduced_pullback_localization : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S] (V : Scheme.{0}) [IsReduced V] (f : V ⟶ Sp R), IsReduced (pullback f (spMap (algebraMap R S))) := by
  intro R S _ _ _ M _ V _ f
  let 𝒰 := Scheme.Pullback.openCoverOfLeft V.affineOpenCover.openCover f (spMap (algebraMap R S))
  have : ∀ i, IsReduced (𝒰.X i) := fun i => by
    have := V.affineOpenCover.map_prop i
    have h0 : IsReduced (Spec (V.affineOpenCover.X i)) :=
      isReduced_of_isOpenImmersion (V.affineOpenCover.f i)
    have h1 := (affine_isReduced_iff _).mp h0
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (V.affineOpenCover.f i ≫ f)
    change IsReduced (pullback (V.affineOpenCover.f i ≫ f) _)
    rw [← hφ]
    letI : Algebra R (V.affineOpenCover.X i) := φ.hom.toAlgebra
    have h2 : IsReduced (V.affineOpenCover.X i ⊗[R] S) :=
      isReduced_localizationPreserves (Algebra.algebraMapSubmonoid (V.affineOpenCover.X i) M) _ h1
    have h3 := (affine_isReduced_iff (.of (V.affineOpenCover.X i ⊗[R] S))).mpr h2
    exact isReduced_of_isOpenImmersion (pullbackSpecIso R (V.affineOpenCover.X i) S).hom
  exact IsReduced.of_openCover _ 𝒰

theorem exists_iso_red_of_range : ∀ (X G : Scheme.{0}) (g : G ⟶ X) [IsClosedImmersion g] [IsReduced G] (Z : Closeds X), Set.range g = (Z : Set X) → ∃ e : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≅ G, e.hom ≫ g = redι Z := by
  intro X G g _ _ Z h
  have hker : Scheme.IdealSheafData.vanishingIdeal Z = g.ker := by
    rw [← InterModel.radical_ker g, ← Scheme.IdealSheafData.vanishingIdeal_support]
    congr 1
    ext1
    rw [Scheme.Hom.support_ker, g.isClosedEmbedding.isClosed_range.closure_eq, h]
  show ∃ e : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≅ G,
    e.hom ≫ g = (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
  rw [hker]
  refine ⟨(asIso g.toImage).symm, ?_⟩
  rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq]
  exact g.toImage_imageι.symm

theorem le_dim_of_genFibre : ∀ (F : Type) [Field F] [NumberField F] (W G : Scheme.{0}) [IsIntegral W] (q : W ⟶ Sp (𝓞 F)) (g : G ⟶ W) (s : G ⟶ Sp F) (d : ℕ), IsProjOver q → CharZero Γ(W, ⊤) → IsPullback g s q (spMap (algebraMap (𝓞 F) F)) → topologicalKrullDim G = d → (((d + 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim W) := by
  intro F _ _ W G _ q g s d hq _ hpb hd
  obtain ⟨N, i, _, hi⟩ := hq
  have := isProper_str (𝓞 F) N
  have : IsProper q := hi ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom (𝓞 F))) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  let t : W ⟶ Sp ℤ := q ≫ spMap (Int.castRingHom (𝓞 F))
  haveI : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  haveI : IsPreimmersion g := MorphismProperty.of_isPullback hpb.flip inferInstance
  have hgen : ∀ x, t (g x) = genericPoint (Sp ℤ) := by
    intro x
    rw [genericPoint_eq_bot_of_affine]
    have e : g ≫ t = s ≫ spMap ((algebraMap (𝓞 F) F).comp (Int.castRingHom (𝓞 F))) := by
      simp only [t, ← Category.assoc, hpb.w]
      simp [spMap, Spec.map_comp]
    change (g ≫ t) x = _
    rw [e]
    refine PrimeSpectrum.ext ?_
    change Ideal.comap _ (s x).asIdeal = ⊥
    have hp : (show PrimeSpectrum F from s x).asIdeal.IsPrime := (show PrimeSpectrum F from s x).isPrime
    rw [Ideal.eq_bot_of_prime (show PrimeSpectrum F from s x).asIdeal]
    exact Ideal.comap_bot_of_injective _ (RingHom.injective_int _)
  have key := GlobalTheory.Vert.dim_add_dim_le (S := W) (T := Sp ℤ) (W := G) t.isClosedMap g.continuous
    g.isEmbedding.injective hgen
  have hZ : topologicalKrullDim (Sp ℤ) = 1 := by
    change topologicalKrullDim (PrimeSpectrum ℤ) = 1
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
  rw [hd, hZ] at key
  exact_mod_cast key

theorem dim_le_of_genFibre : ∀ (F : Type) [Field F] [NumberField F] (W G : Scheme.{0}) [IsIntegral W] (q : W ⟶ Sp (𝓞 F)) (g : G ⟶ W) (s : G ⟶ Sp F) (d : ℕ), IsProjOver q → CharZero Γ(W, ⊤) → IsPullback g s q (spMap (algebraMap (𝓞 F) F)) → topologicalKrullDim G = d → topologicalKrullDim W ≤ ((d + 1 : ℕ) : WithBot ℕ∞) := by
  intro F _ _ W G _ q g s d hq hc hpb hd
  obtain ⟨N, i, _, hi⟩ := hq
  have := isProper_str (𝓞 F) N
  have : IsProper q := hi ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom (𝓞 F))) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  let t : W ⟶ Sp ℤ := q ≫ spMap (Int.castRingHom (𝓞 F))
  have : Flat t := (flat_int_iff_charZero t).2 hc
  have : LocallyOfFiniteType t := inferInstance
  haveI : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  obtain ⟨he, hr⟩ := isEmbedding_and_range_eq_of_isPullback q hpb

  have hfib : Set.range g = t ⁻¹' {genericPoint (Sp ℤ)} := by
    rw [hr, genericPoint_eq_bot_of_affine]
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hy⟩
      change Spec.map _ (q x) = _
      rw [← hy]
      refine PrimeSpectrum.ext ?_
      change Ideal.comap _ (Ideal.comap _ (show PrimeSpectrum F from y).asIdeal) = ⊥
      have hp : (show PrimeSpectrum F from y).asIdeal.IsPrime := (show PrimeSpectrum F from y).isPrime
      rw [Ideal.eq_bot_of_prime (show PrimeSpectrum F from y).asIdeal, Ideal.comap_comap]
      exact Ideal.comap_bot_of_injective _ (RingHom.injective_int _)
    · intro h
      have h' : Ideal.comap (algebraMap ℤ (𝓞 F)) (show PrimeSpectrum (𝓞 F) from q x).asIdeal = ⊥ :=
        congrArg PrimeSpectrum.asIdeal h
      have h0 : (show PrimeSpectrum (𝓞 F) from q x).asIdeal = ⊥ := Ideal.eq_bot_of_comap_eq_bot h'
      refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F), ?_⟩
      refine PrimeSpectrum.ext ?_
      change Ideal.comap _ ⊥ = (show PrimeSpectrum (𝓞 F) from q x).asIdeal
      rw [h0]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)

  obtain ⟨A, _, _, instA, _, _, j, _, -, -, hA⟩ := exists_affine_chart_trdeg_eq t (genericPoint W)
  obtain rfl : instA = Ring.toIntAlgebra A := Subsingleton.elim _ _
  obtain ⟨d', hd'⟩ := exists_trdeg_eq_natCast ℤ (A := A)
  have hfd := topologicalKrullDim_preimage_genericPoint_eq t (d := d') (hA ▸ hd')
  rw [← hfib, topologicalKrullDim_eq_of_isEmbedding he rfl, hd] at hfd
  have hdd : d' = d := by exact_mod_cast hfd.symm
  subst hdd
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
  obtain ⟨B, _, _, _, _, _, j', _, ⟨b, rfl⟩, -, hB⟩ := exists_affine_chart_trdeg_eq t x
  refine ⟨Set.range j', j'.isOpenEmbedding.isOpen_range, ⟨b, rfl⟩, ?_⟩
  rw [topologicalKrullDim_eq_of_isEmbedding j'.isOpenEmbedding.isEmbedding rfl]
  refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim B).le.trans ?_
  have hdB : Algebra.trdeg ℤ B = d' := hB.trans (hA.symm.trans hd')
  have hZ1 : ringKrullDim ℤ ≤ 1 := by
    exact_mod_cast Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 ℤ)
  refine (IntModel.ringKrullDim_le_add (O := ℤ) ℚ).trans ?_
  rw [ringKrullDim_genericFibre_eq ℤ ℚ hdB]
  refine (add_le_add hZ1 (le_refl ((d' : ℕ) : WithBot ℕ∞))).trans_eq ?_
  push_cast
  exact add_comm _ _

theorem dim_eq_of_genFibre : ∀ (F : Type) [Field F] [NumberField F] (W G : Scheme.{0}) [IsIntegral W] (q : W ⟶ Sp (𝓞 F)) (g : G ⟶ W) (s : G ⟶ Sp F) (d : ℕ), IsProjOver q → CharZero Γ(W, ⊤) → IsPullback g s q (spMap (algebraMap (𝓞 F) F)) → topologicalKrullDim G = d → topologicalKrullDim W = (d + 1 : ℕ) :=
  fun F _ _ W G _ q g s d h₁ h₂ h₃ h₄ =>
    le_antisymm (dim_le_of_genFibre F W G q g s d h₁ h₂ h₃ h₄) (le_dim_of_genFibre F W G q g s d h₁ h₂ h₃ h₄)

theorem exists_closure_arith_surface : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (P : TrueGeo.Model Y) (Z : Closeds Y.X), IsCompleteCurve F Z → ∃ (W : Scheme.{0}) (w : W ⟶ P.X) (z : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ W), IsClosedImmersion w ∧ IsArithVar (w ≫ P.p) 1 ∧ z ≫ w = redι Z ≫ P.j ∧ IsPullback z (redι Z ≫ Y.str) (w ≫ P.p) (spMap (algebraMap (𝓞 F) F)) := by
  intro F _ _ Y P Z hZ
  let S : Closeds P.X := ⟨closure (P.j '' (Z : Set Y.X)), isClosed_closure⟩
  have hSirr : IsIrreducible (S : Set P.X) := (hZ.isIrreducible.image _ P.j.continuous.continuousOn).closure
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal S).subscheme := isIntegral_red hSirr
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := isIntegral_red hZ.isIrreducible
  set w := redι S with hw
  haveI : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  haveI : IsPreimmersion P.j := MorphismProperty.of_isPullback P.pb.flip inferInstance
  have hpb1 : IsPullback (pullback.fst w P.j) (pullback.snd w P.j ≫ Y.str) (w ≫ P.p)
      (spMap (algebraMap (𝓞 F) F)) := (IsPullback.of_hasPullback w P.j).paste_vert P.pb
  haveI : IsReduced (pullback (w ≫ P.p) (spMap (algebraMap (𝓞 F) F))) :=
    isReduced_pullback_localization (𝓞 F) F (nonZeroDivisors (𝓞 F)) _ _
  haveI : IsReduced (pullback w P.j) := isReduced_of_isOpenImmersion hpb1.isoPullback.hom
  have hrange : Set.range (pullback.snd w P.j) = (Z : Set Y.X) := by
    rw [Scheme.Pullback.range_snd, hw, range_redι]
    change P.j ⁻¹' closure (P.j '' (Z : Set Y.X)) = _
    rw [← P.j.isEmbedding.isInducing.closure_eq_preimage_closure_image, Z.isClosed.closure_eq]
  obtain ⟨e, he⟩ := exists_iso_red_of_range _ _ (pullback.snd w P.j) Z hrange
  have hzw : (e.hom ≫ pullback.fst w P.j) ≫ w = redι Z ≫ P.j := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, he]
  have hpb : IsPullback (e.hom ≫ pullback.fst w P.j) (redι Z ≫ Y.str) (w ≫ P.p)
      (spMap (algebraMap (𝓞 F) F)) := by
    refine IsPullback.of_iso hpb1 e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp [← he]
    · simp
    · simp
  have hcZ : CharZero Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) := by
    let φ : F →+* Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) :=
      (redι Z ≫ Y.str).appTop.hom.comp (Scheme.ΓSpecIso (.of F)).inv.hom
    exact charZero_of_injective_ringHom φ.injective
  have hcW : CharZero Γ((Scheme.IdealSheafData.vanishingIdeal S).subscheme, ⊤) :=
    (e.hom ≫ pullback.fst w P.j).appTop.hom.charZero
  have hproj : IsProjOver (w ≫ P.p) := by
    obtain ⟨N, j, _, hj⟩ := P.ar.isProjOver
    exact ⟨N, w ≫ j, inferInstance, by rw [Category.assoc, hj]⟩
  have hdZ : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme = (1 : ℕ) := by
    rw [topologicalKrullDim_red, hZ.dim_eq]; rfl
  have hdim := dim_eq_of_genFibre F _ _ (w ≫ P.p) (e.hom ≫ pullback.fst w P.j) (redι Z ≫ Y.str) 1 hproj hcW hpb hdZ
  exact ⟨_, w, e.hom ≫ pullback.fst w P.j, inferInstance, P.ar.of_isClosedImmersion w hcW hdim, hzw, hpb⟩

end GlobalTheory.CurveClosure
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_curve_arith_model_closure : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (P : TrueGeo.Model Y) (Z : Closeds Y.X), IsCompleteCurve F Z → ∃ (W : Scheme.{0}) (w : W ⟶ P.X) (z : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ W), IsClosedImmersion w ∧ IsArithVar (w ≫ P.p) 1 ∧ z ≫ w = redι Z ≫ P.j ∧ IsPullback z (redι Z ≫ Y.str) (w ≫ P.p) (spMap (algebraMap (𝓞 F) F)) := by
  first | exact @GlobalTheory.CurveClosure.exists_closure_arith_surface | exact GlobalTheory.CurveClosure.exists_closure_arith_surface | (intros; apply GlobalTheory.CurveClosure.exists_closure_arith_surface <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RatFibreClosure

theorem isPullback_spec_ringOfIntegers (F : Type) [Field F] [NumberField F] :
    IsPullback (spMap (algebraMap (𝓞 F) F)) (spMap (algebraMap ℚ F))
      (spMap (Int.castRingHom (𝓞 F))) (spMap (Int.castRingHom ℚ)) := by
  have h : Algebra.IsPushout ℤ (𝓞 F) ℚ F :=
    (Algebra.isLocalization_iff_isPushout (nonZeroDivisors ℤ) ℚ).1 inferInstance
  have h' := (CommRingCat.isPushout_iff_isPushout (R := ℤ) (R' := 𝓞 F) (S := ℚ) (S' := F)).2 h
  exact isPullback_SpecMap_of_isPushout _ _ _ _ h'

theorem ratDeg_eq_finrank_mul_interNumRed : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (P : TrueGeo.Model Y) (Z : Closeds Y.X), IsCompleteCurve F Z → ∀ (W : Scheme.{0}) (w : W ⟶ P.X) (z : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ W), IsArithVar (w ≫ P.p) 1 → z ≫ w = redι Z ≫ P.j → IsPullback z (redι Z ≫ Y.str) (w ≫ P.p) (spMap (algebraMap (𝓞 F) F)) → ∀ M : LB P.X, M.IsLB → ratDeg (w ≫ P.p) (M.pull w) = (Module.finrank ℚ F : ℤ) * interNumRed F Z ![M.pull P.j] := by
  intro F _ _ Y P Z hZ W w z hW hzw H M hM
  letI iF : Algebra F Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) := algebraΓOfHom (redι Z ≫ Y.str)
  letI iQ : Algebra ℚ Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) := ((algebraMap F Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤)).comp (algebraMap ℚ F)).toAlgebra
  haveI : IsScalarTower ℚ F Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) := .of_algebraMap_eq fun _ ↦ rfl
  have hi : ∀ r : F, (redι Z).appTop (algebraMap F Γ(Y.X, ⊤) r) = algebraMap F Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) r :=
    fun _ ↦ rfl
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := isIntegral_red hZ.isIrreducible
  have hC : VB.IsProjCurve F (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
    refine ⟨inferInstance, (topologicalKrullDim_red Z).trans hZ.dim_eq, ?_⟩
    rw [strHom_eq (f := redι Z ≫ Y.str) fun _ ↦ rfl]
    obtain ⟨n, f, hf, hs⟩ := Y.isProjOver
    exact ⟨n, redι Z ≫ f, inferInstance, by rw [Category.assoc, hs]⟩

  have H' := H.paste_vert (isPullback_spec_ringOfIntegers F)
  set R := ratFibre (w ≫ P.p)
  set e : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≅ R := H'.isoIsPullback _ _ (ratFibre.isPullback (w ≫ P.p)) with he
  have efst : e.hom ≫ ratFibre.fst (w ≫ P.p) = z := IsPullback.isoIsPullback_hom_fst _ _ H' (ratFibre.isPullback _)
  have hf : ∀ r : ℚ, e.hom.appTop (algebraMap ℚ Γ(R, ⊤) r) = algebraMap ℚ Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) r := fun r ↦
    RingHom.congr_fun (RingHom.ext_rat (e.hom.appTop.hom.comp (algebraMap ℚ _)) (algebraMap ℚ _)) r

  set L := (M.pull w).pull (ratFibre.fst (w ≫ P.p)) with hLdef
  set N := (M.pull P.j).pull (redι Z) with hNdef
  have hL : L.IsLB := Semi.LB.isLB_pull (Semi.LB.isLB_pull hM _) _
  have hN : N.IsLB := Semi.LB.isLB_pull (Semi.LB.isLB_pull hM _) _
  have hLe : (L.pull e.hom).IsLB := Semi.LB.isLB_pull hL _
  have hcls : cls (L.pull e.hom) hLe = cls N hN := by
    rw [cls_pull hL, cls_pull (Semi.LB.isLB_pull hM _), cls_pull hM, cls_pull (Semi.LB.isLB_pull hM _),
      cls_pull hM]
    simp only [← pull_comp, ← Category.assoc, efst, hzw]

  have h₁ : chi ℚ (structureModule R) = chi ℚ (structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) :=
    (chi_congr ℚ (asIso (unitToPush e.hom))).trans (chi_pushforward_of_isClosedImmersion hf _)
  have h₂ : chi ℚ (toMod L) = chi ℚ (twist (structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) N) := by
    refine (chi_congr ℚ (Twist.unitTwistIso L)).symm.trans ?_
    refine (chi_congr ℚ ((twistFunctor L).mapIso (asIso (unitToPush e.hom)))).trans ?_
    refine (chi_twist_pushforward_of_isClosedImmersion hf _ L).trans ?_
    exact (nonempty_twist_iso_of_cls_eq _ hLe hN hcls).elim (chi_congr ℚ)

  have h₃ : interNumRed F Z ![M.pull P.j] = chi F (twist (structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) N) - chi F (structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
    have e₁ := interNumOn_eq_interNum_pull (k := F) (L := ![M.pull P.j]) hi
      (fun i ↦ by fin_cases i; exact Semi.LB.isLB_pull hM _)
    have e₂ := hC.degLB_eq_interNum hN
    rw [VB.degLB_eq hN, ← chi_congr F (Twist.unitTwistIso N)] at e₂
    rw [interNumRed_def, interNumSub_def]
    refine e₁.trans (Eq.trans ?_ e₂.symm)
    congr 1
    funext i
    fin_cases i
    rfl
  rw [ratDeg, degOfRank, h₁, h₂, h₃, GroundFieldChange.chi_fieldChange ℚ F (Scheme.IdealSheafData.vanishingIdeal Z).subscheme,
    GroundFieldChange.chi_fieldChange ℚ F (Scheme.IdealSheafData.vanishingIdeal Z).subscheme]
  push_cast
  ring

end GlobalTheory.RatFibreClosure
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_model_rational_degree : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (P : TrueGeo.Model Y) (Z : Closeds Y.X), IsCompleteCurve F Z → ∀ (W : Scheme.{0}) (w : W ⟶ P.X) (z : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ W), IsArithVar (w ≫ P.p) 1 → z ≫ w = redι Z ≫ P.j → IsPullback z (redι Z ≫ Y.str) (w ≫ P.p) (spMap (algebraMap (𝓞 F) F)) → ∀ M : LB P.X, M.IsLB → ratDeg (w ≫ P.p) (M.pull w) = (Module.finrank ℚ F : ℤ) * interNumRed F Z ![M.pull P.j] := by
  first | exact @GlobalTheory.RatFibreClosure.ratDeg_eq_finrank_mul_interNumRed | exact GlobalTheory.RatFibreClosure.ratDeg_eq_finrank_mul_interNumRed | (intros; apply GlobalTheory.RatFibreClosure.ratDeg_eq_finrank_mul_interNumRed <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

namespace GlobalTheory.FibreDim

theorem charZero_residueField_genericPoint' (X : Scheme.{0}) [IsIntegral X] (hc : CharZero Γ(X, ⊤)) :
    CharZero (X.residueField (genericPoint X)) := by
  have hg : Function.Injective (X.presheaf.germ ⊤ (genericPoint X) trivial) :=
    germ_injective_of_isIntegral X _ _
  have hr : Function.Injective (X.residue (genericPoint X)) := (X.residue (genericPoint X)).hom.injective
  exact charZero_of_injective_ringHom (f := (X.presheaf.germ ⊤ (genericPoint X) trivial ≫ X.residue _).hom)
    (by simpa using hr.comp hg)

theorem not_charZero_residueField {Z : Scheme.{0}} (p : ℕ) [Fact p.Prime] (s : Z ⟶ Sp (ZMod p)) (z : Z) :
    ¬ CharZero (Z.residueField z) := by
  intro hc
  let φ : ZMod p →+* Z.residueField z :=
    ((Scheme.ΓSpecIso (CommRingCat.of (ZMod p))).inv ≫ s.appTop ≫ Z.Γevaluation z).hom
  have h0 : ((p : ZMod p) : ZMod p) = 0 := ZMod.natCast_self p
  have : (p : Z.residueField z) = 0 := by rw [← map_natCast φ p, h0, map_zero]
  exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) this

end GlobalTheory.FibreDim

namespace GlobalTheory.FibreDim

theorem fibre_isProjOver_and_dim_le : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k), IsArithVar q 1 → ∀ (p : ℕ) [Fact p.Prime], (letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))); IsProjOver (strHom (ZMod p) (pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))))) ∧ topologicalKrullDim ↥(pullback (C := Scheme.{0}) (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))) ≤ 1 := by
  intro k _ W q hq p _
  haveI hgc : IsClosedImmersion (spMap (Int.castRingHom (ZMod p))) :=
    IsClosedImmersion.spec_of_surjective _ (ZMod.ringHom_surjective _)
  refine ⟨?_, ?_⟩
  · letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))
    exact VertProj.isProjOver_strHom_zmod k W q 1 hq _
      (pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))) p
  · set f := q ≫ spMap (Int.castRingHom k)
    set g := spMap (Int.castRingHom (ZMod p))
    have := hq.isIntegral
    have hemb := (pullback.fst f g).isClosedEmbedding
    have hs : IsClosed (Set.range (pullback.fst f g)) := hemb.isClosed_range
    have hne : ∀ z, (pullback.fst f g) z ≠ genericPoint W := by
      intro z hz
      have h1 := charZero_residueField_genericPoint' W hq.charZero
      rw [← hz] at h1
      exact not_charZero_residueField p (pullback.snd f g) z
        (charZero_of_injective_ringHom ((pullback.fst f g).residueFieldMap z).hom.injective)
    have key := topologicalKrullDim_add_one_le hs isClosed_univ (T := W) fun x hx =>
      ⟨genericPoint W, trivial, fun ⟨z, hz⟩ => hne z hz, genericPoint_specializes x⟩
    have hW : topologicalKrullDim (Set.univ : Set W) ≤ 2 := by
      have := topologicalKrullDim_subspace_le W Set.univ
      rw [hq.dim_eq] at this
      exact this
    have heq : topologicalKrullDim (Set.range (pullback.fst f g)) =
        topologicalKrullDim ↥(pullback (C := Scheme.{0}) f g) :=
      GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hemb.isEmbedding rfl
    rw [← heq]
    have h2 := key.trans hW
    generalize topologicalKrullDim (Set.range (pullback.fst f g)) = d at h2 ⊢
    induction d with
    | bot => exact bot_le
    | coe n =>
      norm_cast at h2 ⊢
      induction n with
      | top => exact absurd h2 (by decide)
      | coe m =>
        norm_cast at h2 ⊢
        have h3 : m + 1 ≤ 2 := by exact_mod_cast h2
        omega

end GlobalTheory.FibreDim
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmeticSurface_fibre_isProjOver_zmod_dim_le_one : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k), IsArithVar q 1 → ∀ (p : ℕ) [Fact p.Prime], (letI := GlobalTheory.algebraΓOfHom (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))); IsProjOver (strHom (ZMod p) (pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))))) ∧ topologicalKrullDim ↥(pullback (C := Scheme.{0}) (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))) ≤ 1 := by
  atlas_forward_decl GlobalTheory.FibreDim.fibre_isProjOver_and_dim_le
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_nonneg_of_curveDegree_nonneg_over_zmod : ∀ (p : ℕ) [Fact p.Prime] (V : Scheme.{0}) [Algebra (ZMod p) Γ(V, ⊤)], IsProjOver (strHom (ZMod p) V) → topologicalKrullDim V ≤ 1 → ∀ N : LB V, N.IsLB → (∀ (Z : Scheme.{0}) (i : Z ⟶ V) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod p) Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod p) (N.pull i) 1) → 0 ≤ degOfRank (ZMod p) (toMod N) 1 := by
  first | exact @GlobalTheory.CurveDevissage.degOfRank_nonneg | exact GlobalTheory.CurveDevissage.degOfRank_nonneg | (intros; apply GlobalTheory.CurveDevissage.degOfRank_nonneg <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curveDegree_nonneg_zmodFibre_of_nefOnFiniteFieldFibres : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k) (L : HermLB q) (p : ℕ) [Fact p.Prime], ArInt.NefFib L → ∀ (Z : Scheme.{0}) (i : Z ⟶ pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))) [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod p) Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod p) ((L.B.pull (pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))).pull i) 1 := by
  first | exact @GlobalTheory.NefFibPrime.topSelf_nonneg_of_nefFib | exact GlobalTheory.NefFibPrime.topSelf_nonneg_of_nefFib | (intros; apply GlobalTheory.NefFibPrime.topSelf_nonneg_of_nefFib <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier
  GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechPic
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

namespace GlobalTheory.NefGeneric

theorem ratDeg_nonneg : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k) (L : HermLB q),
    IsArithVar q 1 → ArInt.NefFib L → 0 ≤ ratDeg q L.B := by
  intro k _ W q L hW hL
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e1, e2⟩ := GlobalTheory.T.eulerChar_lineBundle_fibre_modp_eq_rat_projective k W q 1 hW 2 L.B L.isLB
  obtain ⟨hproj, hdim⟩ := GlobalTheory.T.arithmeticSurface_fibre_isProjOver_zmod_dim_le_one k W q hW 2
  letI := GlobalTheory.algebraΓOfHom
    (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod 2))))
  have h := GlobalTheory.T.degree_nonneg_of_curveDegree_nonneg_over_zmod 2 _ hproj hdim _ (LB.isLB_pull L.isLB _)
    (fun Z i _ _ _ hZ => GlobalTheory.T.curveDegree_nonneg_zmodFibre_of_nefOnFiniteFieldFibres k W q L 2 hL Z i hZ)
  rw [ratDeg, degOfRank, ← e1, ← e2]
  simpa [degOfRank] using h

theorem isNef_model : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (P : TrueGeo.Model Y) (L : HermLB P.p),
    ArInt.NefFib L → IsNef F (L.B.pull P.j) := by
  intro F _ _ Y P L hL
  refine ⟨LB.isLB_pull L.isLB P.j, fun Z hZ => ?_⟩
  obtain ⟨W, w, z, _, hW, hz, hpb⟩ := GlobalTheory.T.complete_curve_arith_model_closure F Y P Z hZ
  have e := GlobalTheory.T.curve_model_rational_degree F Y P Z hZ W w z hW hz hpb L.B L.isLB
  have h0 := ratDeg_nonneg (𝓞 F) W (w ≫ P.p) (L.pull w rfl) hW
    (ArInt.nefFib_pull (𝓞 F) P.X W P.p (w ≫ P.p) P.ar.isProjOver hW.isProjOver w rfl L hL)
  change 0 ≤ ratDeg (w ≫ P.p) (L.B.pull w) at h0
  rw [e] at h0
  have hpos : (0 : ℤ) < (Module.finrank ℚ F : ℤ) := by exact_mod_cast Module.finrank_pos
  exact (mul_nonneg_iff_of_pos_left hpos).mp h0

end GlobalTheory.NefGeneric

theorem GlobalTheory.CovHt.Link.nef_of_semiPos_nefFib : Hypotheses2 → HypothesesH → ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F)
    (Y : Var F) (M : Adl C Y), M.SemiPos → M.NefFib → Y.nef M.D := by
  intro _ _ F _ _ C Y M _ ⟨P, L, k, cf, ⟨_, r, hr, _⟩, hL⟩
  have h := GlobalTheory.NefGeneric.isNef_model F Y P L hL
  exact (Var.nef_nsmul_iff k.pos).1 ((Var.nef_iff_of_toPic_eq _ hr.toPic_eq).2 h)

end
end
