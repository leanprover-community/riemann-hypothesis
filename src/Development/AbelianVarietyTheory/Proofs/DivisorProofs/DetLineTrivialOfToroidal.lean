import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedChartSnc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncToroidalGenericBoundaryOfSncBoundary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralGeometricallyConnectedOpenModuli
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliSchemeAffineFrameCoverTwoEigenParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieDeterminantLineRatioFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricallyIntegralAlgebraicConstantsMemRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomologyWedgeCoordinateNonzero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreComponentClosureOpenIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalGenericFibreAffineFrameCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVarietyCompactifyingConnectedComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonvanishingDetLineSectionOfHorizontal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeterminantLineSectionRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineHolFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigFrameMatch
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H0NeBotOfHorizontalFunction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicOnProjectiveConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlatOfConstMulPeriodDeterminant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonvanishingExtensionNormalCompactificatio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasMarkingTransportOfCmTypeEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasMarkingPreservingTransportOfConjEmbedding

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_geometricallyConnected_open_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : (Xo.XF c).Opens), GeometricallyConnected (U.ι ≫ toF Xo c) → IsIntegral U.toScheme := by
  first | exact @GlobalTheory.DetLine.isIntegral_open_of_geometricallyConnected | exact GlobalTheory.DetLine.isIntegral_open_of_geometricallyConnected | (intros; apply GlobalTheory.DetLine.isIntegral_open_of_geometricallyConnected <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduliScheme_affineFrameCover_two_eigenParts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : (Xo.XF c).Opens) (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → FrameCover Xo.univ.t (toX Xo c) (toF Xo c) U (HermitianCompactForm.chi c τ) D.p D.q := by
  first | exact @GlobalTheory.DetLine.frameCover_univ | exact GlobalTheory.DetLine.frameCover_univ | (intros; apply GlobalTheory.DetLine.frameCover_univ <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieDeterminantLine_ratio_function : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (S X : Scheme.{0}) (t : SAB H S) (π : X ⟶ S) (s : X ⟶ Sp c.F) (τ : E →+* ℂ) (p q : ℕ) (V : X.Opens) (σ σ' : Rule t π p q), FrameCover t π s V (HermitianCompactForm.chi c τ) p q → IsSection t π s V (HermitianCompactForm.chi c τ) σ → NowhereZero t π s V (HermitianCompactForm.chi c τ) σ → IsSection t π s V (HermitianCompactForm.chi c τ) σ' → ∃ f : Γ(X, V), ∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ X) v w, IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w → σ' R x v w = valR x V f * σ R x v w := by
  first | exact @GlobalTheory.detLine_exists_ratio | exact GlobalTheory.detLine_exists_ratio | (intros; apply GlobalTheory.detLine_exists_ratio <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.OneValue

theorem isAlgebraic_of_one_value {F A C : Type} [Field F] [CommRing A] [Nontrivial A] [IsReduced A] [Algebra F A]
    [Algebra.FiniteType F A] [Field C] [IsAlgClosed C] [Algebra F C] (s : A)
    (h : ∀ φ ψ : A →ₐ[F] C, φ s = ψ s) : IsAlgebraic F s := by
  have hJ : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := F)
  have key : ∀ m : Ideal A, m.IsMaximal →
      ∃ φ : A →ₐ[F] C, (∀ a, φ a = 0 → a ∈ m) ∧ IsAlgebraic F (φ s) := by
    intro m hm
    letI := Ideal.Quotient.field m
    have : Module.Finite F (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing F (A ⧸ m)
    let σ : (A ⧸ m) →ₐ[F] C := IsAlgClosed.lift
    refine ⟨σ.comp (Ideal.Quotient.mkₐ F m), fun a ha => ?_, ?_⟩
    · exact Ideal.Quotient.eq_zero_iff_mem.1 (σ.toRingHom.injective (ha.trans (map_zero σ.toRingHom).symm))
    · exact (Algebra.IsAlgebraic.isAlgebraic (R := F) (Ideal.Quotient.mkₐ F m s)).algHom σ
  obtain ⟨m₀, hm₀⟩ := Ideal.exists_maximal A
  obtain ⟨φ₀, -, P, hP, hPs⟩ := key m₀ hm₀
  refine ⟨P, hP, ?_⟩
  have hj : Polynomial.aeval s P ∈ (⊥ : Ideal A).jacobson := by
    refine Ideal.mem_sInf.2 ?_
    rintro m ⟨-, hm⟩
    obtain ⟨φ, hφ, -⟩ := key m hm
    refine hφ _ ?_
    rw [← Polynomial.aeval_algHom_apply, h φ φ₀, hPs]
  rwa [hJ.out (Ideal.isRadical_bot_iff.2 inferInstance), Ideal.mem_bot] at hj

theorem valR_spMap_fromSpec {X : Scheme.{0}} {R : Type} [CommRing R] {U W : X.Opens} (hW : IsAffineOpen W)
    (e : W ≤ U) (φ : Γ(X, W) →+* R) (f : Γ(X, U)) :
    valR (Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec : Sp R ⟶ X) U f = φ (resG X e f) := by
  have h0 : ⊤ ≤ hW.fromSpec ⁻¹ᵁ W := hW.fromSpec_preimage_self.ge
  have h : ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec : Sp R ⟶ X) ⁻¹ᵁ U :=
    fun y _ => e (h0 (Set.mem_univ ((Spec.map (CommRingCat.ofHom φ)) y)))
  unfold valR
  rw [dif_pos h]
  have e1 : (Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec : Sp R ⟶ X).appLE U ⊤ h =
      X.presheaf.map (homOfLE e).op ≫ hW.fromSpec.appLE W ⊤ h0 ≫ (Spec.map (CommRingCat.ofHom φ)).appTop := by
    rw [← Category.assoc, Scheme.Hom.map_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ U ⊤ ⊤ _ le_rfl).symm
  have e2 : hW.fromSpec.appLE W ⊤ h0 = (Scheme.ΓSpecIso Γ(X, W)).inv := by
    rw [Scheme.Hom.appLE, hW.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg (_ ≫ ·) ((Spec Γ(X, W)).presheaf.map_id _)).trans (Category.comp_id _)
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  change ((Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec : Sp R ⟶ X).appLE U ⊤ h ≫
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom f =
    (X.presheaf.map (homOfLE e).op ≫ CommRingCat.ofHom φ).hom f
  rw [e1, e2, Category.assoc, Category.assoc]
  erw [n]
  erw [(Scheme.ΓSpecIso Γ(X, W)).inv_hom_id_assoc]

theorem exists_eq_algX {F : Type} [Field F] {Y : Scheme.{0}} (p : Y ⟶ Sp F) [GeometricallyIntegral p]
    [LocallyOfFiniteType p] (e : F →+* ℂ) (f : Γ(Y, ⊤))
    (h : ∀ y y' : Sp ℂ ⟶ Y, y ≫ p = spMap e → y' ≫ p = spMap e → valR y ⊤ f = valR y' ⊤ f) :
    ∃ a : F, f = algX p ⊤ a := by
  have : IsIntegral Y := GeometricallyIntegral.isIntegral_of_subsingleton p
  obtain ⟨U, hU, hxU, hUV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
    (show genericPoint Y ∈ (⊤ : Y.Opens) from trivial)
  replace hU : IsAffineOpen U := hU
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have hc : (algX p U).FiniteType := by
    have h1 : (p.appLE ⊤ U (fun _ _ => trivial)).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2)
  letI : Algebra F Γ(Y, U) := (algX p U).toAlgebra
  have : Algebra.FiniteType F Γ(Y, U) := hc
  letI : Algebra F ℂ := e.toAlgebra
  have hg : hU.fromSpec ≫ p = Spec.map (CommRingCat.ofHom (algebraMap F Γ(Y, U))) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hU
      (show U ≤ p ⁻¹ᵁ ⊤ from le_top)
    rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have hpt : ∀ φ : Γ(Y, U) →ₐ[F] ℂ,
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hU.fromSpec : Sp ℂ ⟶ Y) ≫ p = spMap e := by
    intro φ
    rw [Category.assoc, hg, ← Spec.map_comp]
    congr 1
    ext a
    exact φ.commutes a
  obtain ⟨P, hP, hPs⟩ := isAlgebraic_of_one_value (F := F) (C := ℂ) (resG Y hUV f) fun φ ψ => by
    have := h _ _ (hpt φ) (hpt ψ)
    rwa [valR_spMap_fromSpec hU hUV, valR_spMap_fromSpec hU hUV] at this
  obtain ⟨a, ha⟩ := GlobalTheory.GeomIntConst.mem_range_constFn F Y p (GlobalTheory.Cartier.fnOf ⊤ trivial f) ⟨P, hP, by
    rw [← GlobalTheory.Cartier.fnOf_comp_algX p U hxU, ← GlobalTheory.Cartier.fnOf_resG hUV hxU, ← Polynomial.hom_eval₂]
    exact (congrArg _ hPs).trans (map_zero _)⟩
  exact ⟨a, (GlobalTheory.Cartier.fnOf_injective ⊤ trivial ha).symm⟩

theorem exists_eq_constFn_of_one_value :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : (Xo.XF c).Opens) (e : c.F →+* ℂ) (f : Γ(Xo.XF c, U)), GeometricallyConnected (U.ι ≫ toF Xo c) → (∀ y y' : Sp ℂ ⟶ Xo.XF c, y ≫ toF Xo c = spMap e → y' ≫ toF Xo c = spMap e → Set.range y ⊆ U → Set.range y' ⊆ U → valR y U f = valR y' U f) → ∃ a : c.F, f = ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn (toF Xo c) U a := by
  intro E _ _ _ H D l Xo c U e f hU h
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
  have : Smooth (toF Xo c) := inferInstanceAs (Smooth (pullback.snd _ _))
  have : GeometricallyIntegral (U.ι ≫ toF Xo c) := GlobalTheory.geometricallyIntegral_of_smooth _
  have hle : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := fun x _ => x.2
  have hval : ∀ y : Sp ℂ ⟶ U.toScheme, valR y ⊤ ((U.ι.appLE U ⊤ hle).hom f) = valR (y ≫ U.ι) U f := by
    intro y
    have h1 : ⊤ ≤ y ⁻¹ᵁ ⊤ := le_top
    have h2 : ⊤ ≤ (y ≫ U.ι) ⁻¹ᵁ U := fun x _ => (y x).2
    unfold valR
    rw [dif_pos h1, dif_pos h2, ← Scheme.Hom.appLE_comp_appLE y U.ι U ⊤ ⊤ hle h1]
    rfl
  have hr : ∀ y : Sp ℂ ⟶ U.toScheme, Set.range (y ≫ U.ι) ⊆ U := by
    rintro y _ ⟨x, rfl⟩
    exact (y x).2
  obtain ⟨a, ha⟩ := exists_eq_algX (U.ι ≫ toF Xo c) e ((U.ι.appLE U ⊤ hle).hom f) fun y y' hy hy' => by
    rw [hval, hval]
    exact h _ _ ((Category.assoc _ _ _).trans hy) ((Category.assoc _ _ _).trans hy') (hr y) (hr y')
  refine ⟨a, ?_⟩
  have hiso : IsIso (U.ι.appLE U ⊤ hle) := by
    rw [Scheme.Opens.ι_appLE]
    have : U.ι ''ᵁ ⊤ = U := U.ι_image_top
    have : IsIso (homOfLE (x := U.ι ''ᵁ ⊤) (y := U) this.le) := ⟨homOfLE this.ge, rfl, rfl⟩
    exact Functor.map_isIso _ (homOfLE (x := U.ι ''ᵁ ⊤) (y := U) U.ι_image_top.le).op
  refine (ConcreteCategory.bijective_of_isIso (U.ι.appLE U ⊤ hle)).1 (ha.trans ?_)
  have := Scheme.Hom.appLE_comp_appLE U.ι (toF Xo c) ⊤ U ⊤ (fun _ _ => trivial) hle
  exact (congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom a)) this).symm

end GlobalTheory.OneValue
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constant_component_function_complexValues : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : (Xo.XF c).Opens) (e : c.F →+* ℂ) (f : Γ(Xo.XF c, U)), GeometricallyConnected (U.ι ≫ toF Xo c) → (∀ y y' : Sp ℂ ⟶ Xo.XF c, y ≫ toF Xo c = spMap e → y' ≫ toF Xo c = spMap e → Set.range y ⊆ U → Set.range y' ⊆ U → valR y U f = valR y' U f) → ∃ a : c.F, f = ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn (toF Xo c) U a := by
  atlas_forward_decl GlobalTheory.OneValue.exists_eq_constFn_of_one_value
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine

theorem exists_isVecs_of_eigBasis {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E}
    {S : Scheme.{0}} {t : SAB H S} {t' : SAB H (Sp ℂ)} {x : Sp ℂ ⟶ S} (m : SABMap t' t x) {g n : ℕ}
    (u : HolUnif t'.G t'.PP.L g) (hd : ∀ v, IsTangent v → ∃! z, u.IsDiff z v)
    (hd' : ∀ z, ∃! v, IsTangent v ∧ u.IsDiff z v) {χ : 𝓞 E →+* ℂ} {v : Fin n → (epsAt x ⟶ t.G)}
    (hv : IsEigBasisAt t.act x χ v) : ∃ V : Fin n → Fin g → ℂ, IsVecs u m.φ v V ∧ LinearIndependent ℂ V := by
  choose v' hv' using fun i => FlatRow.exists_lift m.cart (v i)
  have ix := FlatDegreeCompare.Indep.of_eigBasis (((FlatRow.fibre_iff m.cart hv').2 m.act χ).2 hv)
  choose V hV using fun i => (hd _ (ix.1 i)).exists
  exact ⟨V, fun i => ⟨v' i, hv' i, hV i⟩, FlatDegreeCompare.ArchExists.linearIndependent_of_indep u hd' ix hV⟩

theorem exists_unif_of_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (e : c.F →+* ℂ) (y : Sp ℂ ⟶ Xo.XF c) v w, FrU Xo c U τ e y v w → ∃ (o : Obj D l (baseKA l) (y ≫ toX Xo c ≫ Xo.s)) (m : ObjMap o Xo.univ (y ≫ toX Xo c)) (g : ℕ) (u : HolUnif o.t.G o.t.PP.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (κ : u.Λ → ℂ) (V : Fin D.p → Fin g → ℂ) (W : Fin D.q → Fin g → ℂ), u.IsAH Hm κ ∧ IsVecs u m.toSABMap.φ v V ∧ IsVecs u m.toSABMap.φ w W ∧ LinearIndependent ℂ V ∧ LinearIndependent ℂ W := by
  intro E _ _ _ H D l Xo c U τ e y v w h
  rw [← Category.assoc]
  obtain ⟨t', ⟨n⟩⟩ := exists_sab (y ≫ toX Xo c) Xo.univ.t
  obtain ⟨T, hT, -⟩ := CM.exists_pat_of_obj E H D l _ _ _ _ (ModelCompare.objOfSABMap Xo.univ n)
  obtain rfl : T.t = t' := hT
  obtain ⟨rig, hrig⟩ := T.pol.rigid
  obtain ⟨u, Hm, κ, -, hA, -, hd, hd', -⟩ := thetaUnifAV_all T.pol rig hrig
  obtain ⟨V, hV, iV⟩ := exists_isVecs_of_eigBasis n u hd hd' h.2.2.1
  obtain ⟨W, hW, iW⟩ := exists_isVecs_of_eigBasis n u hd hd' h.2.2.2
  exact ⟨ModelCompare.objOfSABMap Xo.univ n, ModelCompare.objMapOfSABMap Xo.univ n, _, u, Hm, κ, V, W, hA, hV, hW,
    iV, iW⟩

end GlobalTheory.DetLine
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformised_fibre_of_framed_complex_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (e : c.F →+* ℂ) (y : Sp ℂ ⟶ Xo.XF c) v w, FrU Xo c U τ e y v w → ∃ (o : Obj D l (baseKA l) (y ≫ toX Xo c ≫ Xo.s)) (m : ObjMap o Xo.univ (y ≫ toX Xo c)) (g : ℕ) (u : HolUnif o.t.G o.t.PP.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (κ : u.Λ → ℂ) (V : Fin D.p → Fin g → ℂ) (W : Fin D.q → Fin g → ℂ), u.IsAH Hm κ ∧ IsVecs u m.toSABMap.φ v V ∧ IsVecs u m.toSABMap.φ w W ∧ LinearIndependent ℂ V ∧ LinearIndependent ℂ W := by
  first | exact @GlobalTheory.DetLine.exists_unif_of_frame | exact GlobalTheory.DetLine.exists_unif_of_frame | (intros; apply GlobalTheory.DetLine.exists_unif_of_frame <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homologyWedgeCoordinate_nonzero : ∀ (g p q : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (V : Fin p → Fin g → ℂ) (W : Fin q → Fin g → ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (herm Hm z z).re) → (∀ x, ∃ Δ, IsWedgeCoord Hm V W x Δ) ∧ (LinearIndependent ℂ V → LinearIndependent ℂ W → ∃ x Δ, Δ ≠ 0 ∧ IsWedgeCoord Hm V W x Δ) := by
  first | exact @GlobalTheory.DetLine.exists_wedgeCoord | exact GlobalTheory.DetLine.exists_wedgeCoord | (intros; apply GlobalTheory.DetLine.exists_wedgeCoord <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.CptConst

theorem exists_eq_algX {F : Type} [Field F] {X Z : Scheme.{0}} (p : X ⟶ Sp F) [IsIntegral X] [UniversallyClosed p]
    (g : Z ⟶ X) [GeometricallyIntegral (g ≫ p)] (f : Γ(X, ⊤)) : ∃ a : F, f = algX p ⊤ a := by
  have : IsIntegral Z := GeometricallyIntegral.isIntegral_of_subsingleton (g ≫ p)
  have hal : ∀ {W : Scheme.{0}} (q : W ⟶ Sp F),
      algX q ⊤ = ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ q.appTop).hom := by
    intro W q
    have : q.appLE ⊤ ⊤ le_top = q.appTop := q.appLE_eq_app
    rw [← this]
    rfl
  have hint : (algX p ⊤).IsIntegral := by
    rw [hal]
    let G := (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop
    have : G.hom.IsIntegral := by
      apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
      exact isIntegral_appTop_of_universallyClosed p
    exact this
  have hcomp : g.appTop.hom.comp (algX p ⊤) = algX (g ≫ p) ⊤ := by
    rw [hal, hal, Scheme.Hom.comp_appTop]
    rfl
  letI := (isField_of_universallyClosed F p).toField
  let φ : Γ(X, ⊤) →+* Z.functionField := (GlobalTheory.Cartier.fnOf ⊤ trivial).comp g.appTop.hom
  have hφ : φ.comp (algX p ⊤) = GlobalTheory.Cartier.constFn (g ≫ p) := by
    rw [RingHom.comp_assoc, hcomp]
    rfl
  obtain ⟨P, hP, hPf⟩ := hint f
  obtain ⟨a, ha⟩ := GlobalTheory.GeomIntConst.mem_range_constFn F Z (g ≫ p) (φ f) ⟨P, hP.ne_zero, by
    rw [← hφ, ← Polynomial.hom_eval₂, hPf, map_zero]⟩
  refine ⟨a, φ.injective ?_⟩
  rw [← ha, ← hφ]
  rfl

theorem exists_eq_constFn_compactOf :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens) (V : (gen Y).Opens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (gen Y) → IsClosed (U : Set (Xo.XF c)) → GeometricallyConnected (U.ι ≫ toF Xo c) → (V : Set (gen Y)) = compactOf Y U → ∀ f : Γ(gen Y, V), ∃ a : c.F, f = ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn (genStr Y) V a := by
  intro E _ _ _ H D l Xo c O _ β Y U V hn _ hU hV f
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim _
  have : Smooth (toF Xo c) := inferInstanceAs (Smooth (pullback.snd _ _))
  have hgi : GeometricallyIntegral (U.ι ≫ toF Xo c) := GlobalTheory.geometricallyIntegral_of_smooth _
  have : IsIntegral U.toScheme := GeometricallyIntegral.isIntegral_of_subsingleton (U.ι ≫ toF Xo c)
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have : IsReduced (gen Y) := GlobalTheory.IsNormalScheme.isReduced
  have := isProper_genStr Y
  have hUirr : IsIrreducible (U : Set (Xo.XF c)) :=
    isIrreducible_iff_irreducibleSpace.2 (inferInstanceAs (IrreducibleSpace U.toScheme))
  have hirr : IsIrreducible (V : Set (gen Y)) :=
    hV ▸ (hUirr.image _ Y.jQ.continuous.continuousOn).closure
  have : IrreducibleSpace V.toScheme := Subtype.irreducibleSpace hirr
  have : IsIntegral V.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsClosedImmersion V.ι := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι, hV]
    exact isClosed_closure)
  have hr : Set.range (U.ι ≫ Y.jQ) ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι, hV]
    exact subset_closure ⟨x.1, x.2, rfl⟩
  let g : U.toScheme ⟶ V.toScheme := IsOpenImmersion.lift V.ι (U.ι ≫ Y.jQ) hr
  have hg : g ≫ V.ι ≫ genStr Y = U.ι ≫ toF Xo c := by
    rw [IsOpenImmersion.lift_fac_assoc, Category.assoc]
    exact congrArg (U.ι ≫ ·) Y.jQ_over
  have : GeometricallyIntegral (g ≫ V.ι ≫ genStr Y) := hg ▸ hgi
  have hle : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := fun x _ => x.2
  obtain ⟨a, ha⟩ := exists_eq_algX (V.ι ≫ genStr Y) g ((V.ι.appLE V ⊤ hle).hom f)
  refine ⟨a, ?_⟩
  have hiso : IsIso (V.ι.appLE V ⊤ hle) := by
    rw [Scheme.Opens.ι_appLE]
    have : V.ι ''ᵁ ⊤ = V := V.ι_image_top
    have : IsIso (homOfLE (x := V.ι ''ᵁ ⊤) (y := V) this.le) := ⟨homOfLE this.ge, rfl, rfl⟩
    exact Functor.map_isIso _ (homOfLE (x := V.ι ''ᵁ ⊤) (y := V) V.ι_image_top.le).op
  refine (ConcreteCategory.bijective_of_isIso (V.ι.appLE V ⊤ hle)).1 (ha.trans ?_)
  have := Scheme.Hom.appLE_comp_appLE V.ι (genStr Y) ⊤ V ⊤ (fun _ _ => trivial) hle
  exact (congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom a)) this).symm

end GlobalTheory.CptConst
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constant_function_normal_compactification : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens) (V : (gen Y).Opens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (gen Y) → IsClosed (U : Set (Xo.XF c)) → GeometricallyConnected (U.ι ≫ toF Xo c) → (V : Set (gen Y)) = compactOf Y U → ∀ f : Γ(gen Y, V), ∃ a : c.F, f = ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn (genStr Y) V a := by
  atlas_forward_decl GlobalTheory.CptConst.exists_eq_constFn_compactOf
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toroidalGenericFibre_affineFrameCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (V : (gen Y).Opens) (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → FrameCover Y.t (genι Y) (genStr Y) V (HermitianCompactForm.chi c τ) D.p D.q := by
  first | exact @GlobalTheory.DetLine.frameCover_gen | exact GlobalTheory.DetLine.frameCover_gen | (intros; apply GlobalTheory.DetLine.frameCover_gen <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.RankZero

theorem eq_zero_of_half_mem {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [hd : DiscreteTopology Λ]
    (h : ∀ z ∈ Λ, (2⁻¹ : ℝ) • z ∈ Λ) (z : Fin g → ℂ) (hz : z ∈ Λ) : z = 0 := by
  have hn : ∀ n : ℕ, ((2⁻¹ : ℝ) ^ n) • z ∈ Λ := by
    intro n
    induction n with
    | zero => simpa using hz
    | succ n ih => rw [pow_succ', mul_smul]; exact h _ ih
  have ht : Filter.Tendsto (fun n : ℕ => ((2⁻¹ : ℝ) ^ n) • z) Filter.atTop (nhds 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num) (by norm_num)).smul_const z
    simpa using this
  have ht' : Filter.Tendsto (fun n : ℕ => (⟨_, hn n⟩ : Λ)) Filter.atTop (nhds 0) :=
    tendsto_subtype_rng.2 ht
  rw [nhds_discrete, Filter.tendsto_pure] at ht'
  obtain ⟨n, hn'⟩ := ht'.exists
  have h0 : ((2⁻¹ : ℝ) ^ n) • z = 0 := congrArg Subtype.val hn'
  rcases smul_eq_zero.1 h0 with h1 | h1
  · exact absurd h1 (by positivity)
  · exact h1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem subsingleton_lattice (D : Datum H) (hD : D.p + D.q = 0) : Subsingleton D.La := by
  haveI := D.fin
  haveI := D.proj
  by_contra hne
  have hnt : Nontrivial D.La := not_subsingleton_iff_nontrivial.1 hne
  have := (Module.finrank_pos_iff (R := 𝓞 E) (M := D.La)).2 hnt
  rw [D.rank, hD] at this
  exact lt_irrefl _ this

theorem subsingleton_unif {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {s : Sp ℂ ⟶ Sp B}
    (hD : D.p + D.q = 0) (o : Obj D l b s) {g : ℕ} (u : HolUnif o.t.G o.t.PP.L g) :
    Subsingleton (Fin g → ℂ) := by
  haveI := subsingleton_lattice D hD
  obtain ⟨-, I, -⟩ := o.geom ℂ (𝟙 _) (Spec.preimage s).hom (by simp [spMap])
  have h1 : I.ev 2 0 = 1 := (I.ker 2 two_pos 0).2 ⟨0, Subsingleton.elim _ _⟩
  have htor : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ o.t.G, x * x = 1 → x = 1 := by
    intro x hx
    obtain ⟨a, ha⟩ := (I.onto 2 two_pos x).1 (by rw [pow_two]; exact hx)
    rw [Subsingleton.elim a 0, h1] at ha
    exact ha.symm
  haveI := u.discrete
  have hΛ : ∀ z ∈ u.Λ, z = 0 := by
    refine eq_zero_of_half_mem u.Λ (fun z hz => (u.ker _).1 (htor _ ?_))
    rw [← u.ex_add, ← add_smul, u.ker]
    norm_num
    exact hz
  refine subsingleton_of_forall_eq 0 (fun z => ?_)
  have hz : z ∈ Submodule.span ℝ (u.Λ : Set (Fin g → ℂ)) := by rw [u.full]; trivial
  have : Submodule.span ℝ (u.Λ : Set (Fin g → ℂ)) = ⊥ := Submodule.span_eq_bot.2 hΛ
  rwa [this, Submodule.mem_bot] at hz

theorem hasTransport_of_rank_zero (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l)
    (U : Set (Xo.XF c)) (e : c.F →+* ℂ) (hD : D.p + D.q = 0) : HasTransport Xo c U e := by
  intro y y' _ _ _ _ o o' _ _ g g' u u' Hm Hm' κ κ' _ _
  haveI := subsingleton_unif hD o u
  haveI := subsingleton_unif hD o' u'
  haveI : Subsingleton (𝟙_ (Over (Sp ℂ)) ⟶ o'.t.G) := u'.ex_onto.subsingleton
  refine ⟨LinearEquiv.ofSubsingleton _ _, fun z => ?_, fun _ _ _ _ => Subsingleton.elim _ _, fun z w => ?_,
    fun _ _ _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _⟩
  · rw [Subsingleton.elim z 0, map_zero]
    simp
  · rw [Subsingleton.elim z 0, map_zero]
    simp [HermitianCompactForm.herm]

end GlobalTheory.DetLine.RankZero
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasMarkingPreservingTransport_of_rank_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (e : c.F →+* ℂ), D.p + D.q = 0 → HasTransport Xo c U e := by
  atlas_forward_decl GlobalTheory.DetLine.RankZero.hasTransport_of_rank_zero
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_variety_compactifying_connected_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens), SmoothOfRelativeDimension D.dim (genStr Y) → IsClosed (U : Set (Xo.XF c)) → GeometricallyConnected (U.ι ≫ toF Xo c) → ∃ (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y), IsOpenImmersion io ∧ Set.range io = compactOf Y U ∧ io ≫ genStr Y = B.str := by
  first | exact @GlobalTheory.CompactVar.exists_var | exact GlobalTheory.CompactVar.exists_var | (intros; apply GlobalTheory.CompactVar.exists_var <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
open Formalism.L2.Pj

namespace GlobalTheory.DetLine.HorConst

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_matrix {S : Scheme.{0}} {t : SAB H S} {R : Type} [CommRing R] {x : Sp R ⟶ S} {m n : ℕ} (h : m = n)
    {v v' : Fin n → (epsAt x ⟶ t.G)} {u u' : Fin m → (Sp (DualNumber R) ⟶ t.G.left)}
    (hv : ∀ (i : Fin n) (k : Fin m), (i : ℕ) = k → (v i).left = u k)
    (hv' : ∀ (i : Fin n) (k : Fin m), (i : ℕ) = k → (v' i).left = u' k)
    {M : Matrix (Fin m) (Fin m) R} (hM : ∀ i, IsCombAtG t x u (M i) (u' i)) :
    ∃ M' : Matrix (Fin n) (Fin n) R, M'.det = M.det ∧ ∀ i, IsCombAt x (M' i) v (v' i) := by
  subst h
  refine ⟨M, rfl, fun i => (EigParts.comb_iff v _ _).2 ?_⟩
  rw [hv' i i rfl, show (fun i => (v i).left) = u from funext fun i => hv i i rfl]
  exact hM i

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β}

open GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc GlobalTheory.ShFam.CoordUniq in

theorem exists_matrix_det_ne {k : Type} [Field k] {φ : c.F →+* k} {x : Sp k ⟶ Y.X} (f₁ f₂ : EigFrame Y φ x)
    (ρ : E →+* ℂ) : ∃ M : Matrix (Fin (D.mult ρ)) (Fin (D.mult ρ)) k,
      (∀ i, IsCombAtG Y.t x (f₁.v ρ) (M i) (f₂.v ρ i)) ∧ M.det ≠ 0 := by
  obtain ⟨n, xc, hx⟩ := exists_chart Y.t x
  choose e₁ he₁ using fun i => vec_exists hx _ (f₁.tan ρ i)
  choose e₂ he₂ using fun i => vec_exists hx _ (f₂.tan ρ i)
  choose M hM using fun i => (f₁.basis ρ _ (f₂.tan ρ i) (f₂.eig ρ i)).exists
  have hM' : ∀ i, e₂ i = ∑ j, M i j • e₁ j := fun i => by
    have := hM i
    rw [he₂ i, show f₁.v ρ = fun j => vec Y.t x xc (e₁ j) from funext he₁] at this
    exact (comb_iff hx _ _ _).1 this
  have hind : ∀ a : Fin (D.mult ρ) → k, ∑ i, a i • e₂ i = 0 → a = 0 := fun a ha => by
    have hb := f₂.basis ρ _ (vec_tan hx 0) ((vec_eig_iff hx _ _).2 (Submodule.zero_mem _))
    rw [show f₂.v ρ = fun j => vec Y.t _ xc (e₂ j) from funext he₂] at hb
    exact hb.unique ((comb_iff hx _ _ _).2 ha.symm) ((comb_iff hx _ _ _).2 (by simp))
  refine ⟨Matrix.of M, hM, fun h0 => ?_⟩
  obtain ⟨a, ha, ha0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  refine ha (hind a ?_)
  simp only [hM', Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← Finset.sum_smul]
  have : ∑ i, a i * M i j = 0 := congrFun ha0 j
  rw [this, zero_smul]

theorem quot_eq {τ : E →+* ℂ} (hτ : τ (H.rt : E) = H.rt0) {e : c.F →+* ℂ} {h : CxFr Y e → ℂ} (hh : HorFn τ h)
    {V : Set (gen Y)} {σb : RuleY Y} (hσ : SecY Y V τ σb) (a a' : CxFr Y e) (ha : a.1.1 = a'.1.1) (hi : Inner a.1)
    {v w v' w'} (hf : FrY Y V τ e a.1.1 v w) (hm : Match τ a.2 v w) (hf' : FrY Y V τ e a'.1.1 v' w')
    (hm' : Match τ a'.2 v' w') : σb ℂ a.1.1 v w * (h a)⁻¹ = σb ℂ a'.1.1 v' w' * (h a')⁻¹ := by
  obtain ⟨x, f⟩ := a
  obtain ⟨x', f'⟩ := a'
  obtain rfl : x = x' := Subtype.ext ha
  obtain ⟨M, hM, hM0⟩ := exists_matrix_det_ne f f' τ
  obtain ⟨N, hN, -⟩ := exists_matrix_det_ne f f' (conjEmb τ)
  obtain ⟨M', eM, hM'⟩ := exists_matrix (GlobalTheory.Harm.mult_of_mem D hτ) hm.1 hm'.1 hM
  obtain ⟨N', eN, hN'⟩ := exists_matrix (GlobalTheory.Harm.mult_conjEmb_of_mem D hτ) hm.2 hm'.2 hN
  have e₁ := hσ.2 ℂ e x.1 v w v' w' M' N' hf hf' hM' hN'
  have e₂ := hh.2.1 ⟨x, f⟩ ⟨x, f'⟩ M N hi ⟨rfl, hM⟩ ⟨rfl, hN⟩
  have h₁ := hh.1 ⟨x, f⟩ hi
  have h₂ := hh.1 ⟨x, f'⟩ hi
  rw [eM, eN] at e₁
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff h₁ h₂]
  refine mul_right_cancel₀ hM0 ?_
  linear_combination σb ℂ x.1 v w * e₂ + h ⟨x, f⟩ * e₁

open GlobalTheory.CxPts GlobalTheory.ShFam.Hor.Sec in

theorem exists_const_mul_horFn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ) (e : c.F →+* ℂ) (h : CxFr Y e → ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y) (V : Set (gen Y)), IsOpenImmersion io → Set.range io = V → io ≫ genStr Y = B.str → τ (H.rt : E) = H.rt0 → HorFn τ h → ∀ σb : RuleY Y, SecY Y V τ σb → ∃ κ : ℂ, ∀ (a : CxFr Y e) v w, Inner a.1 → FrY Y V τ e a.1.1 v w → Match τ a.2 v w → σb ℂ a.1.1 v w = κ * h a := by
  intro E _ _ _ H D l Xo c O _ β Y τ e h B io V hio hV hstr hτ hh σb hσ
  obtain ⟨W, hW, φ, fr, a, hy, hφ, ha, hv, hf⟩ :=
    GlobalTheory.ShFam.HolFrames.exists_affine_holFrames E H D l Xo c O β Y e B io hio hstr
  choose v₀ w₀ hf₀ hm₀ using fun y => (EigParts.eigFrame_match E H D l Xo c O β Y τ hτ V _ (φ y) _ (hφ y)
    (by rintro _ ⟨z, rfl⟩; rw [← hV, Scheme.Hom.comp_apply]; exact ⟨_, rfl⟩) (fr y)).1
  let s (y : B.X) : Γ(B.X, W y) := σb _ _ (v₀ y) (w₀ y)
  have key (y) (p : GlobalTheory.CxPts B.str e) (hp : p ∈ ptsIn B.str e (W y)) :
      ∃ v w, FrY Y V τ e (a y p).1.1 v w ∧ Match τ (a y p).2 v w ∧ σb ℂ (a y p).1.1 v w = ev B.str e _ (s y) p := by
    have hx : (a y p).1.1 = spMap (evHom hp) ≫ (show Sp Γ(B.X, W y) ⟶ B.X from (hW y).fromSpec) ≫ io := by
      have : spMap (evHom hp) ≫ (show Sp Γ(B.X, W y) ⟶ B.X from (hW y).fromSpec) = p.1 :=
        GlobalTheory.Points.specMap_valMap_fromSpec (hW y) p.1 hp
      rw [ha, ← Category.assoc, this]
    obtain ⟨v, w, h₁, h₂, h₃⟩ := exists_pull (evHom hp) (hf₀ y) hx
    have hj : (evHom hp).comp (φ y) = e :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective (h₁.1.symm.trans (a y p).1.2))
    refine ⟨v, w, by have := h₁; rwa [hj] at this, ⟨fun i k hik => ?_, fun i k hik => ?_⟩, ?_⟩
    · rw [h₂, (hm₀ y).1 i k hik, hv y p hp]
    · rw [h₃, (hm₀ y).2 i k hik, hv y p hp]
    · rw [ev_eq hp]
      exact hσ.1 _ ℂ (evHom hp) (Chart.dualMapR (evHom hp)) _ _ _ _ _ _ v w
        (fun a => by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
        (by ext <;> simp [Chart.dualMapR]) (hf₀ y) h₁ hx h₂ h₃
  have hA : Dense (ptsIn B.str e (io ⁻¹ᵁ (genBd Y).compl)) := by
    refine (GlobalTheory.T.complexPoints_nonempty_dense_variety c.F B e).2 _ ?_
    obtain ⟨_, ⟨z, rfl⟩, hz⟩ := Y.jQ_dense.inter_open_nonempty _ io.isOpenEmbedding.isOpen_range
      (Set.range_nonempty _)
    exact ⟨z, fun hb => hb hz⟩
  let R := AnRead.all B.str e B.dim
  choose u hu he using fun y => exists_extension R io hA (isOpen_ptsIn (W y)) (fun z _ => ha y z) (hf y)
    (h := fun a => (h a)⁻¹) (fun V _ _ _ B a hB ha hi => (hh.2.2.1 V B a hB ha hi).inv fun b hb => hh.1 _ (hi b hb))
    (logGrowth_inv hh.2.2.2)
  let pt (z : GlobalTheory.CxPts B.str e) : B.X := z.1 (IsLocalRing.closedPoint ℂ)
  have hpt (z : GlobalTheory.CxPts B.str e) : z ∈ ptsIn B.str e (W (pt z)) := mem_ptsIn.2 (hy _)
  obtain ⟨q, hq, hqe⟩ := exists_holoOn_of_local (R := R) hA (S := Set.univ)
    (u := fun z => ev B.str e _ (s (pt z)) z * (h (a (pt z) z))⁻¹) fun y _ =>
    ⟨ptsIn B.str e (W (pt y)), fun z => ev B.str e _ (s (pt y)) z * u (pt y) z, isOpen_ptsIn _, hpt y,
      (R.holoOn_ev _ _).mul (hu _), fun z hz => by
        obtain ⟨v, w, h₁, h₂, h₃⟩ := key _ z hz.1
        obtain ⟨v', w', h₁', h₂', h₃'⟩ := key _ z (hpt z)
        have := quot_eq hτ hh hσ _ _ ((ha _ _).trans (ha _ _).symm) ((inner_iff (ha _ z)).2 hz.2) h₁ h₂ h₁' h₂'
        rw [h₃, h₃'] at this
        simp only [he _ hz]
        exact this⟩
  obtain ⟨κ, hκ⟩ := GlobalTheory.ConstFn.holoOn_univ_const c.F B e R q hq
  refine ⟨κ, fun b v w hi hb hm => ?_⟩
  have hr : Set.range b.1.1 ⊆ Set.range io := hV ▸ hb.2.1
  have hl : IsOpenImmersion.lift io b.1.1 hr ≫ io = b.1.1 := IsOpenImmersion.lift_fac _ _ _
  let z : GlobalTheory.CxPts B.str e := ⟨IsOpenImmersion.lift io b.1.1 hr, by rw [← hstr, ← Category.assoc, hl]; exact b.1.2⟩
  obtain ⟨v', w', h₁', h₂', h₃'⟩ := key _ z (hpt z)
  have e₁ := quot_eq hτ hh hσ b _ (hl.symm.trans (ha _ z).symm) hi hb hm h₁' h₂'
  have e₂ := hqe (x := z) ⟨trivial, (inner_iff hl.symm).1 hi⟩
  rw [hκ] at e₂
  rw [h₃'] at e₁
  rw [e₂]
  exact (mul_inv_eq_iff_eq_mul₀ (hh.1 b hi)).1 e₁

end GlobalTheory.DetLine.HorConst
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_const_mul_horizontalDetLieCoordinate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ) (e : c.F →+* ℂ) (h : CxFr Y e → ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y) (V : Set (gen Y)), IsOpenImmersion io → Set.range io = V → io ≫ genStr Y = B.str → τ (H.rt : E) = H.rt0 → HorFn τ h → ∀ σb : RuleY Y, SecY Y V τ σb → ∃ κ : ℂ, ∀ (a : CxFr Y e) v w, Inner a.1 → FrY Y V τ e a.1.1 v w → Match τ a.2 v w → σb ℂ a.1.1 v w = κ * h a := by
  atlas_forward_decl GlobalTheory.DetLine.HorConst.exists_const_mul_horFn
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasMarkingPreservingTransport_of_conj_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (e : c.F →+* ℂ), HasTransport Xo c U ((starRingEnd ℂ).comp e) → HasTransport Xo c U e := by
  first | exact @GlobalTheory.hasTransport_of_conj | exact GlobalTheory.hasTransport_of_conj | (intros; apply GlobalTheory.hasTransport_of_conj <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm
open GlobalTheory.ArchMetricCompare GlobalTheory.ConjUnif GlobalTheory.ConjTransport GlobalTheory.DetLine

namespace GlobalTheory.ConjFlat

theorem isTangent_of_fibre {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp ℂ ⟶ S} {A : Over (Sp ℂ)} [GrpObj A]
    {ψ : A.left ⟶ G.left} (h : IsGrpPullback A G y ψ) {t : epsR ℂ ⟶ A}
    (ht : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ t.left ≫ ψ = (1 : Over.mk y ⟶ G).left) : IsTangent t := by
  refine h.1.hom_ext ?_ ?_
  · refine ((Category.assoc _ _ _).trans ht).trans ?_
    refine Eq.trans ?_ (PolBaseChange.eSec_comm h).symm
    rw [Hom.one_def]
    simp [eSec]
  · have z := congrArg (· ≫ A.hom) (isTangent_zero A)
    rw [← z, Category.assoc, Category.assoc, Over.w, Over.w]

theorem isVecs_conj {S : Scheme.{0}} {G : Over S} [GrpObj G] {y y₁ : Sp ℂ ⟶ S} {A A₁ : Over (Sp ℂ)} [GrpObj A]
    [GrpObj A₁] {L : LB A.left} {L₁ : LB A₁.left} {ψ : A.left ⟶ G.left} (h : IsGrpPullback A G y ψ)
    {ρ : A₁.left ⟶ A.left} (hρ : IsGrpPullback A₁ A cj ρ) {ψ₁ : A₁.left ⟶ G.left} (hψ : ψ₁ = ρ ≫ ψ) {g n : ℕ}
    {u : HolUnif A L g} {u₁ : HolUnif A₁ L₁ g} (hx : ∀ z, u₁.ex z = cjPt hρ (u.ex (star z)))
    {v : Fin n → (epsAt y ⟶ G)} {v₁ : Fin n → (epsAt y₁ ⟶ G)}
    (hv : ∀ i, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (v i).left = (1 : Over.mk y ⟶ G).left)
    (h₁ : ∀ i, (v₁ i).left = spMap (Chart.dualMapR (starRingEnd ℂ)) ≫ (v i).left) {V : Fin n → Fin g → ℂ}
    (hV : IsVecs u ψ v V) : IsVecs u₁ ψ₁ v₁ fun i => star (V i) := by
  intro i
  obtain ⟨t, ht, hd⟩ := hV i
  have tg : IsTangent t := isTangent_of_fibre h (by rw [ht]; exact hv i)
  have w : (spMap (Chart.dualMapR (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left)) ≫ A.hom =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ cj := by
    rw [Category.assoc, show (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ A.hom =
      spMap (algebraMap ℂ (DualNumber ℂ)) from Over.w t, ← DetExtendZero.spMap_comp, ← DetExtendZero.spMap_comp]
    refine congrArg spMap (RingHom.ext fun a => ?_)
    ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  let t₁ : epsR ℂ ⟶ A₁ := Over.homMk (hρ.1.lift _ _ w) (hρ.1.lift_snd _ _ _)
  have e : t₁.left ≫ ρ = spMap (Chart.dualMapR (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) :=
    hρ.1.lift_fst _ _ _
  refine ⟨t₁, ?_, ?_⟩
  · rw [hψ, ← Category.assoc, e, h₁, ← ht]
    exact Category.assoc _ _ _
  · have := cj_isDiff hρ (pullId u) tg e hd
    intro U hU f
    simp only [hx]
    exact this U hU f

theorem herm_conj {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    herm (Hm.map star) (star z) (star w) = star (herm Hm z w) := by
  rw [herm, herm, ← star_form, star_star, star_star]

theorem isWedgeCoord_conj {g p q : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} {V : Fin p → Fin g → ℂ} {W : Fin q → Fin g → ℂ}
    {x : Fin q ⊕ Fin p → Fin g → ℂ} {Δ : ℂ} (h : IsWedgeCoord Hm V W x Δ) :
    IsWedgeCoord (Hm.map star) (fun i => star (V i)) (fun j => star (W j)) (fun k => star (x k)) (star Δ) := by
  obtain ⟨a, ha, rfl⟩ := h
  refine ⟨fun k i => star (a k i), fun k i => ?_, ?_⟩
  · have e : star (x k) - ∑ m, star (a k m) • star (V m) = star (x k - ∑ m, a k m • V m) := by
      simp [star_sum]
    rw [e, herm_conj, ha, star_zero]
  · refine ((starRingEnd ℂ).map_det _).trans (congrArg Matrix.det ?_)
    ext k (j | i)
    · simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Sum.elim_inl, herm_conj]
      simp
    · simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}

theorem isTransport_to_conj {B : Type} [CommRing B] {b : Base l B} {s s₁ s' s₁' : Sp ℂ ⟶ Sp B} {o : Obj D l b s}
    {o₁ : Obj D l b s₁} {o' : Obj D l b s'} {o₁' : Obj D l b s₁'}
    (m : ObjMap o₁ o cj) (m' : ObjMap o₁' o' cj) {g g' : ℕ}
    {u : HolUnif o.t.G o.t.PP.L g} {u' : HolUnif o'.t.G o'.t.PP.L g'}
    {u₁ : HolUnif o₁.t.G o₁.t.PP.L g} {u₁' : HolUnif o₁'.t.G o₁'.t.PP.L g'}
    {Hm : Matrix (Fin g) (Fin g) ℂ} {Hm' : Matrix (Fin g') (Fin g') ℂ}
    (hΛ : ∀ z, z ∈ u₁.Λ ↔ star z ∈ u.Λ) (hx : ∀ z, u₁.ex z = cjPt m.cart (u.ex (star z)))
    (hΛ' : ∀ z, z ∈ u₁'.Λ ↔ star z ∈ u'.Λ) (hx' : ∀ z, u₁'.ex z = cjPt m'.cart (u'.ex (star z)))
    {φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g' → ℂ)} (h : IsTransport o o' u u' Hm Hm' φ) :
    IsTransport o₁ o₁' u₁ u₁' (Hm.map star) (Hm'.map star) ((conjEquiv g).trans (φ.trans (conjEquiv g'))) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e : ∀ z, ((conjEquiv g).trans (φ.trans (conjEquiv g'))) z = star (φ (star z)) := fun _ => rfl
  refine ⟨fun z => ?_, fun a z w hw => ?_, fun z w => ?_, fun a z hz => ?_, fun a z hz => ?_⟩
  · rw [e, hΛ', star_star, h1, hΛ]
  · rw [hx, hx, ← cjPt_act] at hw
    rw [e, e, hx', hx', star_star, star_star, ← cjPt_act, h2 a _ _ (cjPt_injective m.cart hw)]
  · rw [e, e, herm_map_star, herm_map_star, star_star, star_star, h3]
  · rw [hx, ← cjPt_eta m] at hz
    rw [e, hx', star_star, h4 a _ (cjPt_injective m.cart hz), cjPt_eta]
  · rw [hx, ← cjPt_etaA m] at hz
    rw [e, hx', star_star, h5 a _ (cjPt_injective m.cart hz), cjPt_etaA]

theorem exists_conj_fibre (Xo : Moduli D l) (c : Coeff l) (y : Sp ℂ ⟶ Xo.XF c)
    (o : Obj D l (baseKA l) (y ≫ toX Xo c ≫ Xo.s)) (n : ObjMap o Xo.univ (y ≫ toX Xo c)) :
    ∃ (o₁ : Obj D l (baseKA l) ((cj ≫ y) ≫ toX Xo c ≫ Xo.s)) (m : ObjMap o₁ o cj)
      (k : ObjMap o₁ Xo.univ ((cj ≫ y) ≫ toX Xo c)), k.toSABMap.φ = m.toSABMap.φ ≫ n.toSABMap.φ := by
  obtain ⟨o₁, ⟨m⟩, -⟩ := exists_conj_obj Xo c y o n
  refine ⟨o₁, m, ?_⟩
  have a : ∀ f : Sp ℂ ⟶ Xo.X, f = cj ≫ y ≫ toX Xo c →
      ∃ k : ObjMap o₁ Xo.univ f, k.toSABMap.φ = m.toSABMap.φ ≫ n.toSABMap.φ := by
    rintro _ rfl
    exact ObjComp.objMap_comp n m
  exact a _ (Category.assoc _ _ _)

end GlobalTheory.ConjFlat

namespace GlobalTheory

open ConjFlat

theorem isFlatAt_of_conj (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σ : RuleU Xo c)
    (e : c.F →+* ℂ) (hσ : SecU Xo c U τ σ) (h : IsFlatAt Xo c U τ σ ((starRingEnd ℂ).comp e)) :
    IsFlatAt Xo c U τ σ e := by
  intro y y' v w v' w' hf hf' o o' n n' g g' u u' Hm Hm' κ κ' φ V W V' W' x Δ Δ' hA hA' hφ hV hW hV' hW' hΔ hΔ'
  obtain ⟨o₁, m, k, hk⟩ := exists_conj_fibre Xo c y o n
  obtain ⟨o₁', m', k', hk'⟩ := exists_conj_fibre Xo c y' o' n'
  obtain ⟨u₁, κ₁, hA₁, hΛ, hx⟩ := exists_unif m u hA
  obtain ⟨u₁', κ₁', hA₁', hΛ', hx'⟩ := exists_unif m' u' hA'
  obtain ⟨v₁, w₁, hf₁, a, b⟩ := exists_pull (starRingEnd ℂ) hf (x' := cj ≫ y) rfl
  obtain ⟨v₁', w₁', hf₁', a', b'⟩ := exists_pull (starRingEnd ℂ) hf' (x' := cj ≫ y') rfl
  have i1 : ∀ z : ℂ, Chart.dualMapR (starRingEnd ℂ) (algebraMap ℂ _ z) = algebraMap ℂ _ (starRingEnd ℂ z) :=
    fun z => by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have i2 : Chart.dualMapR (starRingEnd ℂ) DualNumber.eps = DualNumber.eps := by ext <;> simp [Chart.dualMapR]
  have s := hσ.1 ℂ ℂ _ _ _ _ _ _ v w v₁ w₁ i1 i2 hf hf₁ rfl a b
  have s' := hσ.1 ℂ ℂ _ _ _ _ _ _ v' w' v₁' w₁' i1 i2 hf' hf₁' rfl a' b'
  have q := h (cj ≫ y) (cj ≫ y') v₁ w₁ v₁' w₁' hf₁ hf₁' o₁ o₁' k k' g g' u₁ u₁' _ _ κ₁ κ₁' _ _ _ _ _
    (fun i => star (x i)) (star Δ) (star Δ') hA₁ hA₁' (isTransport_to_conj m m' hΛ hx hΛ' hx' hφ)
    (isVecs_conj n.cart m.cart hk hx (fun i => (hf.2.2.1.1 i).1) a hV)
    (isVecs_conj n.cart m.cart hk hx (fun i => (hf.2.2.2.1 i).1) b hW)
    (isVecs_conj n'.cart m'.cart hk' hx' (fun i => (hf'.2.2.1.1 i).1) a' hV')
    (isVecs_conj n'.cart m'.cart hk' hx' (fun i => (hf'.2.2.2.1 i).1) b' hW')
    (isWedgeCoord_conj hΔ) (by
      have := isWedgeCoord_conj hΔ'
      simpa only [LinearEquiv.trans_apply, conjEquiv_apply, star_star] using this)
  rw [s, s'] at q
  refine (starRingEnd ℂ).injective ?_
  rw [map_mul, map_mul]
  exact q

end GlobalTheory
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHorizontalLieDeterminantSection_of_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σ : RuleU Xo c) (e : c.F →+* ℂ), SecU Xo c U τ σ → IsFlatAt Xo c U τ σ ((starRingEnd ℂ).comp e) → IsFlatAt Xo c U τ σ e := by
  first | exact @GlobalTheory.isFlatAt_of_conj | exact GlobalTheory.isFlatAt_of_conj | (intros; apply GlobalTheory.isFlatAt_of_conj <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor

namespace GlobalTheory.DetLine

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}

theorem good_or (c : Coeff l) (e : c.F →+* ℂ) :
    Formalism.L2.PjFree.GoodEmb c e ∨ Formalism.L2.PjFree.GoodEmb c ((starRingEnd ℂ).comp e) := by
  set z := (e.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ with hz
  have h1 : z ^ 2 = H.rt0 ^ 2 := by rw [hz, ← map_pow, (baseKA l).ρ_sq, H.sqrt_neg_disc_sq]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exact .inl h
  · refine .inr (show starRingEnd ℂ z = H.rt0 from ?_)
    have h4 := H.sqrt_neg_disc_sq
    have h5 := congrArg Complex.im h4
    have h6 := congrArg Complex.re h4
    have h7 : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
    simp [pow_two] at h5 h6
    have h8 : H.rt0.re = 0 := by
      by_contra h0
      have : H.rt0.im = 0 := by
        have : H.rt0.re * H.rt0.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left h0
      rw [this] at h6
      nlinarith [mul_self_nonneg H.rt0.re]
    rw [h]
    exact Complex.ext (by simp [h8]) (by simp)

section Unique

variable {S X : Scheme.{0}} {c : Coeff l} {t : SAB H S} {π : X ⟶ S} {s : X ⟶ Sp c.F} {τ : E →+* ℂ} {p q : ℕ}

theorem existsUnique_multiple {V : X.Opens} (hne : (V : Set X).Nonempty)
    (hc : FrameCover t π s V (HermitianCompactForm.chi c τ) p q) {σ σ' : Rule t π p q} (hz : NowhereZero t π s V (HermitianCompactForm.chi c τ) σ)
    (a : c.F) (h : ∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ X) v w,
      IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w → σ' R x v w = valR x V (Geo.Tor.constFn s V a) * σ R x v w) :
    ∃! a : c.F, IsMultiple t π s V (HermitianCompactForm.chi c τ) σ' a σ := by
  have h1 : IsMultiple t π s V (HermitianCompactForm.chi c τ) σ' a σ := fun R _ j x v w hf => by
    rw [h R j x v w hf, GlobalTheory.Points.valR_constFn_of_over s j x hf.1 V (fun z _ => hf.2.1 ⟨z, rfl⟩)]
  refine ⟨a, h1, fun b hb => ?_⟩
  obtain ⟨z, hzV⟩ := hne
  obtain ⟨W, hW, j, v, w, hzW, hf⟩ := hc z hzV
  have : Nonempty W := ⟨⟨z, hzW⟩⟩
  have : Nontrivial Γ(X, W) := Scheme.component_nontrivial X W
  exact j.injective ((hz _ j _ v w hf).mul_right_cancel ((hb _ j _ v w hf).symm.trans (h1 _ j _ v w hf)))

end Unique

variable {Xo : Moduli D l} {c : Coeff l}

theorem nonempty_of_geomConn {U : (Xo.XF c).Opens} (hG : GeometricallyConnected (U.ι ≫ toF Xo c)) :
    (U : Set (Xo.XF c)).Nonempty := by
  have := GlobalTheory.T.isIntegral_geometricallyConnected_open_moduli E H D l Xo c U hG
  exact ⟨_, (genericPoint U.toScheme).2⟩

theorem flat_unique {U : (Xo.XF c).Opens} (hG : GeometricallyConnected (U.ι ≫ toF Xo c)) {τ : E →+* ℂ}
    (hτ : τ (H.rt : E) = H.rt0) (e : c.F →+* ℂ) (hT : HasTransport Xo c U e) {σ σ' : RuleU Xo c}
    (hs : SecU Xo c U τ σ) (hz : NzU Xo c U τ σ) (hf : IsFlatAt Xo c U τ σ e) (hs' : SecU Xo c U τ σ')
    (hf' : IsFlatAt Xo c U τ σ' e) :
    ∃! a : c.F, IsMultiple Xo.univ.t (toX Xo c) (toF Xo c) U (HermitianCompactForm.chi c τ) σ' a σ := by
  have hc := GlobalTheory.T.moduliScheme_affineFrameCover_two_eigenParts E H D l Xo c U τ hτ
  obtain ⟨f, hr⟩ := GlobalTheory.T.exists_lieDeterminantLine_ratio_function E H l c _ _ _ _ _ τ _ _ U σ σ' hc hs hz hs'
  have fr : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ toF Xo c = spMap e → Set.range y ⊆ U → ∃ v w, FrU Xo c U τ e y v w :=
    fun y hy hU => by
      obtain ⟨W, hW, j, v, w, hzW, h⟩ := hc _ (hU ⟨IsLocalRing.closedPoint ℂ, rfl⟩)
      have hle : ⊤ ≤ y ⁻¹ᵁ W := (GlobalTheory.Points.le_preimage_iff y W).2 hzW
      have hy' := (GlobalTheory.Points.specMap_valMap_fromSpec hW y hle).symm
      obtain ⟨v', w', h', -⟩ := exists_pull (GlobalTheory.Points.valMap y W hle).hom h hy'
      obtain rfl : e = (GlobalTheory.Points.valMap y W hle).hom.comp j :=
        congrArg CommRingCat.Hom.hom (Spec.map_injective (hy.symm.trans h'.1))
      exact ⟨v', w', h'⟩
  obtain ⟨a, rfl⟩ := GlobalTheory.T.exists_constant_component_function_complexValues E H D l Xo c U e f hG fun y y' hy hy' hU hU' => by
    obtain ⟨v, w, h⟩ := fr y hy hU
    obtain ⟨v', w', h'⟩ := fr y' hy' hU'
    obtain ⟨o, m, g, u, Hm, κ, V, W, hA, hV, hW, iV, iW⟩ := GlobalTheory.T.exists_uniformised_fibre_of_framed_complex_point E H D l Xo c U τ e y v w h
    obtain ⟨o', m', g', u', Hm', κ', V', W', hA', hV', hW', -⟩ := GlobalTheory.T.exists_uniformised_fibre_of_framed_complex_point E H D l Xo c U τ e y' v' w' h'
    obtain ⟨φ, hφ⟩ := hT y y' hy hy' hU hU' o o' ⟨m⟩ ⟨m'⟩ g g' u u' Hm Hm' κ κ' hA hA'
    obtain ⟨x, Δ, hΔ, hx⟩ := (GlobalTheory.T.exists_homologyWedgeCoordinate_nonzero g _ _ Hm V W hA.1 hA.2.1).2 iV iW
    obtain ⟨Δ', hx'⟩ := (GlobalTheory.T.exists_homologyWedgeCoordinate_nonzero g' _ _ Hm' V' W' hA'.1 hA'.2.1).1 fun k => φ (x k)
    have e1 := hf y y' v w v' w' h h' o o' m m' g g' u u' Hm Hm' κ κ' φ V W V' W' x Δ Δ' hA hA' hφ hV hW hV' hW' hx hx'
    have e2 := hf' y y' v w v' w' h h' o o' m m' g g' u u' Hm Hm' κ κ' φ V W V' W' x Δ Δ' hA hA' hφ hV hW hV' hW' hx hx'
    rw [hr ℂ e y v w h, hr ℂ e y' v' w' h', _root_.mul_assoc, _root_.mul_assoc, e1] at e2
    exact mul_right_cancel₀ (mul_ne_zero (hz ℂ e y' v' w' h').ne_zero hΔ) e2
  exact existsUnique_multiple (nonempty_of_geomConn hG) hc hz a hr

theorem cpt_unique {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {U : (Xo.XF c).Opens}
    (hN : Geo.Tor.IsNormalScheme (gen Y)) (hU : IsClosed (U : Set (Xo.XF c)))
    (hG : GeometricallyConnected (U.ι ≫ toF Xo c)) {τ : E →+* ℂ} (hτ : τ (H.rt : E) = H.rt0) {σ σ' : RuleY Y}
    (hs : SecY Y (compactOf Y U) τ σ) (hz : NzY Y (compactOf Y U) τ σ) (hs' : SecY Y (compactOf Y U) τ σ') :
    ∃! a : c.F, IsMultiple Y.t (genι Y) (genStr Y) (compactOf Y U) (HermitianCompactForm.chi c τ) σ' a σ := by
  obtain ⟨V, hV, -⟩ := GlobalTheory.T.genericFibre_componentClosure_open_isIntegral E H D l Xo c O β Y U hN hU hG
  have hne : (V : Set (gen Y)).Nonempty := hV ▸ ((nonempty_of_geomConn hG).image _).closure
  have hk := GlobalTheory.T.exists_constant_function_normal_compactification E H D l Xo c O β Y U V hN hU hG hV
  rw [← hV] at hs hz hs' ⊢
  have hc := GlobalTheory.T.toroidalGenericFibre_affineFrameCover E H D l Xo c O β Y V τ hτ
  obtain ⟨f, hr⟩ := GlobalTheory.T.exists_lieDeterminantLine_ratio_function E H l c _ _ _ _ _ τ _ _ V σ σ' hc hs hz hs'
  obtain ⟨a, rfl⟩ := hk f
  exact existsUnique_multiple hne hc hz a hr

def HasFlatSection (Xo : Moduli D l) (c : Coeff l) (U : (Xo.XF c).Opens) (τ : E →+* ℂ) : Prop :=
  (∀ e : c.F →+* ℂ, HasTransport Xo c U e) ∧ ∃ σ : RuleU Xo c, SecU Xo c U τ σ ∧ NzU Xo c U τ σ ∧
    (∀ e : c.F →+* ℂ, IsFlatAt Xo c U τ σ e) ∧
    ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), Geo.Tor.IsNormalScheme (gen Y) →
      ∃ σb : RuleY Y, SecY Y (compactOf Y U) τ σb ∧ NzY Y (compactOf Y U) τ σb ∧ Restricts Y U τ σb σ

theorem exists_of_rank_zero (U : (Xo.XF c).Opens) (τ : E →+* ℂ) (h : D.p + D.q = 0) : HasFlatSection Xo c U τ := by
  have : IsEmpty (Fin D.p) := ⟨fun i => by have := i.2; omega⟩
  have : IsEmpty (Fin D.q) := ⟨fun i => by have := i.2; omega⟩
  refine ⟨fun e => GlobalTheory.T.hasMarkingPreservingTransport_of_rank_zero E H D l Xo c U e h, fun _ _ _ _ _ => 1,
    isSection_of_chg fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by simp [Matrix.det_isEmpty],
    fun _ _ _ _ _ _ _ => isUnit_one, fun e => ?_, fun O _ β Y _ => ⟨fun _ _ _ _ _ => 1,
    isSection_of_chg fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => by simp [Matrix.det_isEmpty],
    fun _ _ _ _ _ _ _ => isUnit_one, fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩⟩
  intro y y' v w v' w' _ _ o o' m m' g g' u u' Hm Hm' κ κ' φ V W V' W' x Δ Δ' _ _ _ _ _ _ _ ⟨a, _, ha⟩ ⟨a', _, ha'⟩
  rw [ha, ha', Matrix.det_isEmpty, Matrix.det_isEmpty]

theorem exists_of_snc {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β)
    (hsm : SmoothOfRelativeDimension D.dim (genStr Z)) (hsnc : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Z))
    {U : (Xo.XF c).Opens} (hU : IsClosed (U : Set (Xo.XF c))) (hG : GeometricallyConnected (U.ι ≫ toF Xo c))
    {τ : E →+* ℂ} (hτ : τ (H.rt : E) = H.rt0) (hr : 1 ≤ D.p + D.q) : HasFlatSection Xo c U τ := by
  obtain ⟨B, io, h1, h2, h3⟩ := GlobalTheory.T.exists_variety_compactifying_connected_component E H D l Xo c O β Z U hsm hU hG
  have fam : ∀ e : c.F →+* ℂ, Formalism.L2.PjFree.GoodEmb c e → ∃ (g : ℕ) (en : Fin g ≃ Pad.Letter D) (Fu : Fam Xo c e en)
      (x : ∀ i, Idx D τ → (Fu.Di i).La) (hm : Fin Fu.n → Matrix (Idx D τ) (Idx D τ) E),
      ∀ i, IsPerBasis (Fu.Di i) (x i) (hm i) := fun e he => by
    let en : Fin (Fintype.card (Pad.Letter D)) ≃ Pad.Letter D := (Fintype.equivFin _).symm
    obtain ⟨Fu⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H D l Xo (e.comp (IntermediateField.inclusion c.le).toRingHom) _
      (fun j => Formalism.L2.PjFree.relab c e (en j).1) hr he ((GlobalTheory.Relab.relab_good E H l c e he).2.2.2 D _ en)
    choose x hm hx using fun i : Fin Fu.n => GlobalTheory.T.exists_hermitianPeriodLatticeBasis_same_signature _ H D (Fu.Di i) τ (Fu.sig i)
    exact ⟨_, en, Fu, x, hm, hx⟩
  obtain ⟨e₀, he₀⟩ : ∃ e₀, Formalism.L2.PjFree.GoodEmb c e₀ := (good_or c c.F.val.toRingHom).elim (⟨_, ·⟩) (⟨_, ·⟩)
  obtain ⟨g₀, en₀, Fu₀, x₀, hm₀, hx₀⟩ := fam e₀ he₀
  obtain ⟨σZ, hsZ, hzZ⟩ := GlobalTheory.T.exists_nonvanishing_detLine_section_of_horizontal E H D l Xo c O β Z τ e₀ _ B io _ h1 h2 h3 hτ (horFn_horOf_snc hsm hsnc he₀ hr hx₀)
  obtain ⟨σ, hs, hres, hz⟩ := GlobalTheory.T.exists_determinantLine_section_restriction E H D l Xo c O β Z U τ σZ hsZ
  have hflat : ∀ e, Formalism.L2.PjFree.GoodEmb c e → IsFlatAt Xo c U τ σ e := fun e he => by
    obtain ⟨g, en, Fu, x, hm, hx⟩ := fam e he
    obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_const_mul_horizontalDetLieCoordinate E H D l Xo c O β Z τ e _ B io _ h1 h2 h3 hτ (horFn_horOf_snc hsm hsnc he hr hx) σZ hsZ
    refine GlobalTheory.T.isFlat_of_const_mul_periodDeterminant E H D l Xo c O β Z U τ e g en Fu x hm σZ σ κ B io hU h1 h2 h3 hτ hx hres
      fun a v w i Q hP hf hM => ?_
    rw [← horOf_eq_perVal hx a i Q hP]
    refine hκ a v w ?_ hf hM
    obtain ⟨P, W, y, -, -, hy, -⟩ := hP
    exact fun h => h ⟨y (IsLocalRing.closedPoint ℂ), by rw [← hy]; exact (Scheme.Hom.comp_apply _ _ _).symm⟩
  refine ⟨fun e => ?_, σ, hs, hz hzZ, fun e => ?_, fun O' _ β' Y hN =>
    GlobalTheory.T.exists_nonvanishing_extension_normal_compactification E H D l Xo c O' β' Y O β Z U τ σZ σ hN hU hG hτ hsZ hzZ hs hres⟩
  · rcases good_or c e with he | he
    · exact GlobalTheory.T.hasMarkingTransport_of_cmType_embedding E H D l Xo c O β Z U e B io hU h1 h2 h3 hr he
    · exact GlobalTheory.T.hasMarkingPreservingTransport_of_conj_embedding E H D l Xo c U e (GlobalTheory.T.hasMarkingTransport_of_cmType_embedding E H D l Xo c O β Z U _ B io hU h1 h2 h3 hr he)
  · rcases good_or c e with he | he
    · exact hflat e he
    · exact GlobalTheory.T.isHorizontalLieDeterminantSection_of_conj E H D l Xo c U τ σ e hs (hflat _ he)

theorem detLineTrivial_of_toroidal (hT : GlobalTheory.Published.ToroidalCompactification) : DetLineTrivial := by
  intro E _ _ _ H D l Xo c U hU hG τ hτ
  have hex : HasFlatSection Xo c U τ := by
    rcases Nat.eq_zero_or_pos (D.p + D.q) with h | h
    · exact exists_of_rank_zero U τ h
    · obtain ⟨Z, hsm, hsnc, -⟩ := hT E H D h l Xo c
      exact exists_of_snc Z
        ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hsm)
        (GlobalTheory.VarFlag.snc_genBdIdeal_of_snc_boundary hsnc) hU hG hτ h
  obtain ⟨htr, σ, hs, hz, hf, hY⟩ := hex
  refine ⟨htr, σ, hs, hz, hf, fun σ' hs' hf' => ?_, fun O _ β Y hN => ?_⟩
  · exact flat_unique hG hτ c.F.val.toRingHom (htr _) hs hz (hf _) hs' (hf' _)
  · obtain ⟨σb, h1, h2, h3⟩ := hY O β Y hN
    exact ⟨σb, h1, h2, h3, fun σ' h' => cpt_unique Y hN hU hG hτ h1 h2 h'⟩

end GlobalTheory.DetLine
end
end
