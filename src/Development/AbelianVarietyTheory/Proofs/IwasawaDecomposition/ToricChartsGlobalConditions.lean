import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHenselRootResidueStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialApproxPowMaximalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialApproxUniquenessStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HenselRootsCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonomialFormOnChartRing

section
section
open IsLocalRing GlobalTheory.LN Polynomial IntermediateField

namespace GlobalTheory

theorem exists_cDvr_residue_lift : ∀ {A : Type} [CommRing A] [IsLocalRing A] {L : Type} [Field L] (φ : ResidueField A →+* L), φ.Finite → CharZero (ResidueField A) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (α : A →+* W), IsLocalHom α → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : W →+* V), CDvr V ∧ Function.Injective f ∧ IsLocalHom f ∧ ∃ σ : L →+* ResidueField V, ∀ a : A, σ (φ (residue A a)) = residue V (f (α a)) := by
  intro A _ _ L _ φ hφ hK W _ _ _ hW α hα
  obtain ⟨hd, hc, h0⟩ := (cDvr_iff W).1 hW
  let K := ResidueField A
  letI : Algebra K L := φ.toAlgebra
  haveI : FiniteDimensional K L := hφ
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element K L
  have hθi : IsIntegral K θ := .of_finite K θ
  let β : K →+* ResidueField W := ResidueField.map α
  obtain ⟨q, hq1, hq2, hq3⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.map_surjective (residue W) residue_surjective ((minpoly K θ).map β)) ((minpoly.monic hθi).map β)
  let F := FractionRing W
  haveI : CharZero F := IsFractionRing.charZero_of_isFractionRing W
  let M := (q.map (algebraMap W F)).SplittingField
  haveI : FaithfulSMul W M := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful W F M
  haveI : Module.Finite W (integralClosure W M) := IsIntegralClosure.finite W F M (integralClosure W M)
  haveI hVd : IsDiscreteValuationRing (integralClosure W M) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr W F M
  haveI : CharZero M := charZero_of_injective_algebraMap (algebraMap F M).injective
  have hdeg : ((q.map (algebraMap W F)).map (algebraMap F M)).degree ≠ 0 := by
    rw [degree_map_eq_of_injective (algebraMap F M).injective,
      degree_map_eq_of_injective (IsFractionRing.injective W F), hq2, degree_map,
      degree_eq_natDegree (minpoly.ne_zero hθi)]
    exact_mod_cast (minpoly.natDegree_pos hθi).ne'
  obtain ⟨x, hx⟩ := Splits.exists_eval_eq_zero (SplittingField.splits _) hdeg
  have hxq : aeval x q = 0 := by
    rw [Polynomial.map_map, eval_map, ← IsScalarTower.algebraMap_eq] at hx
    rw [aeval_def]; exact hx
  let V := integralClosure W M
  let y : V := ⟨x, q, hq3, hxq⟩
  have hyq : aeval y q = 0 := Subtype.ext (by
    change (integralClosure W M).val (aeval y q) = 0
    rw [← Polynomial.aeval_algHom_apply]; exact hxq)
  let f : W →+* V := algebraMap W V
  haveI hfl : IsLocalHom f := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom W M
  let ψ : K →+* ResidueField V := (ResidueField.map f).comp β
  have hψ : eval₂ ψ (residue V y) (minpoly K θ) = 0 := by
    have e1 := congrArg (residue V) hyq
    rw [map_zero, aeval_def, hom_eval₂] at e1
    have e2 : (residue V).comp (algebraMap W V) = (ResidueField.map f).comp (residue W) := by
      ext w; simp [f]
    rw [e2, ← eval₂_map, hq1, eval₂_map] at e1
    exact e1
  letI : Algebra K (ResidueField V) := ψ.toAlgebra
  let pb := IntermediateField.adjoin.powerBasis hθi
  let τ : K⟮θ⟯ →ₐ[K] ResidueField V := pb.lift (residue V y) (by
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen, aeval_def]; exact hψ)
  let σ : L →ₐ[K] ResidueField V :=
    τ.comp ((IntermediateField.equivOfEq hθ).trans IntermediateField.topEquiv).symm.toAlgHom
  refine ⟨V, inferInstance, inferInstance, inferInstance, f,
    (cDvr_iff V).2 ⟨hVd, GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local W V, inferInstance⟩,
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_inj W M, hfl, σ.toRingHom, fun a => ?_⟩
  change σ (algebraMap K L (residue A a)) = _
  rw [σ.commutes]
  change ResidueField.map f (ResidueField.map α (residue A a)) = _
  simp [ResidueField.map_residue]

end GlobalTheory
end

open IsLocalRing GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_residue_extension : ∀ {A : Type} [CommRing A] [IsLocalRing A] {L : Type} [Field L] (φ : ResidueField A →+* L), φ.Finite → CharZero (ResidueField A) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (α : A →+* W), IsLocalHom α → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : W →+* V), CDvr V ∧ Function.Injective f ∧ IsLocalHom f ∧ ∃ σ : L →+* ResidueField V, ∀ a : A, σ (φ (residue A a)) = residue V (f (α a)) := by
  atlas_forward_decl GlobalTheory.exists_cDvr_residue_lift
end

section
section
open IsLocalRing Polynomial

namespace GlobalTheory

theorem residue_eval_map_eq_aeval {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R]
    [IsLocalRing R] (φ : A →+* R) [IsLocalHom φ] (P : A[X]) (x : R) :
    letI := (ResidueField.map φ).toAlgebra
    residue R ((P.map φ).eval x) = aeval (residue R x) (P.map (residue A)) := by
  letI := (ResidueField.map φ).toAlgebra
  rw [aeval_def, eval₂_map, eval_map, hom_eval₂]
  congr 1

theorem exists_hensel_generator_of_residue_finite : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (φ : A →+* R) [IsLocalHom φ], (ResidueField.map φ).Finite → CharZero (ResidueField A) → ∃ (θ : R) (q : Polynomial A), q.Monic ∧ (q.map φ).eval θ = 0 ∧ IsUnit ((q.derivative.map φ).eval θ) ∧ (∀ r : R, ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R) ∧ ∀ P : Polynomial A, P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R → ∀ i, P.coeff i ∈ maximalIdeal A := by
  intro A R _ _ _ _ _ φ _ hfin hchar
  letI := (ResidueField.map φ).toAlgebra
  haveI : FiniteDimensional (ResidueField A) (ResidueField R) := hfin
  haveI : Algebra.IsSeparable (ResidueField A) (ResidueField R) := inferInstance
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ResidueField A) (ResidueField R)
  have hint : IsIntegral (ResidueField A) α := Algebra.IsIntegral.isIntegral α
  set p := minpoly (ResidueField A) α with hp
  have hpm : p.Monic := minpoly.monic hint
  have hlift : p ∈ lifts (residue A) :=
    (lifts_iff_coeff_lifts p).2 fun n => residue_surjective (p.coeff n)
  obtain ⟨q, hqmap, hqdeg, hqm⟩ := lifts_and_degree_eq_and_monic hlift hpm
  have hqnat : q.natDegree = p.natDegree := natDegree_eq_of_degree_eq hqdeg
  obtain ⟨θ₀, hθ₀⟩ := residue_surjective (R := R) α
  have hmon : (q.map φ).Monic := hqm.map φ
  have h1 : (q.map φ).eval θ₀ ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, residue_eval_map_eq_aeval, hqmap, hθ₀]
    exact minpoly.aeval _ _
  have hder : ∀ x : R, residue R x = α → IsUnit ((q.derivative.map φ).eval x) := by
    intro x hx
    rw [← residue_ne_zero_iff_isUnit, residue_eval_map_eq_aeval, ← derivative_map, hqmap, hx]
    have hsep : (minpoly (ResidueField A) α).Separable :=
      Algebra.IsSeparable.isSeparable (ResidueField A) α
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval _ _)
  have h2 : IsUnit ((q.map φ).derivative.eval θ₀) := by
    rw [derivative_map]; exact hder θ₀ hθ₀
  obtain ⟨θ, hroot, hθθ₀⟩ :=
    (IsAdicComplete.henselianRing R (maximalIdeal R)).is_henselian _ hmon θ₀ h1 (h2.map _)
  have hθ : residue R θ = α := by
    rw [← hθ₀, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hθθ₀
  refine ⟨θ, q, hqm, hroot, hder θ hθ, ?_, ?_⟩
  · intro r
    have hr : residue R r ∈ Algebra.adjoin (ResidueField A) {α} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
        IntermediateField.mem_toSubalgebra, hα]
      exact IntermediateField.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hr
    obtain ⟨pb, hpb⟩ := hr
    obtain ⟨P, hP⟩ := map_surjective (residue A) residue_surjective pb
    refine ⟨P, ?_⟩
    rw [← residue_eq_zero_iff, map_sub, residue_eval_map_eq_aeval, hP, hθ, sub_eq_zero]
    exact hpb.symm
  · intro P hdeg hmem i
    rw [← residue_eq_zero_iff, residue_eval_map_eq_aeval, hθ] at hmem
    have hz : P.map (residue A) = 0 := by
      by_contra hne
      have := minpoly.degree_le_of_ne_zero (ResidueField A) α hne hmem
      have h3 := natDegree_le_natDegree this
      have h4 : (P.map (residue A)).natDegree ≤ P.natDegree := natDegree_map_le
      rw [← hp] at h3
      omega
    rw [← residue_eq_zero_iff, ← coeff_map, hz, coeff_zero]

end GlobalTheory
end

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_element_complete : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (φ : A →+* R) [IsLocalHom φ], (ResidueField.map φ).Finite → CharZero (ResidueField A) → ∃ (θ : R) (q : Polynomial A), q.Monic ∧ (q.map φ).eval θ = 0 ∧ IsUnit ((q.derivative.map φ).eval θ) ∧ (∀ r : R, ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R) ∧ ∀ P : Polynomial A, P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R → ∀ i, P.coeff i ∈ maximalIdeal A := by
  atlas_forward_decl GlobalTheory.exists_hensel_generator_of_residue_finite
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.ChartLift

theorem eq_of_stalkClosedPointTo : ∀ {X : Scheme.{0}} {R W V : Type} [CommRing R] [IsLocalRing R] [CommRing W] [IsLocalRing W] [CommRing V] [IsLocalRing V] (ξ : Sp R ⟶ X) (χ : Sp W ⟶ X) (h : ξ (closedPoint R) = χ (closedPoint W)) (ψ : R →+* V) (f : W →+* V), IsLocalHom ψ → IsLocalHom f → ψ.comp (Scheme.stalkClosedPointTo ξ).hom = f.comp ((X.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ Scheme.stalkClosedPointTo χ).hom → spMap f ≫ χ = spMap ψ ≫ ξ := by
  intro X R W V _ _ _ _ _ _ ξ χ h ψ f hψ hf hc
  have key : ∀ (x y : X) (hxy : x = y) (g : X.presheaf.stalk y ⟶ CommRingCat.of V),
      Spec.map ((X.presheaf.stalkCongr (Inseparable.of_eq hxy)).hom ≫ g) ≫ X.fromSpecStalk x =
        Spec.map g ≫ X.fromSpecStalk y := by
    intro x y hxy g
    subst hxy
    simp
  have hc' : Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom ψ =
      (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ Scheme.stalkClosedPointTo χ ≫ CommRingCat.ofHom f := by
    ext a
    exact congrArg (fun g : _ →+* V => g a) hc
  conv_lhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk χ]
  conv_rhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ]
  simp only [spMap, ← Category.assoc, ← Spec.map_comp]
  rw [hc', key _ _ h]

theorem exists_lift_to_chart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) {k : Type} [Field k] {m e : ℕ} (ξ : Sp (ChartRing k m e) ⟶ gen Y), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (χ : Sp W ⟶ Y.X), χ (closedPoint W) = genι Y (ξ (closedPoint _)) → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : W →+* V) (ψ : ChartRing k m e →+* V), CDvr V ∧ Function.Injective f ∧ IsLocalHom f ∧ IsLocalHom ψ ∧ spMap f ≫ χ = spMap ψ ≫ ξ ≫ genι Y := by
  intro E _ _ _ H D l Xo c Y k _ m e ξ hξ W _ _ _ hW χ hχ
  have hiso : IsIso (spMap (RingHom.id c.F)) := by
    show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
    rw [show CommRingCat.ofHom (RingHom.id c.F) = 𝟙 (CommRingCat.of c.F) from rfl, Spec.map_id]
    infer_instance
  haveI : IsIso (genι Y) := inferInstance
  let χ' : Sp W ⟶ gen Y := χ ≫ inv (genι Y)
  have hχχ : χ' ≫ genι Y = χ := by simp [χ']
  have hpt : ξ (closedPoint (ChartRing k m e)) = χ' (closedPoint W) := by
    have h1 : genι Y (χ' (closedPoint W)) = χ (closedPoint W) := by
      rw [← hχχ]; rfl
    apply (genι Y).isOpenEmbedding.injective
    rw [h1, hχ]
  let φ : (gen Y).presheaf.stalk (ξ (closedPoint (ChartRing k m e))) →+* ChartRing k m e := (Scheme.stalkClosedPointTo ξ).hom
  let α : (gen Y).presheaf.stalk (ξ (closedPoint (ChartRing k m e))) →+* W := (((gen Y).presheaf.stalkCongr (Inseparable.of_eq hpt)).hom ≫ Scheme.stalkClosedPointTo χ').hom
  haveI : IsLocalHom α := by
    simp only [α, CommRingCat.hom_comp]
    infer_instance
  haveI : IsLocalHom φ := Scheme.isLocalHom_stalkClosedPointTo' ξ
  obtain ⟨hflat, hmax, hfin⟩ := hξ
  have hfin' : (ResidueField.map φ).Finite := by
    rw [← ResidueField.map_comp_residue] at hfin
    exact RingHom.Finite.of_comp_finite hfin
  have hch0 : CharZero (ResidueField ((gen Y).presheaf.stalk (ξ (closedPoint (ChartRing k m e))))) := by
    let g : c.F →+* ResidueField ((gen Y).presheaf.stalk (ξ (closedPoint (ChartRing k m e)))) :=
      (residue _).comp ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv ≫
        (Sp c.F).presheaf.germ ⊤ ((genStr Y) (ξ (closedPoint _))) trivial ≫
        (genStr Y).stalkMap (ξ (closedPoint _))).hom
    exact (RingHom.charZero_iff g.injective).1 inferInstance
  obtain ⟨V, _, _, _, f, hV, hfinj, hfloc, σ, hσ⟩ := GlobalTheory.T.exists_dvr_residue_extension (ResidueField.map φ) hfin' hch0 W hW α inferInstance
  haveI := hV.2.1
  have : IsAdicComplete (maximalIdeal k) k := by rw [maximalIdeal_eq_bot]; infer_instance
  haveI hCA : IsAdicComplete (maximalIdeal (ChartRing k m e)) (ChartRing k m e) :=
    GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _
  obtain ⟨θ, q, hqm, hqθ, hqd, hgen, hind⟩ := GlobalTheory.T.exists_primitive_element_complete φ hfin' hch0
  obtain ⟨η, hη, -⟩ := GlobalTheory.T.exists_hensel_root_residue φ (f.comp α) σ (fun a => by rw [RingHom.comp_apply, ← hσ a, ResidueField.map_residue]) θ q hqm hqθ hqd
  have hgp := GlobalTheory.T.polynomial_approx_pow_maximal φ hmax θ hgen
  have hip := GlobalTheory.T.polynomial_approx_uniqueness φ hflat hmax θ q hqm hqθ hgp hind
  obtain ⟨ψ, hψ, hψl⟩ := GlobalTheory.T.hensel_roots_compatible φ (f.comp α) inferInstance θ η q hqm hqθ hη hgp hip
  refine ⟨V, inferInstance, inferInstance, inferInstance, f, ψ, hV, hfinj, hfloc, hψl, ?_⟩
  have hg := eq_of_stalkClosedPointTo ξ χ' hpt ψ f hψl hfloc hψ
  rw [← hχχ, ← Category.assoc, hg, Category.assoc]

end GlobalTheory.ChartLift
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_lift_through_etale_chart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) {k : Type} [Field k] {m e : ℕ} (ξ : Sp (ChartRing k m e) ⟶ gen Y), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (χ : Sp W ⟶ Y.X), χ (closedPoint W) = genι Y (ξ (closedPoint _)) → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : W →+* V) (ψ : ChartRing k m e →+* V), CDvr V ∧ Function.Injective f ∧ IsLocalHom f ∧ IsLocalHom ψ ∧ spMap f ≫ χ = spMap ψ ≫ ξ ≫ genι Y := by
  atlas_forward_decl GlobalTheory.ChartLift.exists_lift_to_chart
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomial_form_on_chart_ring : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) {k : Type} [Field k] {m e : ℕ} (ξ : Sp (ChartRing k m e) ⟶ gen Y) {tC : SAB H (Sp (ChartRing k m e))} (_ : SABMap tC Y.t (ξ ≫ genι Y)) (PC : PELUnif (maximalIdeal (ChartRing k m e)) tC) (γ : Fin m → LinearMap.BilinForm ℤ PC.D.toPre.X), IsMonomial PC.D.toPre (bdParam k m e) γ → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (ϖ : W), Irreducible ϖ → ∀ (χ : Sp W ⟶ Y.X) (t : SAB H (Sp W)) (_ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t), Set.range (jK W ≫ χ) ⊆ Set.range Y.j → ∀ (be : LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre ![ϖ] ![be] → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (ϖ' : V), Irreducible ϖ' → ∀ (f : W →+* V) (ψ : ChartRing k m e →+* V), Function.Injective f → IsLocalHom f → IsLocalHom ψ → spMap f ≫ χ = spMap ψ ≫ ξ ≫ genι Y → ∀ (r : ℕ) (u : Vˣ), f ϖ = u * ϖ' ^ r → ∀ (n : Fin m → ℕ) (v : Fin m → Vˣ), (∀ i, ψ (bdParam k m e i) = v i * ϖ' ^ n i) → ∃ ε : P.D.toPre.X ≃ₗ[𝓞 E] PC.D.toPre.X, ∀ y, (r : ℤ) * be y y = ∑ i, (n i : ℤ) * γ i (ε y) (ε y) := by
  first | exact @GlobalTheory.TraitChartForm.main | exact GlobalTheory.TraitChartForm.main | (intros; apply GlobalTheory.TraitChartForm.main <;> assumption)
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan.PhiOrder

theorem lift_trait {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) {k : Type} [Field k] {m e : ℕ}
    (ξ : Sp (ChartRing k m e) ⟶ gen Y) (hξ : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom)
    (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (hW : CDvr W) (χ : Sp W ⟶ Y.X)
    (hχ : χ (closedPoint W) = genι Y (ξ (closedPoint _))) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : W →+* V) (ψ : ChartRing k m e →+* V),
      CDvr V ∧ Function.Injective f ∧ IsLocalHom f ∧ IsLocalHom ψ ∧ spMap f ≫ χ = spMap ψ ≫ ξ ≫ genι Y :=
  GlobalTheory.T.exists_dvr_lift_through_etale_chart Y ξ hξ W hW χ hχ

theorem form_compare {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) {k : Type} [Field k] {m e : ℕ}
    (ξ : Sp (ChartRing k m e) ⟶ gen Y) {tC : SAB H (Sp (ChartRing k m e))} (mC : SABMap tC Y.t (ξ ≫ genι Y))
    (PC : PELUnif (maximalIdeal (ChartRing k m e)) tC) (γ : Fin m → LinearMap.BilinForm ℤ PC.D.toPre.X)
    (hγ : IsMonomial PC.D.toPre (bdParam k m e) γ)
    (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (hW : CDvr W) (ϖ : W) (hϖ : Irreducible ϖ)
    (χ : Sp W ⟶ Y.X) (t : SAB H (Sp W)) (mχ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t)
    (hr : Set.range (jK W ≫ χ) ⊆ Set.range Y.j) (be : LinearMap.BilinForm ℤ P.D.toPre.X)
    (hbe : IsMonomial P.D.toPre ![ϖ] ![be])
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V) (ϖ' : V) (hϖ' : Irreducible ϖ')
    (f : W →+* V) (ψ : ChartRing k m e →+* V) (hf : Function.Injective f) [hfl : IsLocalHom f] [hψl : IsLocalHom ψ]
    (hc : spMap f ≫ χ = spMap ψ ≫ ξ ≫ genι Y) (r : ℕ) (u : Vˣ) (hu : f ϖ = u * ϖ' ^ r)
    (n : Fin m → ℕ) (v : Fin m → Vˣ) (hv : ∀ i, ψ (bdParam k m e i) = v i * ϖ' ^ n i) :
    ∃ ε : P.D.toPre.X ≃ₗ[𝓞 E] PC.D.toPre.X, ∀ y, (r : ℤ) * be y y = ∑ i, (n i : ℤ) * γ i (ε y) (ε y) :=
  GlobalTheory.T.monomial_form_on_chart_ring Y ξ mC PC γ hγ W hW ϖ hϖ χ t mχ P hr be hbe V hV ϖ' hϖ' f ψ hf hfl hψl hc r u hu n v hv

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem comb_evalZ (ψ φ : InvFun (𝓞 E)) (d : ℕ) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X]
    (be : LinearMap.BilinForm ℤ X) : (comb 0 ψ d φ).evalZ be = d * φ.evalZ be := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' (𝓞 E) X
  unfold InvFun.evalZ
  rw [InvFun.eval_eq _ hr, InvFun.eval_eq _ hr]
  show (0 : ℕ) * ψ.toFun n _ + d * φ.toFun n _ = _
  simp

theorem eq_of_diag {X : Type} [AddCommGroup X] (B₁ B₂ : LinearMap.BilinForm ℤ X) (h₁ : ∀ y z, B₁ y z = B₁ z y)
    (h₂ : ∀ y z, B₂ y z = B₂ z y) (h : ∀ y, B₁ y y = B₂ y y) (y z : X) : B₁ y z = B₂ y z := by
  have e1 := h (y + z)
  simp only [map_add, LinearMap.add_apply] at e1
  rw [h y, h z, h₁ z y, h₂ z y] at e1
  omega

theorem range_j_subset_abLocus {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Set.range Y.j ⊆ abLocus Y.t.G := by
  rintro _ ⟨w, rfl⟩
  have hw : Y.jQ w ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by rw [Y.ab_gen]; exact ⟨w, rfl⟩
  show (Y.jQ ≫ pullback.fst _ _) w ∈ _
  rw [Scheme.Hom.comp_apply]
  exact hw

end SlopeTestRemainingChoices

section Cases

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem order_of_abelian (Y : Model Xo c (RingHom.id c.F)) (BD : EffCartierData Y.X) (φ : InvFun (𝓞 E))
    (hsupp : ∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Y.t.G)
    (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (hW : CDvr W) (ϖ : W)
    (χ : Sp W ⟶ Y.X) (t : SAB H (Sp W)) (mχ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t)
    (be : LinearMap.BilinForm ℤ P.D.toPre.X) (hab : χ (closedPoint W) ∈ abLocus Y.t.G) :
    ∃ n : ℕ, (n : ℝ) = φ.evalZ be ∧ idlAlong BD.idealSheaf χ = Ideal.span {ϖ ^ n} := by
  obtain ⟨h₁, h₂, h₃⟩ := hW
  let T : CDVR := { V := W }
  have hc : (closedPoint T.V : Sp T.V) ∈ abLocus t.G :=
    (abLocus_pullback abLocusOne Y.t.semi mχ.cart.1 _).1 hab
  have hs : Subsingleton P.D.toPre.X := (closed_mem_abLocus_iff T P).1 hc
  refine ⟨0, ?_, ?_⟩
  · rw [InvFun.evalZ, φ.eval_of_subsingleton]; simp
  · have hns : χ (closedPoint W) ∉ BD.idealSheaf.support := fun h => hsupp _ h hab
    have htop : FinalTheorems.stalkId BD.idealSheaf (χ (closedPoint W)) = ⊤ := by
      by_contra h
      exact hns ((mem_support_iff_stalkId _ _).2 h)
    rw [pow_zero, Ideal.span_singleton_one, idlAlong, htop, Ideal.map_top]

end Cases

section Chart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem order_of_chart (φ : InvFun (𝓞 E)) (Y : Model Xo c (RingHom.id c.F)) (BD : EffCartierData Y.X) (d : ℕ)
    (x : gen Y) (hch : GlobalTheory.MumfordChart.HasChartOf φ Y BD d x)
    (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (hW : CDvr W) (ϖ : W) (hϖ : Irreducible ϖ)
    (χ : Sp W ⟶ Y.X) (t : SAB H (Sp W)) (mχ : SABMap t Y.t χ) (P : PELUnif (maximalIdeal W) t)
    (hr : Set.range (jK W ≫ χ) ⊆ Set.range Y.j) (be : LinearMap.BilinForm ℤ P.D.toPre.X)
    (hbe : ∀ y z, be y z = be z y) (hmon : IsMonomial P.D.toPre ![ϖ] ![be])
    (hx : χ (closedPoint W) = genι Y x) :
    ∃ n : ℕ, (n : ℝ) = d * φ.evalZ be ∧ idlAlong BD.idealSheaf χ = Ideal.span {ϖ ^ n} := by
  obtain ⟨k, _, m, e, ξ, tC, PC, γ, δ, a, hξx, h₁, -, h₃, ⟨mC⟩, h₅, -, hcone, hγδ, ha, hid⟩ := hch
  have := hW.1
  obtain ⟨V, _, _, _, f, ψ, hV, hfi, hfl, hψl, hcomm⟩ := lift_trait Y ξ h₁ W hW χ (by rw [hx, hξx])
  have := hV.1
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hfϖ : f ϖ ≠ 0 := fun h => hϖ.ne_zero (hfi (h.trans (map_zero f).symm))
  obtain ⟨r, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hfϖ hϖ'

  have hψt : ∀ i, ψ (bdParam k m e i) ≠ 0 := by
    let q : Sp V := ⟨⊥, Ideal.isPrime_bot⟩
    have hq : spMap f q = (⟨⊥, Ideal.isPrime_bot⟩ : Sp W) :=
      PrimeSpectrum.ext (Ideal.comap_bot_of_injective f hfi)
    have hw : (⟨⊥, Ideal.isPrime_bot⟩ : Sp W) = jK W (⟨⊥, Ideal.isPrime_bot⟩ : Sp (FractionRing W)) :=
      PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ (IsFractionRing.injective W (FractionRing W))).symm
    have e1 : χ (spMap f q) = genι Y (ξ (spMap ψ q)) := by
      rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    have hab : genι Y (ξ (spMap ψ q)) ∈ abLocus Y.t.G := by
      rw [← e1, hq, hw]
      exact range_j_subset_abLocus Y (hr ⟨_, Scheme.Hom.comp_apply (jK W) χ _⟩)
    have hnb : ξ (spMap ψ q) ∉ genBd Y := fun h => (mem_genBd_iff.1 h) hab
    have hp : ∏ i, bdParam k m e i ∉ (spMap ψ q).asIdeal := fun h => hnb ((h₃ _).2 h)
    have hp' : ψ (∏ i, bdParam k m e i) ≠ 0 := fun h => hp (by
      show ψ (∏ i, bdParam k m e i) ∈ (⊥ : Ideal V)
      rw [h]; exact Ideal.zero_mem _)
    rw [map_prod] at hp'
    exact fun i => Finset.prod_ne_zero_iff.1 hp' i (Finset.mem_univ i)
  choose nn vv hvv using fun i => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hψt i) hϖ'
  obtain ⟨ε, hε⟩ := form_compare Y ξ mC PC (fun i => (γ i : LinearMap.BilinForm ℤ PC.D.toPre.X)) h₅ W hW ϖ hϖ χ t mχ P
    hr be hmon V hV ϖ' hϖ' f ψ hfi hcomm r u hu nn vv hvv

  have hU : IsUnit (∏ i, (vv i : V) ^ a i) := by
    have := (∏ i, vv i ^ a i).isUnit
    push_cast at this
    exact this
  have hmapψ : idlAlong BD.idealSheaf (spMap f ≫ χ) = Ideal.span {ϖ' ^ ∑ i, nn i * a i} := by
    rw [hcomm, GlobalTheory.TraitOrder.idlAlong_comp, hid, Ideal.map_span, Set.image_singleton, map_prod]
    simp_rw [map_pow, hvv, mul_pow, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]
    exact Ideal.span_singleton_mul_left_unit hU _
  have hmapf : (idlAlong BD.idealSheaf χ).map f = Ideal.span {ϖ' ^ ∑ i, nn i * a i} := by
    rw [← GlobalTheory.TraitOrder.idlAlong_comp]; exact hmapψ
  have hne : idlAlong BD.idealSheaf χ ≠ ⊥ := by
    intro h
    rw [h, Ideal.map_bot] at hmapf
    exact pow_ne_zero _ hϖ'.ne_zero (Ideal.span_singleton_eq_bot.1 hmapf.symm)
  obtain ⟨n0, hn0⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
  have hrN : r * n0 = ∑ i, nn i * a i := by
    rw [hn0, Ideal.map_span, Set.image_singleton, map_pow, hu, mul_pow, ← pow_mul,
      Ideal.span_singleton_mul_left_unit (u.isUnit.pow _)] at hmapf
    have hass := (Ideal.span_singleton_eq_span_singleton.1 hmapf)
    exact le_antisymm ((pow_dvd_pow_iff hϖ'.ne_zero hϖ'.not_isUnit).1 hass.dvd)
      ((pow_dvd_pow_iff hϖ'.ne_zero hϖ'.not_isUnit).1 hass.symm.dvd)
  refine ⟨n0, ?_, hn0⟩

  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hu
    exact hϖ.not_isUnit (isUnit_of_map_unit f ϖ (hu ▸ u.isUnit))
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr0
  let εZ : P.D.toPre.X →ₗ[ℤ] PC.D.toPre.X := ε.toLinearMap.toAddMonoidHom.toIntLinearMap
  let B₂ : LinearMap.BilinForm ℤ P.D.toPre.X :=
    ∑ i, (nn i : ℤ) • (γ i : LinearMap.BilinForm ℤ PC.D.toPre.X).compl₁₂ εZ εZ
  have hB₂ : ∀ y z, B₂ y z = ∑ i, (nn i : ℤ) * (γ i : LinearMap.BilinForm ℤ PC.D.toPre.X) (ε y) (ε z) := by
    intro y z
    simp [B₂, εZ, LinearMap.sum_apply]
  have hfull : ∀ y z, (r : ℤ) * be y z = ∑ i, (nn i : ℤ) * (γ i : LinearMap.BilinForm ℤ PC.D.toPre.X) (ε y) (ε z) := by
    intro y z
    have := eq_of_diag ((r : ℤ) • be) B₂ (fun y z => by simp [hbe y z])
      (fun y z => by rw [hB₂, hB₂]; exact Finset.sum_congr rfl fun i _ => by rw [(γ i).2.1])
      (fun y => by rw [hB₂, ← hε y]; simp) y z
    rw [hB₂] at this
    simpa using this
  have hlin : φ.LinearOn (fun i => (γ i : LinearMap.BilinForm ℤ PC.D.toPre.X)) := by
    have e' : (fun i => (γ i : LinearMap.BilinForm ℤ PC.D.toPre.X)) = fun i => (l.M' : ℤ) • δ i := funext hγδ
    rw [e']; exact hcone.linearOn_smul l.M'
  have hφbe : φ.evalZ be = ∑ i, ((nn i : ℝ) / r) * φ.evalZ (γ i : LinearMap.BilinForm ℤ PC.D.toPre.X) := by
    rw [← hlin (fun i => (nn i : ℝ) / r) (fun i => by positivity), ← φ.eval_equiv ε]
    unfold InvFun.evalZ
    congr 1
    funext y z
    have h := congrArg (fun n : ℤ => (n : ℝ)) (hfull y z)
    push_cast at h
    rw [eq_comm, ← mul_right_inj' hr', Finset.mul_sum, h]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  have hN : (r : ℝ) * n0 = ∑ i, (nn i : ℝ) * (d * φ.evalZ (γ i : LinearMap.BilinForm ℤ PC.D.toPre.X)) := by
    have := congrArg (fun n : ℕ => (n : ℝ)) hrN
    push_cast at this
    rw [this]
    exact Finset.sum_congr rfl fun i _ => by rw [ha]
  rw [hφbe, ← mul_right_inj' hr', hN, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

end Chart

theorem isPhiDiv_comb : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} (φ : InvFun (𝓞 E)), IsPolFan H.bar (min D.p D.q) φ →
    NoSelfInt H.bar (min D.p D.q) φ → ∀ (Y : Model Xo c (RingHom.id c.F)) (BD : GlobalTheory.EffCartierData Y.X) (d : ℕ),
    SmoothOfRelativeDimension D.dim (genStr Y) → FinalTheorems.Snc (genBdIdeal Y) →
    (∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Y.t.G) → (∀ x ∈ genBd Y, GlobalTheory.MumfordChart.HasChartOf φ Y BD d x) →
    IsPhiDiv (comb 0 φ d φ) Y BD := by
  intro E _ _ _ H D l Xo c φ _ _ Y BD d _ _ hsupp hch W _ _ _ hW ϖ hϖ χ t mχ P hr be hbe hmon
  by_cases hab : χ (closedPoint W) ∈ abLocus Y.t.G
  · exact order_of_abelian Y BD _ hsupp W hW ϖ χ t mχ P be hab
  · rcases GlobalTheory.GenFan.exists_of_id Y (χ (closedPoint W)) with ⟨x, hxb, hxz⟩ | hj
    · obtain ⟨n, hn, hI⟩ := order_of_chart φ Y BD d x (hch x hxb) W hW ϖ hϖ χ t mχ P hr be hbe.1 hmon hxz.symm
      exact ⟨n, hn.trans (comb_evalZ φ φ d be).symm, hI⟩
    · exact absurd (range_j_subset_abLocus Y hj) hab

end GlobalTheory.GenFan.PhiOrder
end
end
