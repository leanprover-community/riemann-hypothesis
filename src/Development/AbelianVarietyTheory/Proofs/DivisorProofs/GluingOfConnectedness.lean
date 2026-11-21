import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensityStatementHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelOpenNoetherian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsLocallyNoetherianOfIsQProjOver
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelWithRatio
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalOfConnectedDensity

section
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.density_statement_holds : DensSt := by
  first | exact @GlobalTheory.FlatModel.densSt | exact GlobalTheory.FlatModel.densSt | (intros; apply GlobalTheory.FlatModel.densSt <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

theorem GlobalTheory.FlatModel.isIrreducible_of_geomIrr_of_le_basicOpen : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime],
    (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens),
    Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → GeomIrr s Xw → IsIrreducible (Xw : Set X) := by
  intro F _ _ V p hpr hpV X s Xw hXw hg
  have hirr := hg F V.subtype Subtype.val_injective
  set P := pullback (Xw.ι ≫ s) (spMap V.subtype)
  have hI := (IrreducibleSpace.isIrreducible_univ P).image (⇑(pullback.fst (Xw.ι ≫ s) (spMap V.subtype) ≫ Xw.ι))
    (Scheme.Hom.continuous _).continuousOn
  rw [Set.image_univ] at hI
  convert hI using 1
  have hdvr := (GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField V hpr.out.ne_zero hpV).1
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Pullback.range_fst]
  have key : ∀ x : (Xw : Scheme), (Xw.ι ≫ s) x ∈ Set.range (spMap V.subtype) := by
    intro x
    have hx : Xw.ι x ∈ X.basicOpen (p : Γ(X, ⊤)) := by
      apply hXw
      show Xw.ι x ∈ (Xw : Set X)
      rw [← Scheme.Opens.range_ι]
      exact ⟨x, rfl⟩
    have h1 : s (Xw.ι x) ∈ (Sp V).basicOpen (p : Γ(Sp V, ⊤)) := by
      rw [← Scheme.Hom.mem_preimage, Scheme.preimage_basicOpen_top, map_natCast]
      exact hx
    rw [basicOpen_eq_of_affine', map_natCast] at h1
    have hbot : (s (Xw.ι x)).asIdeal = ⊥ := by
      by_contra hne
      have hm := Ideal.IsPrime.isMaximal (s (Xw.ι x)).2 hne
      have he := IsLocalRing.eq_maximalIdeal hm
      obtain ⟨ha, hmem⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal (A := V)).1 hpV
      apply h1
      rw [he]
      convert hmem
      simp
    refine ⟨⟨⊥, Ideal.bot_prime⟩, ?_⟩
    rw [Scheme.Hom.comp_apply]
    refine PrimeSpectrum.ext ?_
    rw [hbot]
    exact (RingHom.ker_eq_bot_iff_eq_zero _).2 fun a ha => Subtype.ext ha
  have hu : (⇑(Xw.ι ≫ s) ⁻¹' Set.range ⇑(spMap V.subtype)) = Set.univ := Set.eq_univ_of_forall key
  rw [hu, Set.image_univ, Scheme.Opens.range_ι]
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometrically_irreducible_open_irreducible : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime],
    (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens),
    Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → GeomIrr s Xw → IsIrreducible (Xw : Set X) := by
  atlas_forward_decl GlobalTheory.FlatModel.isIrreducible_of_geomIrr_of_le_basicOpen
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem isTest_comp_opens_ι {p : ℕ} [Fact p.Prime] {X : Scheme.{0}} (U Xw : X.Opens)
    (yb : Sp 𝓞_ℂ_[p] ⟶ U.toScheme) (h : IsTest p (U.ι ⁻¹ᵁ Xw) yb) : IsTest p Xw (yb ≫ U.ι) := by
  obtain ⟨⟨T, kO, yT, hT, hk, he⟩, hr⟩ := h
  refine ⟨⟨T, kO, yT ≫ U.ι, hT, hk, by rw [← Category.assoc, he]⟩, ?_⟩
  rintro _ ⟨w, rfl⟩
  have := hr ⟨w, rfl⟩
  simpa [Scheme.Hom.comp_apply] using this

theorem chartAt_opens_restrict : ∀ (p n : ℕ) [Fact p.Prime] (X : Scheme.{0}) (U Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p])
    (x : U.toScheme), ChartAt p n Xw K (U.ι x) → ChartAt p n (U.ι ⁻¹ᵁ Xw) (fun yb => K (yb ≫ U.ι)) x := by
  intro p n _ X U Xw K x h
  obtain ⟨R, _, ξ, J, _, Q, u, hξ, ⟨z, hz⟩, hT⟩ := h
  have hxU : U.ι x ∈ (U : Set X) := by rw [← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩
  have hzU : z ∈ ((ξ ⁻¹ᵁ U : (Sp R).Opens) : Set (Sp R)) := by
    show ξ z ∈ U
    rw [hz]; exact hxU
  obtain ⟨_, ⟨f, rfl⟩, hzf, hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hzU (ξ ⁻¹ᵁ U).isOpen
  let ι' := algebraMap R (Localization.Away f)
  have hrange : Set.range (spMap ι') = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away f) f
  have hsub : Set.range (spMap ι' ≫ ξ) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    have hy : (spMap ι') y ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := hrange ▸ ⟨y, rfl⟩
    exact hfU hy
  obtain ⟨ξ₁, hfac⟩ : ∃ ξ₁ : Sp (Localization.Away f) ⟶ U.toScheme, ξ₁ ≫ U.ι = spMap ι' ≫ ξ :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hsub⟩
  have hξ₁ : IsOpenImmersion ξ₁ := by
    haveI : IsOpenImmersion (ξ₁ ≫ U.ι) := by rw [hfac]; infer_instance
    exact IsOpenImmersion.of_comp ξ₁ U.ι
  let Q' : J → Localization.Away f := fun j => ι' (Q j)
  have hunit : ∀ j, IsUnit (((algebraMap (Localization.Away f) (Localization.Away ((p : Localization.Away f) * Q' j))).comp ι')
      ((p : R) * Q j)) := by
    intro j
    rw [RingHom.comp_apply, map_mul, map_natCast]
    exact IsLocalization.Away.algebraMap_isUnit _
  obtain ⟨g, hg⟩ : ∃ g : ∀ j, Localization.Away ((p : R) * Q j) →+* Localization.Away ((p : Localization.Away f) * Q' j),
      ∀ j, (g j).comp (algebraMap R _) = (algebraMap (Localization.Away f) _).comp ι' :=
    ⟨fun j => IsLocalization.Away.lift ((p : R) * Q j) (hunit j),
      fun j => IsLocalization.Away.lift_comp _ (hunit j)⟩
  refine ⟨Localization.Away f, inferInstance, ξ₁, J, inferInstance, Q', fun j => Units.map (g j : _ →* _) (u j), hξ₁,
    ?_, ?_⟩
  · have hz' : z ∈ Set.range (spMap ι') := hrange ▸ hzf
    obtain ⟨z', rfl⟩ := hz'
    refine ⟨z', (Scheme.Hom.isOpenEmbedding U.ι).injective ?_⟩
    rw [← hz, ← Scheme.Hom.comp_apply, hfac, Scheme.Hom.comp_apply]
  · intro φ' hφ'
    have heq : spMap (φ'.comp ι') ≫ ξ = (spMap φ' ≫ ξ₁) ≫ U.ι := by
      rw [Category.assoc, hfac, sp_sp]
    obtain ⟨⟨j0, hj0⟩, hall⟩ := hT (φ'.comp ι') (by rw [heq]; exact isTest_comp_opens_ι U Xw _ hφ')
    refine ⟨⟨j0, hj0⟩, fun j hj ψ' hψ' κ hκ => ?_⟩
    have := hall j hj (ψ'.comp (g j))
      (by rw [RingHom.comp_assoc, hg j, ← RingHom.comp_assoc, hψ', RingHom.comp_assoc]) κ (by rw [heq]; exact hκ)
    exact this

end GlobalTheory.FlatModel
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_restrict_open : ∀ (p n : ℕ) [Fact p.Prime] (X : Scheme.{0}) (U Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p])
    (x : U.toScheme), ChartAt p n Xw K (U.ι x) → ChartAt p n (U.ι ⁻¹ᵁ Xw) (fun yb => K (yb ≫ U.ι)) x := by
  atlas_forward_decl GlobalTheory.FlatModel.chartAt_opens_restrict
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem geomIrr_restrict : ∀ (V : Type) [CommRing V] (X : Scheme.{0}) (s : X ⟶ Sp V) (U Xw : X.Opens), Xw ≤ U →
    GeomIrr s Xw → GeomIrr (U.ι ≫ s) (U.ι ⁻¹ᵁ Xw) := by
  intro V _ X s U Xw hle h k _ f hf
  have hr : Set.range ((U.ι ⁻¹ᵁ Xw).ι ≫ U.ι) = Set.range Xw.ι := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    have : ((U.ι ⁻¹ᵁ Xw : U.toScheme.Opens) : Set U.toScheme) = U.ι ⁻¹' (Xw : Set X) := rfl
    rw [this, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
    exact Set.inter_eq_left.2 hle
  let e := IsOpenImmersion.isoOfRangeEq ((U.ι ⁻¹ᵁ Xw).ι ≫ U.ι) Xw.ι hr
  have he : e.hom ≫ Xw.ι = (U.ι ⁻¹ᵁ Xw).ι ≫ U.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have h0 := h k f hf
  let m := pullback.map (Xw.ι ≫ s) (spMap f) ((U.ι ⁻¹ᵁ Xw).ι ≫ U.ι ≫ s) (spMap f) e.inv (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, ← Category.assoc _ U.ι s, ← he]; simp) (by simp)
  haveI : IsIso m := by unfold m; infer_instance
  exact Function.Surjective.irreducibleSpace m.homeomorph.continuous m.homeomorph.surjective

theorem range_subset_of_bot_mem {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} (g : Sp R ⟶ X) {C : Set X}
    (hC : IsClosed C) (h : g (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ C) : Set.range g ⊆ C := by
  rintro _ ⟨z, rfl⟩
  have h1 : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ⤳ z := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  exact (h1.map g.continuous).mem_closed hC h

theorem isTest_comp {p : ℕ} [Fact p.Prime] {X : Scheme.{0}} (U Xw : X.Opens) {yb : Sp 𝓞_ℂ_[p] ⟶ U.toScheme}
    (h : IsTest p (U.ι ⁻¹ᵁ Xw) yb) : IsTest p Xw (yb ≫ U.ι) := by
  obtain ⟨⟨T, kO, yT, hT, hk, e⟩, hr⟩ := h
  refine ⟨⟨T, kO, yT ≫ U.ι, hT, hk, by rw [← Category.assoc, e]⟩, ?_⟩
  rintro _ ⟨z, rfl⟩
  have := hr ⟨z, rfl⟩
  rw [← Category.assoc]
  exact this

theorem restrictSt : RestrictSt := by
  intro F _ _ V p _ hpV X s Xw hnorm hproj hflat hXw hirr n K hK hchart
  haveI : IsNoetherianRing V := GlobalTheory.ModelNoeth.isNoetherianRing_valuationSubring V
  haveI : IsLocallyNoetherian X := GlobalTheory.ZM.isLocallyNoetherian_of_isQProjOver (by
    obtain ⟨N, i, hi, e⟩ := hproj
    exact ⟨N, i, inferInstance, inferInstance, e⟩)
  haveI : GlobalTheory.IsNormalScheme X := GlobalTheory.IsNormalScheme.of_pred hnorm
  haveI : Flat s := hflat
  have hXi : IsIrreducible (Xw : Set X) := GlobalTheory.T.geometrically_irreducible_open_irreducible F V p hpV X s Xw hXw hirr
  obtain ⟨W, hW, hXwW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hXi
  have hWcl : W ⊆ closure (Xw : Set X) := by
    have h1 := subset_closure_inter_of_isPreirreducible_of_isOpen hW.1.2 Xw.isOpen
      (by rw [Set.inter_eq_right.2 hXwW]; exact hXi.nonempty)
    rwa [Set.inter_eq_right.2 hXwW] at h1
  let Z : irreducibleComponents X := ⟨W, hW⟩
  let U : X.Opens := GlobalTheory.IsNormalScheme.component Z
  have hU : (U : Set X) = W := rfl
  have hWc : IsClosed W := isClosed_of_mem_irreducibleComponents W hW
  refine ⟨U.toScheme, U.ι ≫ s, U.ι ⁻¹ᵁ Xw, fun yb => K (yb ≫ U.ι), inferInstance,
    GlobalTheory.IsNormalScheme.pred U.toScheme, ?_, inferInstance, ?_, geomIrr_restrict V X s U Xw hXwW hirr,
    fun yb hyb => hK _ (isTest_comp U Xw hyb), fun x => GlobalTheory.T.chart_restrict_open p n X U Xw K x (hchart _ (hWcl x.2)), ?_⟩
  · obtain ⟨N, i, hi, e⟩ := hproj
    exact ⟨N, U.ι ≫ i, inferInstance, by rw [Category.assoc, e]⟩
  · intro x hx
    have h := hXw hx
    have e := Scheme.preimage_basicOpen_top U.ι (p : Γ(X, ⊤))
    rw [map_natCast] at e
    rw [← e]
    exact h
  · intro yb ⟨⟨T, kO, yT, hT, hk, e⟩, hr⟩
    have hb : yb (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum 𝓞_ℂ_[p]) ∈ (Xw : Set X) := by
      rw [← bot_map (φ := algebraMap 𝓞_ℂ_[p] ℂ_[p]) (fun a b h => Subtype.ext h) yb]
      exact hr ⟨_, rfl⟩
    have hbT : yT (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.V) ∈ W := by
      rw [← bot_map hk yT, e]; exact hXwW hb
    have r1 : Set.range yb ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]; exact range_subset_of_bot_mem yb hWc (hXwW hb)
    have r2 : Set.range yT ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]; exact range_subset_of_bot_mem yT hWc hbT
    have f1 := IsOpenImmersion.lift_fac U.ι yb r1
    have f2 := IsOpenImmersion.lift_fac U.ι yT r2
    refine ⟨IsOpenImmersion.lift U.ι yb r1, ⟨⟨T, kO, IsOpenImmersion.lift U.ι yT r2, hT, hk, ?_⟩, ?_⟩, ?_⟩
    · rw [← cancel_mono U.ι, Category.assoc, f2, f1, e]
    · rintro _ ⟨z, rfl⟩
      show _ ∈ Xw
      rw [← Scheme.Hom.comp_apply, Category.assoc, f1]
      exact hr ⟨z, rfl⟩
    · simp only [f1]; exact le_rfl

end GlobalTheory.FlatModel
end
end

open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restriction_statement_holds : RestrictSt := by
  atlas_forward_decl GlobalTheory.FlatModel.restrictSt
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
namespace GlobalTheory.FlatModel.BlowupModel

theorem preimage_basicOpen_natCast (p : ℕ) {X X' : Scheme.{0}} (π : X' ⟶ X) :
    π ⁻¹ᵁ X.basicOpen (p : Γ(X, ⊤)) = X'.basicOpen (p : Γ(X', ⊤)) := by
  rw [Scheme.preimage_basicOpen, map_natCast]
  rfl

theorem isUnit_natCast_of_ne {F : Type} [Field F] (V : ValuationSubring F) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hqp : q ≠ p) (hV : (p : F) ∈ V.nonunits) : IsUnit (q : V) := by
  by_contra h
  have h1 : (q : V) ∈ IsLocalRing.maximalIdeal V := h
  have h2 : (p : V) ∈ IsLocalRing.maximalIdeal V := ValuationSubring.coe_mem_nonunits_iff.mp (by simpa using hV)
  have hc : IsCoprime (q : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 hqp)
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom V)
  apply (IsLocalRing.maximalIdeal V).ne_top_iff_one.1 (IsLocalRing.maximalIdeal.isMaximal V).ne_top
  rw [← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

theorem charZero_residueField {F : Type} [Field F] (V : ValuationSubring F) (p : ℕ) [hp : Fact p.Prime]
    (hV : (p : F) ∈ V.nonunits) {X : Scheme.{0}} (s : X ⟶ Sp V) (y : X)
    (hy : y ∈ X.basicOpen (p : Γ(X, ⊤))) : CharZero (X.residueField y) := by
  let φ : V →+* X.residueField y :=
    (X.evaluation ⊤ y trivial).hom.comp (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom)
  have hpy : (p : X.residueField y) ≠ 0 := by
    have := (X.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) y trivial (p : Γ(X, ⊤))).2 hy
    simpa using this
  have hq : ∀ q : ℕ, q.Prime → q ≠ p → (q : X.residueField y) ≠ 0 := by
    intro q hq hqp
    have hu := (isUnit_natCast_of_ne V p q hp.out hq hqp hV).map φ
    rw [map_natCast] at hu
    exact hu.ne_zero
  have := ringChar.charP (X.residueField y)
  rcases CharP.char_is_prime_or_zero (X.residueField y) (ringChar (X.residueField y)) with h | h
  · exfalso
    have h0 := ringChar.Nat.cast_ringChar (R := X.residueField y)
    by_cases e : ringChar (X.residueField y) = p
    · exact hpy (e ▸ h0)
    · exact hq _ h e h0
  · have := ringChar.of_eq h
    exact CharP.charP_to_charZero _

end GlobalTheory.FlatModel.BlowupModel

open GlobalTheory.FlatModel.BlowupModel in

theorem GlobalTheory.FlatModel.exists_normBlowup_off_basicOpen : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime],
    (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V), IsIntegral X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X →
    IsProjOver s → Flat s → ∀ J : X.IdealSheafData, (∀ x ∈ J.support, x ∉ X.basicOpen (p : Γ(X, ⊤))) →
    ∃ (X'' X' : Scheme.{0}) (b : X'' ⟶ X) (ν : X' ⟶ X''), ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap b) ∧
      IsIntegral X' ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' ∧ IsProjOver (ν ≫ b ≫ s) ∧ Flat (ν ≫ b ≫ s) ∧
      IsProper (ν ≫ b) ∧ IsIso ((ν ≫ b) ∣_ X.basicOpen (p : Γ(X, ⊤))) := by
  intro F _ _ V p _ hp X s hXi hXn hXp hXf J hJ
  have hDVR := (GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField V
    (Fact.out : p.Prime).ne_zero hp).1
  let U : X.Opens := X.basicOpen (p : Γ(X, ⊤))
  obtain ⟨X'', b, hb, hbs, hiso⟩ := GlobalTheory.ProjBlowup.exists_blowup s hXp J
  have hbU : IsIso (b ∣_ U) := hiso U fun x hx hJx => hJ x hJx hx
  have hN : GlobalTheory.IsNormalScheme X := .of_pred hXn
  have e₀ : (b ⁻¹ᵁ U).ι ≫ b = b ∣_ U ≫ U.ι := (morphismRestrict_ι b U).symm
  have : IsOpenImmersion ((b ⁻¹ᵁ U).ι ≫ b) := by rw [e₀]; infer_instance
  have : Flat ((b ⁻¹ᵁ U).ι ≫ b ≫ s) := by rw [← Category.assoc]; infer_instance
  have hV : GlobalTheory.IsNormalScheme (b ⁻¹ᵁ U).toScheme := .of_isOpenImmersion ((b ⁻¹ᵁ U).ι ≫ b)
  obtain ⟨N, ν, hfin, hn, hpr, hfl, hν, hd⟩ :=
    GlobalTheory.ProjBlowup.exists_normal_model (b ≫ s) (b ⁻¹ᵁ U) hbs hV.pred fun x => by
      have hy : ((b ⁻¹ᵁ U).ι ≫ b) x ∈ U := x.2
      have := charZero_residueField V p hp s _ hy
      exact charZero_of_injective_ringHom (((b ⁻¹ᵁ U).ι ≫ b).residueFieldMap x).hom.injective
  have hνb : IsIso ((ν ≫ b) ∣_ U) := by
    rw [morphismRestrict_comp]; exact IsIso.comp_isIso' hν hbU
  have : IsFinite ν := hfin
  have : IsSeparated s := by
    obtain ⟨n, i, hi, rfl⟩ := hXp
    have := isProper_str V n
    infer_instance
  have : IsProper (b ≫ s) := by
    obtain ⟨n, i, hi, e⟩ := hbs
    have := isProper_str V n
    rw [← e]
    infer_instance
  have : IsProper b := IsProper.of_comp b s

  have hUne : (U : Set X).Nonempty := by
    obtain x := Classical.arbitrary X
    let g₀ : Sp V := (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum V)
    have hg₀s : g₀ ⤳ s x := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    obtain ⟨x', -, hx'⟩ := Flat.generalizingMap s hg₀s
    refine ⟨x', ?_⟩
    change x' ∈ X.basicOpen (p : Γ(X, ⊤))
    rw [← preimage_basicOpen_natCast p s]
    change s x' ∈ (Sp V).basicOpen (p : Γ(Sp V, ⊤))
    rw [hx']
    have hp0 : (p : V) ≠ 0 := fun h => by
      have h' : ((p : V) : F) = 0 := by rw [h]; rfl
      push_cast at h'
      exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h')
    have e : (p : Γ(Sp V, ⊤)) = (Scheme.ΓSpecIso (CommRingCat.of V)).inv (p : V) := by simp
    rw [e, basicOpen_eq_of_affine]
    exact hp0
  have : Nonempty U := hUne.to_subtype
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  obtain ⟨j, hj, hjr⟩ := GlobalTheory.ProjBlowup.exists_section_of_isIso_restrict (ν ≫ b) U
  have hjd : Dense (Set.range j) := hd.mono hjr
  have hirr : IsIrreducible (Set.range j) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image j j.continuous.continuousOn
  have : IrreducibleSpace N := (irreducibleSpace_def N).2 (by simpa [hjd.closure_eq] using hirr.closure)
  have : GlobalTheory.IsNormalScheme N := .of_pred hn
  have : IsReduced N := isReduced_of_isReduced_stalk N
  have : IsIntegral N := isIntegral_of_irreducibleSpace_of_isReduced N
  exact ⟨X'', N, b, ν, hb.1, inferInstance, hn, hpr, hfl, inferInstance, hνb⟩
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blowup_normalization_cartier : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime],
    (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V), IsIntegral X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X →
    IsProjOver s → Flat s → ∀ J : X.IdealSheafData, (∀ x ∈ J.support, x ∉ X.basicOpen (p : Γ(X, ⊤))) →
    ∃ (X'' X' : Scheme.{0}) (b : X'' ⟶ X) (ν : X' ⟶ X''), ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap b) ∧
      IsIntegral X' ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' ∧ IsProjOver (ν ≫ b ≫ s) ∧ Flat (ν ≫ b ≫ s) ∧
      IsProper (ν ≫ b) ∧ IsIso ((ν ≫ b) ∣_ X.basicOpen (p : Γ(X, ⊤))) := by
  atlas_forward_decl GlobalTheory.FlatModel.exists_normBlowup_off_basicOpen
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
namespace GlobalTheory.FlatModel

theorem field_pt_eq_bot {K : Type} [Field K] (z : Sp K) : z = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) :=
  by haveI := z.isPrime; exact PrimeSpectrum.ext (Ideal.eq_bot_of_prime _)

theorem isTest_lift (p : ℕ) [Fact p.Prime] (X X' : Scheme.{0}) (π : X' ⟶ X) (hπ : IsProper π) (Xw O : X.Opens)
    (hO : Xw ≤ O) (hiso : IsIso (π ∣_ O)) (yb : Sp 𝓞_ℂ_[p] ⟶ X) (hyb : IsTest p Xw yb) :
    ∃ yb', IsTest p (π ⁻¹ᵁ Xw) yb' ∧ yb' ≫ π = yb := by
  obtain ⟨⟨T, kO, yT, hfin, hinj, hyT⟩, hrange⟩ := hyb
  have hgen : yT (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.V) ∈ Xw := by
    have h1 := hrange ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ_[p]), rfl⟩
    rw [bot_map (FaithfulSMul.algebraMap_injective 𝓞_ℂ_[p] ℂ_[p]), ← hyT, bot_map hinj] at h1
    exact h1
  set y : Sp T.Fr ⟶ X := spMap (algebraMap T.V T.Fr) ≫ yT with hy
  have hyO : Set.range y ⊆ (O : Set X) := by
    rintro _ ⟨z, rfl⟩
    rw [field_pt_eq_bot z, hy, bot_map (IsFractionRing.injective T.V T.Fr)]
    exact hO hgen
  have hr : Set.range y ⊆ Set.range O.ι := by rw [Scheme.Opens.range_ι]; exact hyO
  let y₀ : Sp T.Fr ⟶ O := IsOpenImmersion.lift O.ι y hr
  let y' : Sp T.Fr ⟶ X' := y₀ ≫ inv (π ∣_ O) ≫ (π ⁻¹ᵁ O).ι
  have hy' : y' ≫ π = spMap (algebraMap T.V T.Fr) ≫ yT := by
    simp only [y', Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc, y₀, IsOpenImmersion.lift_fac]
    exact hy
  haveI : ValuationRing T.V := inferInstance
  obtain ⟨yT', -, hyT'⟩ := valuative_lift_of_isProper π y' yT hy'
  refine ⟨spMap kO ≫ yT', ⟨⟨T, kO, yT', hfin, hinj, rfl⟩, ?_⟩, by rw [Category.assoc, hyT', hyT]⟩
  rintro _ ⟨z, rfl⟩
  show π _ ∈ Xw
  have := hrange ⟨z, rfl⟩
  rw [← hyT, ← hyT'] at this
  simp only [Scheme.Hom.comp_apply, Category.assoc] at this
  exact this

end GlobalTheory.FlatModel
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_point_lift_proper : ∀ (p : ℕ) [Fact p.Prime] (X X' : Scheme.{0}) (π : X' ⟶ X), IsProper π → ∀ (Xw O : X.Opens), Xw ≤ O →
    IsIso (π ∣_ O) → ∀ yb : Sp 𝓞_ℂ_[p] ⟶ X, IsTest p Xw yb → ∃ yb', IsTest p (π ⁻¹ᵁ Xw) yb' ∧ yb' ≫ π = yb := by
  atlas_forward_decl GlobalTheory.FlatModel.isTest_lift
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
namespace GlobalTheory.FlatModel

theorem geomIrr_preimage_of_isIso_restrict (V : Type) [CommRing V] (X X' : Scheme.{0}) (s : X ⟶ Sp V) (π : X' ⟶ X)
    (Xw O : X.Opens) (hle : Xw ≤ O) (hiso : IsIso (π ∣_ O)) (hg : GeomIrr s Xw) :
    GeomIrr (π ≫ s) (π ⁻¹ᵁ Xw) := by
  have h1 : IsIso ((π ∣_ O) ∣_ (O.ι ⁻¹ᵁ Xw)) :=
    IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme) hiso _
  have h2 : IsIso (π ∣_ (O.ι ''ᵁ (O.ι ⁻¹ᵁ Xw))) :=
    ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff (morphismRestrictRestrict π O (O.ι ⁻¹ᵁ Xw))).mp h1
  have e : O.ι ''ᵁ (O.ι ⁻¹ᵁ Xw) = Xw := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hle
  rw [e] at h2
  intro k _ f hf
  haveI := hg k f hf
  have hcomm : (π ⁻¹ᵁ Xw).ι ≫ π ≫ s = (π ∣_ Xw) ≫ Xw.ι ≫ s := by
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  let m := pullback.map ((π ⁻¹ᵁ Xw).ι ≫ π ≫ s) (spMap f) (Xw.ι ≫ s) (spMap f) (π ∣_ Xw) (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, hcomm]) (by simp)
  haveI : IsIso m := pullback.map_isIso _ _ _ _ _ _ _ _ _
  let H := Scheme.homeoOfIso (asIso m)
  exact Function.Surjective.irreducibleSpace H.symm.continuous H.symm.surjective

end GlobalTheory.FlatModel
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometrically_irreducible_pullback_iso : ∀ (V : Type) [CommRing V] (X X' : Scheme.{0}) (s : X ⟶ Sp V) (π : X' ⟶ X) (Xw O : X.Opens),
    Xw ≤ O → IsIso (π ∣_ O) → GeomIrr s Xw → GeomIrr (π ≫ s) (π ⁻¹ᵁ Xw) := by
  atlas_forward_decl GlobalTheory.FlatModel.geomIrr_preimage_of_isIso_restrict
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
namespace GlobalTheory.FlatModel

theorem unitChartAt_of_mem_basicOpen_p : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (Xw : X.Opens)
    (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (x : X),
    x ∈ X.basicOpen (p : Γ(X, ⊤)) → UnitChartAt p Xw K x := by
  intro p _ X Xw K x hx
  obtain ⟨W', hW', hxW, hWle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx
  have hW'a : IsAffineOpen W' := hW'
  refine ⟨Γ(X, W'), inferInstance, hW'a.fromSpec, 1, inferInstance, ?_, ?_⟩
  · rw [hW'a.range_fromSpec]; exact hxW
  · intro φ _
    exfalso
    have hu : IsUnit ((p : ℕ) : Γ(X, W')) := by
      have := (X.toRingedSpace.isUnit_res_basicOpen (p : Γ(X, ⊤))).map
        (X.presheaf.map (homOfLE hWle).op).hom
      simp only [map_natCast] at this
      erw [map_natCast] at this
      exact this
    have h2 := hu.map φ
    rw [map_natCast] at h2
    exact GlobalTheory.PadicComplexHost.not_isUnit_p p h2

end GlobalTheory.FlatModel
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_chart_at_invertible_p : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (x : X),
    x ∈ X.basicOpen (p : Γ(X, ⊤)) → UnitChartAt p Xw K x := by
  atlas_forward_decl GlobalTheory.FlatModel.unitChartAt_of_mem_basicOpen_p
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
namespace GlobalTheory.FlatModel

theorem chart_sections_factor : ∀ (X : Scheme.{0}) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) [IsOpenImmersion ξ],
    ∃ e : R →+* Γ(X, ξ.opensRange), ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (V : Y.Opens) (hV : IsAffineOpen V)
      (hVU : V ≤ f ⁻¹ᵁ ξ.opensRange), hV.fromSpec ≫ f = spMap ((f.appLE ξ.opensRange V hVU).hom.comp e) ≫ ξ := by
  intro X R _ ξ _
  have hU : IsAffineOpen ξ.opensRange := isAffineOpen_opensRange ξ
  have hr : Set.range hU.fromSpec.base ⊆ Set.range ξ.base := by
    rw [hU.range_fromSpec]; simp
  refine ⟨(Spec.preimage (IsOpenImmersion.lift ξ hU.fromSpec hr)).hom, ?_⟩
  intro Y f V hV hVU
  rw [← hU.SpecMap_appLE_fromSpec f hV hVU]
  conv_lhs => rw [← IsOpenImmersion.lift_fac ξ hU.fromSpec hr]
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom, Spec.map_preimage]

end GlobalTheory.FlatModel
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_immersion_ring_factor : ∀ (X : Scheme.{0}) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) [IsOpenImmersion ξ],
    ∃ e : R →+* Γ(X, ξ.opensRange), ∀ (Y : Scheme.{0}) (f : Y ⟶ X) (V : Y.Opens) (hV : IsAffineOpen V)
      (hVU : V ≤ f ⁻¹ᵁ ξ.opensRange), hV.fromSpec ≫ f = spMap ((f.appLE ξ.opensRange V hVU).hom.comp e) ≫ ξ := by
  atlas_forward_decl GlobalTheory.FlatModel.chart_sections_factor
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem unitChartAt_of_dvd : ∀ (p n : ℕ) [Fact p.Prime] (X X' : Scheme.{0}) (π : X' ⟶ X) (Xw : X.Opens)
    (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (J : Type) (Q : J → R)
    (u : ∀ j, (Localization.Away ((p : R) * Q j))ˣ),
    (∀ φ : R →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ) → (∃ j, (p : ℝ)⁻¹ ^ n < ‖(φ (Q j) : ℂ_[p])‖) ∧
      ∀ j, (p : ℝ)⁻¹ ^ n < ‖(φ (Q j) : ℂ_[p])‖ → ∀ ψ : Localization.Away ((p : R) * Q j) →+* ℂ_[p],
        ψ.comp (algebraMap R _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ →
          ∀ κ ∈ K (spMap φ ≫ ξ), ‖ψ (u j) - κ‖ < ‖κ‖) →
    (∀ yb' : Sp 𝓞_ℂ_[p] ⟶ X', IsTest p (π ⁻¹ᵁ Xw) yb' → IsTest p Xw (yb' ≫ π)) →
    ∀ (R' : Type) [CommRing R'] (χ : Sp R' ⟶ X') (g : R →+* R') (x' : X'), IsOpenImmersion χ → x' ∈ Set.range χ →
      χ ≫ π = spMap g ≫ ξ →
      (((π ⁻¹ᵁ Xw : X'.Opens) : Set X').Nonempty → ∃ φ : R' →+* 𝓞_ℂ_[p], IsTest p (π ⁻¹ᵁ Xw) (spMap φ ≫ χ)) →
      ((∃ k, (∀ j, g (Q k) ∣ g (Q j)) ∧ g (Q k) ∣ (p : R') ^ n) ∨ ∀ j, (p : R') ^ n ∣ g (Q j)) →
      UnitChartAt p (π ⁻¹ᵁ Xw) (fun yb' => K (yb' ≫ π)) x' := by
  intro p n _ X X' π Xw K R _ ξ J Q u hC hT R' _ χ g x' hχ hx' hχπ _hD hcase
  have hcomp : ∀ φ : R' →+* 𝓞_ℂ_[p], (spMap φ ≫ χ) ≫ π = spMap (φ.comp g) ≫ ξ := by
    intro φ; rw [Category.assoc, hχπ, sp_sp]
  have hm : ∀ x : 𝓞_ℂ_[p], ‖(x : ℂ_[p])‖ ≤ 1 := fun x => by
    have this : (Valued.v (x : ℂ_[p]) : NNReal) ≤ 1 := x.2
    rw [PadicComplex.norm_eq_norm]
    exact (Valued.toNormedField.norm_le_one_iff).2 this
  have hpn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    have : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := by simp
    rw [this, norm_algebraMap', Padic.norm_p]
  have htest : ∀ φ : R' →+* 𝓞_ℂ_[p], IsTest p (π ⁻¹ᵁ Xw) (spMap φ ≫ χ) →
      IsTest p Xw (spMap (φ.comp g) ≫ ξ) := by
    intro φ h; rw [← hcomp]; exact hT _ h
  rcases hcase with ⟨k, hk, hkp⟩ | hall
  · have hunit : IsUnit ((algebraMap R' (Localization.Away (p : R'))).comp g ((p : R) * Q k)) := by
      obtain ⟨d, hd⟩ := hkp
      have h1 : IsUnit (algebraMap R' (Localization.Away (p : R')) ((p : R') ^ (n + 1))) := by
        rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit (p : R')).pow _
      refine isUnit_of_dvd_unit ⟨algebraMap R' _ d, ?_⟩ h1
      simp only [RingHom.comp_apply, map_mul, map_natCast]
      rw [pow_succ', hd, map_mul, map_mul, map_natCast]; ring
    let L := IsLocalization.Away.lift (S := Localization.Away ((p : R) * Q k)) ((p : R) * Q k) hunit
    refine ⟨R', inferInstance, χ, Units.map L.toMonoidHom (u k), hχ, hx', ?_⟩
    intro φ hφ ψ hψ κ hκ
    obtain ⟨⟨j, hj⟩, hcl⟩ := hC (φ.comp g) (htest φ hφ)
    have hkbig : (p : ℝ)⁻¹ ^ n < ‖((φ.comp g) (Q k) : ℂ_[p])‖ := by
      refine hj.trans_le ?_
      obtain ⟨d, hd⟩ := hk j
      have e : (((φ.comp g) (Q j) : 𝓞_ℂ_[p]) : ℂ_[p]) = ((φ.comp g) (Q k) : ℂ_[p]) * (φ d : ℂ_[p]) := by
        rw [RingHom.comp_apply, hd, map_mul]; rfl
      rw [e, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hm _)
    have hcompat : (ψ.comp L).comp (algebraMap R (Localization.Away ((p : R) * Q k))) =
        (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (φ.comp g) := by
      ext r
      have := RingHom.congr_fun hψ (g r)
      simp only [RingHom.comp_apply] at this ⊢
      rw [← this]
      congr 1
      exact IsLocalization.lift_eq _ r
    have hκ' : κ ∈ K (spMap (φ.comp g) ≫ ξ) := by rw [← hcomp]; exact hκ
    exact hcl k hkbig (ψ.comp L) hcompat κ hκ'
  · refine ⟨R', inferInstance, χ, 1, hχ, hx', ?_⟩
    intro φ hφ
    exfalso
    obtain ⟨⟨j, hj⟩, -⟩ := hC (φ.comp g) (htest φ hφ)
    obtain ⟨d, hd⟩ := hall j
    have e : (((φ.comp g) (Q j) : 𝓞_ℂ_[p]) : ℂ_[p]) = (p : ℂ_[p]) ^ n * (φ d : ℂ_[p]) := by
      rw [RingHom.comp_apply, hd, map_mul, map_pow, map_natCast]; push_cast; rfl
    rw [e, norm_mul, norm_pow, hpn] at hj
    have := mul_le_of_le_one_right (pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg p) : (0:ℝ) ≤ (p : ℝ)⁻¹) n) (hm (φ d))
    linarith

end GlobalTheory.FlatModel
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_units_charts : ∀ (p n : ℕ) [Fact p.Prime] (X X' : Scheme.{0}) (π : X' ⟶ X) (Xw : X.Opens)
    (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (J : Type) (Q : J → R)
    (u : ∀ j, (Localization.Away ((p : R) * Q j))ˣ),
    (∀ φ : R →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ) → (∃ j, (p : ℝ)⁻¹ ^ n < ‖(φ (Q j) : ℂ_[p])‖) ∧
      ∀ j, (p : ℝ)⁻¹ ^ n < ‖(φ (Q j) : ℂ_[p])‖ → ∀ ψ : Localization.Away ((p : R) * Q j) →+* ℂ_[p],
        ψ.comp (algebraMap R _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ →
          ∀ κ ∈ K (spMap φ ≫ ξ), ‖ψ (u j) - κ‖ < ‖κ‖) →
    (∀ yb' : Sp 𝓞_ℂ_[p] ⟶ X', IsTest p (π ⁻¹ᵁ Xw) yb' → IsTest p Xw (yb' ≫ π)) →
    ∀ (R' : Type) [CommRing R'] (χ : Sp R' ⟶ X') (g : R →+* R') (x' : X'), IsOpenImmersion χ → x' ∈ Set.range χ →
      χ ≫ π = spMap g ≫ ξ →
      (((π ⁻¹ᵁ Xw : X'.Opens) : Set X').Nonempty → ∃ φ : R' →+* 𝓞_ℂ_[p], IsTest p (π ⁻¹ᵁ Xw) (spMap φ ≫ χ)) →
      ((∃ k, (∀ j, g (Q k) ∣ g (Q j)) ∧ g (Q k) ∣ (p : R') ^ n) ∨ ∀ j, (p : R') ^ n ∣ g (Q j)) →
      UnitChartAt p (π ⁻¹ᵁ Xw) (fun yb' => K (yb' ≫ π)) x' := by
  atlas_forward_decl GlobalTheory.FlatModel.unitChartAt_of_dvd
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel.Modif

theorem isTest_comp (p : ℕ) [Fact p.Prime] {X X' : Scheme.{0}} (π : X' ⟶ X) (Xw : X.Opens)
    (yb' : Sp 𝓞_ℂ_[p] ⟶ X') (h : IsTest p (π ⁻¹ᵁ Xw) yb') : IsTest p Xw (yb' ≫ π) := by
  obtain ⟨⟨T, kO, yT, hT, hk, e⟩, hr⟩ := h
  refine ⟨⟨T, kO, yT ≫ π, hT, hk, by rw [← Category.assoc, e]⟩, ?_⟩
  rintro _ ⟨z, rfl⟩
  have : (spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb') z ∈ π ⁻¹ᵁ Xw := hr ⟨z, rfl⟩
  simpa [Scheme.Hom.comp_apply] using this

theorem preimage_basicOpen_p (p : ℕ) {X X' : Scheme.{0}} (π : X' ⟶ X) :
    π ⁻¹ᵁ X.basicOpen (p : Γ(X, ⊤)) = X'.basicOpen (p : Γ(X', ⊤)) := by
  rw [Scheme.preimage_basicOpen, map_natCast]
  rfl

end GlobalTheory.FlatModel.Modif

namespace GlobalTheory.FlatModel

open Modif

theorem modSt_of_densSt : DensSt → ModSt := by
  intro hD F _ _ V p _ hp X s Xw hXi hXn hXp hXf hXw hGI n K hK hC
  have hDVR := (GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField V (Fact.out : p.Prime).ne_zero hp).1
  have : LocallyOfFiniteType s := by
    obtain ⟨N, i, hi, rfl⟩ := hXp
    have := isProper_str V N
    infer_instance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace X := by
    obtain ⟨N, i, hi, rfl⟩ := hXp
    have := isProper_str V N
    exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str V N)
  choose R _ ξ J _ Q u hξ hx hcl using hC
  haveI : ∀ x, IsOpenImmersion (ξ x) := hξ
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (fun x => ((ξ x).opensRange : Set X))
    fun x => (ξ x).opensRange.isOpen.mem_nhds (by simpa using hx x)
  choose e he using fun x => GlobalTheory.T.open_immersion_ring_factor X (R x) (ξ x)
  let U : t → X.Opens := fun j => (ξ j.1).opensRange
  let m : t → ℕ := fun j => Nat.card (J j.1) + 1
  let A : ∀ j : t, Fin (m j) → Γ(X, U j) := fun j =>
    Fin.cons ((p : Γ(X, U j)) ^ n) fun i => e j.1 (Q j.1 ((Finite.equivFin (J j.1)).symm i))
  obtain ⟨Jd, hJd, hPr⟩ := GlobalTheory.HTLine.princ_of_finite X p U m A (fun j => isAffineOpen_opensRange (ξ j.1))
    fun j => ⟨n, Ideal.subset_span ⟨0, rfl⟩⟩
  obtain ⟨X'', X', b, ν, hEff, hI', hN', hP', hF', hpr, hiso⟩ := GlobalTheory.T.exists_blowup_normalization_cartier F V p hp X s hXi hXn hXp hXf Jd hJd
  have hT : ∀ yb', IsTest p ((ν ≫ b) ⁻¹ᵁ Xw) yb' → IsTest p Xw (yb' ≫ (ν ≫ b)) := isTest_comp p (ν ≫ b) Xw
  have hle : (ν ≫ b) ⁻¹ᵁ Xw ≤ X'.basicOpen (p : Γ(X', ⊤)) := by
    rw [← preimage_basicOpen_p p (ν ≫ b)]
    exact fun x hx => hXw hx
  have : LocallyOfFiniteType (ν ≫ b ≫ s) := by
    obtain ⟨N, i, hi, e'⟩ := hP'
    have := isProper_str V N
    rw [← e']
    infer_instance
  refine ⟨X', ν ≫ b ≫ s, (ν ≫ b) ⁻¹ᵁ Xw, fun yb' => K (yb' ≫ (ν ≫ b)), hI', hN', hP', hF', hle, ?_,
    fun yb' h => hK _ (hT yb' h), ?_, fun yb h => ?_⟩
  · have := GlobalTheory.T.geometrically_irreducible_pullback_iso V X X' s (ν ≫ b) Xw _ hXw hiso hGI
    simpa only [Category.assoc] using this
  · intro x'
    by_cases hx' : x' ∈ X'.basicOpen (p : Γ(X', ⊤))
    · exact GlobalTheory.T.unit_chart_at_invertible_p p X' _ _ x' hx'
    have hmem : (ν ≫ b) x' ∈ ⋃ x ∈ t, ((ξ x).opensRange : Set X) := by rw [ht]; exact Set.mem_univ _
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨x, hxt, hfx⟩ := hmem
    obtain ⟨V', hV', hxV', hVa, k, hk⟩ := hPr X'' X' b ν hEff x' ⟨x, hxt⟩ hfx
    have heq := he x X' (ν ≫ b) V' hVa hV'
    refine GlobalTheory.T.localization_units_charts p n X X' (ν ≫ b) Xw K (R x) (ξ x) (J x) (Q x) (u x) (hcl x) hT Γ(X', V') hVa.fromSpec
      _ x' inferInstance (by rw [hVa.range_fromSpec]; exact hxV') heq
      (fun hne => hD F V p hp X' (ν ≫ b ≫ s) _ hI' hF' inferInstance hle hne Γ(X', V') hVa.fromSpec inferInstance
        ⟨x', by rw [hVa.range_fromSpec]; exact hxV', hx'⟩) ?_
    have hA0 : ((ν ≫ b).appLE (ξ x).opensRange V' hV').hom ((p : Γ(X, (ξ x).opensRange)) ^ n) =
        (p : Γ(X', V')) ^ n := by rw [map_pow, map_natCast]
    revert hk
    refine Fin.cases (fun hk => Or.inr fun j => ?_) (fun i hk => Or.inl ⟨(Finite.equivFin (J x)).symm i,
      fun j => ?_, ?_⟩) k
    · have := hk ((Finite.equivFin (J x)) j).succ
      simpa [A, U, hA0] using this
    · have := hk ((Finite.equivFin (J x)) j).succ
      simpa [A, U] using this
    · have := hk 0
      simpa [A, U, hA0] using this
  · obtain ⟨yb', h1, h2⟩ := GlobalTheory.T.test_point_lift_proper p X X' (ν ≫ b) hpr Xw _ hXw hiso yb h
    exact ⟨yb', h1, fun κ hκ => by show κ ∈ K (yb' ≫ (ν ≫ b)); rw [h2]; exact hκ⟩

end GlobalTheory.FlatModel
end
end

open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularity_of_density : DensSt → ModSt := by
  atlas_forward_decl GlobalTheory.FlatModel.modSt_of_densSt
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem glueSt_of (hC : ConnSt) (hZ : GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.PropZ) : GlueSt := by
  intro F _ _ V p _ hp X s Xw hN hP hF hXw hG n K hK hCh
  obtain ⟨X₁, s₁, Xw₁, K₁, hI₁, hN₁, hP₁, hF₁, hXw₁, hG₁, hK₁, hCh₁, hT₁⟩ :=
    GlobalTheory.T.restriction_statement_holds F V p hp X s Xw hN hP hF hXw hG n K hK hCh
  obtain ⟨X₂, s₂, Xw₂, K₂, hI₂, hN₂, hP₂, hF₂, hXw₂, hG₂, hK₂, hCh₂, hT₂⟩ :=
    GlobalTheory.T.modularity_of_density GlobalTheory.T.density_statement_holds F V p hp X₁ s₁ Xw₁ hI₁ hN₁ hP₁ hF₁ hXw₁ hG₁ n K₁ hK₁ hCh₁
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.principal_of_connected_density hC hZ GlobalTheory.T.density_statement_holds F V p hp X₂ s₂ Xw₂ hI₂ hN₂ hP₂ hF₂ hXw₂ hG₂ K₂ hK₂ hCh₂
  refine ⟨ρ, fun yb hyb κ hκ => ?_⟩
  obtain ⟨yb₁, h1, hs1⟩ := hT₁ yb hyb
  obtain ⟨yb₂, h2, hs2⟩ := hT₂ yb₁ h1
  exact hρ yb₂ h2 κ (hs2 (hs1 hκ))

end GlobalTheory.FlatModel
end
end

open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluing_of_connectedness : ConnSt → GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.PropZ → GlueSt := by
  atlas_forward_decl GlobalTheory.FlatModel.glueSt_of
end
