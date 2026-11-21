import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFanOrderIdealGluedClopenPieces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleComponentsClopenPartition
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalModelCartierDivisorThetaSetup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDescendingDivisorPowerThetaSetup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExistsAfterFiniteExtensionOfCompleteDVRStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitLatticesIsoFormsProportionalRamificationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongComapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtPointLiftOfSurjectiveLocFinType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrIntegralClosureFiniteFractionRi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperLiftTraitOfGenericLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealMapEqSpanPowUniformizerDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimAddRank
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLiftThetaSetupModelAfterExtension
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelSmoothOfRelativeDimensionCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDescentIdealSheafFiniteOpenClosedImage

section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fanOrder_ideal_glued_clopen_pieces : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (j : F.X ⟶ S) (φ : InvFun ℤ) {ι : Type} [Fintype ι] (W : ι → Set S) (J : ι → S.IdealSheafData) (d : ι → ℕ), (∀ c, IsClopen (W c)) → (∀ x, ∃! c, x ∈ W c) → (∀ c, 1 ≤ d c) → (∀ c, ∀ x ∈ (J c).support, x ∈ W c ∧ x ∉ Set.range j) → (∀ c (T : Trait F) (ξ : Sp T.V ⟶ S), jK T.V ≫ ξ = T.y ≫ j → ξ (closedPoint T.V) ∈ W c → ∃ a : ℕ, (a : ℝ) = d c * φ.evalZ T.β ∧ idlAlong (J c) ξ = Ideal.span {T.ϖ ^ a}) → ∃ (d' : ℕ) (J' : S.IdealSheafData), 1 ≤ d' ∧ (∀ x ∈ J'.support, x ∉ Set.range j) ∧ ValOn F j φ J' d' := by
  first | exact @GlobalTheory.Poinc.exists_valOn_of_pieces | exact GlobalTheory.Poinc.exists_valOn_of_pieces | (intros; apply GlobalTheory.Poinc.exists_valOn_of_pieces <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_clopen_irreducible_partition_of_normal_proj : ∀ (n : ℕ) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)), IsProjOver z → GlobalTheory.IsNormalScheme Z → ∃ (ι : Type) (_ : Fintype ι) (W : ι → Set Z), (∀ c, IsClopen (W c)) ∧ (∀ c, IsIrreducible (W c)) ∧ ∀ x, ∃! c, x ∈ W c := by
  first | exact @GlobalTheory.irreducibleComponents_clopen_partition | exact GlobalTheory.irreducibleComponents_clopen_partition | (intros; apply GlobalTheory.irreducibleComponents_clopen_partition <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory

theorem exists_mem_genericPoints_closure_eq_of_isClopen :
    ∀ (X Z : Scheme.{0}) (i : X ⟶ Z), IsOpenImmersion i → Dense (Set.range i) → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∃ η ∈ genericPoints X, closure {i η} = W := by
  intro X Z i hi hd W hWc hWi
  have he : Topology.IsOpenEmbedding i := i.isOpenEmbedding

  have hgen : IsGenericPoint hWi.genericPoint W :=
    hWi.isGenericPoint_genericPoint hWc.isClosed
  have hne : (W ∩ Set.range i).Nonempty :=
    hd.inter_open_nonempty W hWc.isOpen hWi.nonempty
  have hmem : hWi.genericPoint ∈ Set.range i :=
    (hgen.mem_open_set_iff he.isOpen_range).2 hne
  obtain ⟨η, hη⟩ := hmem
  have hcl : closure {i η} = W := by rw [hη]; exact hgen
  refine ⟨η, ?_, hcl⟩

  have hpre : closure ({η} : Set X) = i ⁻¹' W := by
    rw [← hcl, he.isOpenMap.preimage_closure_eq_closure_preimage he.continuous,
      ← Set.image_singleton, he.injective.preimage_image]
  show closure ({η} : Set X) ∈ irreducibleComponents X
  have hirr : IsIrreducible (closure ({η} : Set X)) := isIrreducible_singleton.closure
  have hclo : IsClopen (closure ({η} : Set X)) := by
    rw [hpre]; exact hWc.preimage he.continuous
  refine ⟨hirr, fun T hT hsub => ?_⟩
  refine hT.2.isPreconnected.subset_isClopen hclo ?_
  exact ⟨η, hsub (subset_closure rfl), subset_closure rfl⟩

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem Setup.range_π_eq : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W8 i) (η : F.X) (W : Set Z), (∀ w, (spMap X₁.S.R.val.toRingHom ≫ X₁.u) w = η) → closure {i η} = W → Set.range X₁.π = W := by
  intro g n F W8 Z i X₁ η W hη hW
  haveI := X₁.fin
  have hc : IsClosedMap X₁.π.base := X₁.π.isClosedMap
  let w₀ : Sp X₁.Ω₁ := IsLocalRing.closedPoint X₁.Ω₁
  have hgen : X₁.M.pt w₀ = genericPoint X₁.M.Z := X₁.M.pt_apply w₀
  have hpt : X₁.π (X₁.M.pt w₀) = i η := by
    have h := congrArg (fun f => f.base w₀) X₁.comp
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    rw [← hη w₀]
    simpa using h
  have huniv : closure ({genericPoint X₁.M.Z} : Set X₁.M.Z) = Set.univ := genericPoint_spec X₁.M.Z
  rw [← hW, ← hpt, hgen, ← Set.image_singleton, ← Set.image_univ, ← huniv]
  exact (hc.closure_image_eq_of_continuous X₁.π.continuous _).symm

end GlobalTheory.Poinc
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_model_cartierDivisor_thetaSetup : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W8 : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W8 → ThetaInt F W8 i → ∀ X₁ : Setup F W8 i, ∃ (ι : ℕ) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (D : GlobalTheory.EffCartierData Y.Z), 1 ≤ ι ∧ X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY ∧ IsProper πY ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y.Z ∧ (∀ y ∈ D.idealSheaf.support, X₁.π (πY y) ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a} := by
  first | exact @GlobalTheory.Poinc.exists_model_divisor_of_orders | exact GlobalTheory.Poinc.exists_model_divisor_of_orders | (intros; apply GlobalTheory.Poinc.exists_model_divisor_of_orders <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteExt_point_lift_of_surjective_locFinType : ∀ {X Y : Scheme.{0}} (π : Y ⟶ X), LocallyOfFiniteType π → Function.Surjective π → ∀ (K : Type) [Field K] (x : Sp K ⟶ X), ∃ (K' : Type) (_ : Field K') (σ : K →+* K') (y : Sp K' ⟶ Y), σ.Finite ∧ y ≫ π = spMap σ ≫ x := by
  first | exact @GlobalTheory.exists_finite_ext_point_lift_of_surjective_lft | exact GlobalTheory.exists_finite_ext_point_lift_of_surjective_lft | (intros; apply GlobalTheory.exists_finite_ext_point_lift_of_surjective_lft <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complete_dvr_integralClosure_finite_fractionRing : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (K' : Type) [Field K'] (σ : FractionRing V →+* K'), σ.Finite → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V') (f : V →+* V') (τ : K' →+* FractionRing V'), IsAdicComplete (maximalIdeal V') V' ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧ ∀ a, τ (σ (algebraMap V _ a)) = algebraMap V' _ (f a) := by
  first | exact @GlobalTheory.exists_complete_dvr_of_finite_fractionRing_hom | exact GlobalTheory.exists_complete_dvr_of_finite_fractionRing_hom | (intros; apply GlobalTheory.exists_complete_dvr_of_finite_fractionRing_hom <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_lift_trait_of_generic_lift : ∀ {X Y : Scheme.{0}} (π : Y ⟶ X), IsProper π → ∀ (V V' : Type) [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (f : V →+* V') (fK : FractionRing V →+* FractionRing V'), (∀ a, fK (algebraMap V _ a) = algebraMap V' _ (f a)) → ∀ (ξ : Sp V ⟶ X) (y : Sp (FractionRing V') ⟶ Y), y ≫ π = spMap fK ≫ jK V ≫ ξ → ∃ ξ' : Sp V' ⟶ Y, ξ' ≫ π = spMap f ≫ ξ ∧ jK V' ≫ ξ' = y := by
  first | exact @GlobalTheory.proper_lift_trait | exact GlobalTheory.proper_lift_trait | (intros; apply GlobalTheory.proper_lift_trait <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_map_eq_span_pow_uniformizer_dvr : ∀ (V W : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (f : V →+* W), Function.Injective f → ∀ (ϖ : V) (w : W) (e a : ℕ) (I : Ideal V), Irreducible ϖ → Irreducible w → Associated (f ϖ) (w ^ e) → I.map f = Ideal.span {w ^ a} → ∃ b : ℕ, e * b = a ∧ I = Ideal.span {ϖ ^ b} := by
  first | exact @GlobalTheory.ideal_map_eq_span_pow_uniformizer | exact GlobalTheory.ideal_map_eq_span_pow_uniformizer | (intros; apply GlobalTheory.ideal_map_eq_span_pow_uniformizer <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.Poinc.ideal_orders_of_proper_model : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (φ : InvFun ℤ) (X₁ : Setup F W8 i) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → IsProper πY → ∀ (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), (∀ y ∈ (J₁.comap πY).support, X₁.π (πY y) ∉ Set.range i) → (∀ (T : Trait F) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong (J₁.comap πY) ξ = Ideal.span {T.ϖ ^ a}) → (∀ (T : Trait F) (k : ℕ), 1 ≤ k → φ.evalZ ((k : ℤ) • T.β) = k * φ.evalZ T.β) → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a} := by
  intro g n F W8 Z i φ X₁ Y πY hhom hprop ι J₁ hsupp hord hφ
  haveI := hprop

  have hsurj : Function.Surjective πY := by
    have hgen : genericPoint X₁.M.Z ∈ Set.range πY := by
      have w : Sp X₁.Ω₁ := IsLocalRing.closedPoint X₁.Ω₁
      refine ⟨Y.pt w, ?_⟩
      have h := congrArg (fun h : Sp X₁.Ω₁ ⟶ X₁.M.Z => h w) (show Y.pt ≫ πY = _ from hhom)
      simp only [Scheme.Hom.comp_apply] at h
      rw [h]
      exact X₁.M.pt_apply _
    have hcl : IsClosed (Set.range πY) := πY.isClosedMap.isClosed_range
    intro x
    have : x ∈ closure (Set.range πY) :=
      closure_mono (Set.singleton_subset_iff.2 hgen) (by rw [genericPoint_spec X₁.M.Z]; trivial)
    rwa [hcl.closure_eq] at this
  refine ⟨fun x hx => ?_, fun T ξ₁ hT => ?_⟩
  · obtain ⟨y, rfl⟩ := hsurj x
    exact hsupp y (by rw [Scheme.IdealSheafData.support_comap]; exact hx)
  ·
    obtain ⟨K', _, σ, yK, hσ, hy⟩ := GlobalTheory.T.exists_finiteExt_point_lift_of_surjective_locFinType πY inferInstance hsurj (FractionRing T.V) (jK T.V ≫ ξ₁)
    obtain ⟨V', _, _, _, _, f, τ, hc', hfi, hfl, hff, hτ⟩ := GlobalTheory.T.exists_complete_dvr_integralClosure_finite_fractionRing T.V T.complete K' σ hσ
    have hfK : ∀ a, (τ.comp σ) (algebraMap T.V _ a) = algebraMap V' _ (f a) := hτ
    obtain ⟨ξ', hξπ, hξg⟩ := GlobalTheory.T.proper_lift_trait_of_generic_lift πY hprop T.V V' f (τ.comp σ) hfK ξ₁ (spMap τ ≫ yK) (by
      rw [Category.assoc, hy, spMap_comp, Category.assoc])
    have hB' : GlobalTheory.Mum.Base V' := ⟨⟨inferInstance, inferInstance, inferInstance, hc'⟩, inferInstance⟩
    obtain ⟨T₂, f₂, fK₂, hf₂i, hf₂l, -, hf₂K, hT₂y⟩ :=
      GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n _ _ F V' hB' inferInstance (spMap (τ.comp σ) ≫ T.y)
    haveI := hfl
    haveI := hf₂l
    have hjK : ∀ {R S : Type} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] (u : R →+* S)
        (uK : FractionRing R →+* FractionRing S), (∀ a, uK (algebraMap R _ a) = algebraMap S _ (u a)) →
        jK S ≫ spMap u = spMap uK ≫ jK R := by
      intro R S _ _ _ _ u uK hu
      change spMap (algebraMap S (FractionRing S)) ≫ spMap u = spMap uK ≫ spMap (algebraMap R (FractionRing R))
      rw [← spMap_comp, ← spMap_comp]
      exact congrArg spMap (RingHom.ext fun a => (hu a).symm)

    have hcomm : jK T₂.V ≫ (spMap f₂ ≫ ξ') ≫ πY ≫ X₁.π = T₂.y ≫ i := by
      have e1 := hjK f₂ fK₂ hf₂K
      calc jK T₂.V ≫ (spMap f₂ ≫ ξ') ≫ πY ≫ X₁.π = (jK T₂.V ≫ spMap f₂) ≫ ξ' ≫ πY ≫ X₁.π := by
            simp only [Category.assoc]
        _ = spMap fK₂ ≫ (jK V' ≫ ξ') ≫ πY ≫ X₁.π := by rw [e1]; simp only [Category.assoc]
        _ = spMap fK₂ ≫ spMap τ ≫ (yK ≫ πY) ≫ X₁.π := by rw [hξg]; simp only [Category.assoc]
        _ = spMap fK₂ ≫ spMap τ ≫ spMap σ ≫ (jK T.V ≫ ξ₁ ≫ X₁.π) := by rw [hy]; simp only [Category.assoc]
        _ = T₂.y ≫ i := by rw [hT, hT₂y, spMap_comp]; simp only [Category.assoc]
    obtain ⟨a', ha', hid⟩ := hord T₂ (spMap f₂ ≫ ξ') hcomm
    rw [GlobalTheory.PullAlong.idlAlong_comap_eq, Category.assoc, hξπ, ← Category.assoc, ← spMap_comp,
      GlobalTheory.TraitOrder.idlAlong_comp] at hid

    set h := f₂.comp f with hh
    have hinj : Function.Injective h := hf₂i.comp hfi
    have hloc : IsLocalHom h := inferInstance
    have hne : h T.ϖ ≠ 0 := (map_ne_zero_iff h hinj).2 T.irr.ne_zero
    obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne T₂.irr
    have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with rfl | hpos
      · exact absurd ((isUnit_map_iff h T.ϖ).1 (he.isUnit_iff.2 (by simp))) T.irr.not_isUnit
      · exact hpos
    obtain ⟨b, hb, hI⟩ := GlobalTheory.T.ideal_map_eq_span_pow_uniformizer_dvr T.V T₂.V h hinj T.ϖ T₂.ϖ e a' _ T.irr T₂.irr he hid

    have hB₂ : GlobalTheory.Mum.Base T₂.V := ⟨⟨inferInstance, inferInstance, inferInstance, T₂.complete⟩, inferInstance⟩
    obtain ⟨eq, heq⟩ := GlobalTheory.T.trait_lattices_iso_forms_proportional_ramification g n _ _ F T T₂ T₂.V h (RingHom.id _) (fK₂.comp (τ.comp σ)) (RingHom.id _)
      hB₂ inferInstance hinj Function.injective_id hloc inferInstance
      (fun a => by rw [RingHom.comp_apply, hfK, hf₂K]; rfl) (fun _ => rfl)
      (by
        rw [hT₂y, spMap_comp, Category.assoc]
        have hid1 : spMap (RingHom.id (FractionRing T₂.V)) = 𝟙 _ := by
          simp [spMap]
        rw [hid1, Category.id_comp]) T₂.ϖ e 1 T₂.irr he (by simp)
    have hval : φ.evalZ T₂.β = e * φ.evalZ T.β := by
      rw [← hφ T e he1]
      unfold InvFun.evalZ
      rw [← φ.eval_equiv eq.toIntLinearEquiv]
      congr 1
      ext a c
      have := heq a c
      simp only [Nat.cast_one, one_mul] at this
      simp [AddEquiv.coe_toIntLinearEquiv, ← this]
    refine ⟨b, ?_, hI⟩
    have h1 : (e : ℝ) * b = e * (ι * φ.evalZ T.β) := by
      rw [← Nat.cast_mul, hb, ha', hval]; ring
    have h2 : (e : ℝ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
    exact mul_left_cancel₀ h2 h1
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.Poinc.exists_setup_ideal_over_component : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∃ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι ∧ Set.range X₁.π = W ∧ (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a} := by
  intro g n hg hn hodd F Z z i hθ φ hφ W hWc hWi
  obtain ⟨hproj, hnorm, hopen, hcomp, hdense, W8, hE8, hTI⟩ := id hθ
  obtain ⟨η, hη, hcl⟩ := GlobalTheory.exists_mem_genericPoints_closure_eq_of_isClopen F.X Z i hopen hdense W hWc hWi
  obtain ⟨X₁, -, hX₁⟩ := GlobalTheory.Poinc.GSetup.exists_setup g n hg hn hodd F Z z i hproj
    (fun x => ⟨hnorm.isDomain_stalk x, hnorm.isIntegrallyClosed_stalk x⟩) hopen hcomp hdense W8 hE8 hTI η hη 0
  have hr := GlobalTheory.Poinc.Setup.range_π_eq g n F W8 Z i X₁ η W hX₁ hcl
  obtain ⟨ι, Y, πY, D, hι, hhom, hprop, hnY, hsupp, hord⟩ := GlobalTheory.T.exists_normal_model_cartierDivisor_thetaSetup g n hg hn hodd F Z z i hθ φ hφ W8 hE8 hTI X₁
  obtain ⟨ι', J₁, hι', hsupp', hord'⟩ :=
    GlobalTheory.T.exists_idealSheaf_descending_divisor_power_thetaSetup g n hg hn hodd F Z z i hθ φ hφ W8 hE8 hTI X₁ ι Y πY D hι X₁.projM hhom hprop hnY hsupp hord
  have hhomog : ∀ (T : Trait F) (k : ℕ), 1 ≤ k → φ.evalZ ((k : ℤ) • T.β) = k * φ.evalZ T.β := by
    intro T k _
    have hrk : Module.finrank ℤ T.D.toPre.X ≤ g := by
      have := GlobalTheory.Poinc.Trait.dim_add_rank (by omega : 2 ≤ n) F T
      omega
    have hβ : T.β ∈ balForms (id : ℤ → ℤ) T.D.toPre.X := ⟨T.symm, fun a y z => by simp⟩
    rw [natCast_zsmul, StrictData.evalZ_eq, StrictData.evalZ_eq, StrictData.toReal_nsmul]
    exact (hφ _ hrk).homog _ (StrictData.toReal_mem_psdCone hβ fun y => T.mono.nonneg 0 y) _ (Nat.cast_nonneg k)
  obtain ⟨hs, ho⟩ := GlobalTheory.Poinc.ideal_orders_of_proper_model g n F W8 Z i φ X₁ Y πY hhom hprop ι' J₁ hsupp' hord' hhomog
  exact ⟨W8, X₁, ι', J₁, hι', hr, hs, ho⟩
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaSetup_ideal_over_clopen_component : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∃ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι ∧ Set.range X₁.π = W ∧ (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a} := by
  atlas_forward_decl GlobalTheory.Poinc.exists_setup_ideal_over_component
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trait_lift_thetaSetup_model_after_extension : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i), IsClopen (Set.range X₁.π) → ∀ (T : Trait F) (ξ : Sp T.V ⟶ Z), jK T.V ≫ ξ = T.y ≫ i → ξ (closedPoint T.V) ∈ Set.range X₁.π → ∃ (T' : Trait F) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V) (ξ₁ : Sp T'.V ⟶ X₁.M.Z), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) ∧ T'.y = spMap fK ≫ T.y ∧ spMap f ≫ ξ = ξ₁ ≫ X₁.π ∧ jK T'.V ≫ ξ₁ ≫ X₁.π = T'.y ≫ i := by
  first | exact @GlobalTheory.Poinc.traitLift_setup | exact GlobalTheory.Poinc.traitLift_setup | (intros; apply GlobalTheory.Poinc.traitLift_setup <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc.TraitRam

variable {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ}

theorem dim_eq (hn : 2 ≤ n) (hζ : IsUnit ζ) (T : Trait F) : T.A.g = g := by
  let K := AlgebraicClosure (FractionRing T.V)
  let k : Sp K ⟶ Sp (FractionRing T.V) := spMap (algebraMap (FractionRing T.V) K)
  have hK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hp := (IsPullback.of_hasPullback T.A.A.hom k).paste_horiz T.cart.1
  have h1 : SmoothOfRelativeDimension T.A.g (pullback.snd T.A.A.hom k) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback T.A.A.hom k) T.A.smoothDim
  refine GlobalTheory.SiegDim.dim_geometric_fibre F.univ hn hζ hK (k ≫ T.y) ?_
  change SmoothOfRelativeDimension T.A.g (pullback.snd F.univ.A.hom (k ≫ T.y))
  rw [← hp.isoPullback_inv_snd]
  exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
    (IsPullback.of_horiz_isIso (fst := hp.isoPullback.inv) (g := 𝟙 _) ⟨by simp⟩) h1

theorem finrank_le (hn : 2 ≤ n) (hζ : IsUnit ζ) (T : Trait F) : Module.finrank ℤ T.D.toPre.X ≤ g := by
  have hR : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, T.complete⟩
  have h := GlobalTheory.TateUnif.rank_add_dim hR T.semi T.U
  have e := dim_eq hn hζ T
  omega

theorem evalZ_eq_mul : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o), 2 ≤ n → IsUnit ζ → ∀ (F : SFam g n ζ) (T T' : Trait F) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V), Function.Injective f → IsLocalHom f → (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) → T'.y = spMap fK ≫ T.y → ∀ m : ℕ, Associated (f T.ϖ) (T'.ϖ ^ m) → ∀ φ : InvFun ℤ, IsPolFan id g φ → φ.evalZ T'.β = m * φ.evalZ T.β := by
  intro g n o _ ζ hn hζ F T T' f fK hf hl hK hy m hm φ hφ
  have hB : GlobalTheory.Mum.Base T'.V := ⟨⟨inferInstance, inferInstance, inferInstance, T'.complete⟩, inferInstance⟩
  have hid : spMap (RingHom.id (FractionRing T'.V)) = 𝟙 _ := Spec.map_id _
  obtain ⟨e, he⟩ := GlobalTheory.T.trait_lattices_iso_forms_proportional_ramification g n o ζ F T T' T'.V f (RingHom.id _) fK (RingHom.id _) hB inferInstance hf
    Function.injective_id hl inferInstance hK (fun _ => rfl) (by rw [hid, Category.id_comp, hy]) T'.ϖ m 1 T'.irr hm
    (by rw [pow_one]; rfl)
  have hon := hφ T.D.toPre.X (finrank_le hn hζ T)
  have hc : toReal T.β ∈ psdCone (id : ℤ → ℤ) T.D.toPre.X :=
    GlobalTheory.PolFan.TameZ.toReal_mem_psdCone_int (mem_balForms_int.2 T.symm) fun x => by simpa using T.mono.nonneg 0 x
  rw [← evalR_toReal φ T.β, ← hon.homog _ hc m m.cast_nonneg,
    ← evalZ_pull φ (r := e.toIntLinearEquiv.toLinearMap) e.surjective, ← evalR_toReal]
  congr 1
  refine LinearMap.ext₂ fun a b => ?_
  have h := he a b
  rw [Nat.cast_one, one_mul] at h
  simp only [toReal_apply, pull_apply, LinearMap.smul_apply, smul_eq_mul]
  exact_mod_cast h.symm

end GlobalTheory.Poinc.TraitRam
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.NormDown

theorem dvd_of_map_dvd {V V' : Type} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing V'] [IsDomain V']
    (h : V →+* V') (hi : Function.Injective h) [IsLocalHom h] {x y : V} (hxy : h x ∣ h y) : x ∣ y := by
  rcases ValuationRing.dvd_total x y with hd | ⟨c, rfl⟩
  · exact hd
  · by_cases hy : y = 0
    · simp [hy]
    obtain ⟨e, he⟩ := hxy
    have hy' : h y ≠ 0 := fun h0 => hy (hi (by rw [h0, map_zero]))
    have h1 : h y * 1 = h y * (h c * e) := by rw [mul_one, ← mul_assoc, ← map_mul, ← he]
    have hu : IsUnit (h c) := isUnit_iff_exists_inv.2 ⟨e, (mul_left_cancel₀ hy' h1).symm⟩
    have hc : IsUnit c := (isUnit_map_iff h c).1 hu
    exact ⟨↑hc.unit⁻¹, by rw [mul_assoc, IsUnit.mul_val_inv, mul_one]⟩

theorem map_injective {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    (h : V →+* V') (hi : Function.Injective h) [IsLocalHom h] {I I' : Ideal V} (e : I.map h = I'.map h) : I = I' := by
  obtain ⟨x, rfl⟩ : ∃ x, I = Ideal.span {x} := ⟨_, (Submodule.IsPrincipal.span_singleton_generator I).symm⟩
  obtain ⟨y, rfl⟩ : ∃ y, I' = Ideal.span {y} := ⟨_, (Submodule.IsPrincipal.span_singleton_generator I').symm⟩
  rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
    Ideal.span_singleton_eq_span_singleton] at e
  rw [Ideal.span_singleton_eq_span_singleton]
  exact associated_of_dvd_dvd (dvd_of_map_dvd h hi e.dvd) (dvd_of_map_dvd h hi e.symm.dvd)

theorem jK_spMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (fK : FractionRing R →+* FractionRing S)
    (hc : ∀ a, fK (algebraMap R _ a) = algebraMap S _ (f a)) : jK S ≫ spMap f = spMap fK ≫ jK R := by
  simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  exact (hc a).symm

theorem normDescent : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = W → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) → (∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a}) → ∃ (k : ℕ) (J : Z.IdealSheafData), 1 ≤ k ∧ (∀ x ∈ J.support, x ∈ W ∧ x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → idlAlong J (ξ₁ ≫ X₁.π) = idlAlong J₁ ξ₁ ^ k := by
  intro g n hg hn hodd F Z z i hZ φ hφ W hWc hWi W8 X₁ ι J₁ hι hπ hsupp hord
  have hne : ((⊤ : X₁.M.Z.Opens) : Set X₁.M.Z).Nonempty := Set.univ_nonempty
  haveI : CharZero X₁.Ω₁ := X₁.ar.char
  haveI hchar : CharZero Γ(X₁.M.Z, ⊤) := RingHom.charZero (X₁.M.res ⊤ hne)
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  haveI := X₁.M.lft
  have hLN : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
  obtain ⟨d, J, hd, hJs, hJl⟩ := GlobalTheory.T.norm_descent_idealSheaf_finite_open_closed_image X₁.M.Z Z X₁.π X₁.fin inferInstance hLN X₁.normal hZ.2.1
    (by rw [hπ]; exact hWc.isOpen) hchar J₁
  refine ⟨d, J, hd, fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hJs x hx
    exact ⟨hπ ▸ ⟨y, rfl⟩, hsupp y hy⟩
  intro T ξ₁ hgen
  obtain ⟨V', _, _, _, _, f, ψ, hc', hfi, hfl, hψ, hprod⟩ :=
    hJl T.V T.complete (ξ₁ ≫ X₁.π) ⟨ξ₁ (closedPoint T.V), rfl⟩
  let fK : FractionRing T.V →+* FractionRing V' :=
    IsLocalization.map (FractionRing V') f (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hfi)
  have hfK : ∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a) := fun a => IsLocalization.map_eq _ a
  have hB : GlobalTheory.Mum.Base V' := ⟨⟨inferInstance, inferInstance, inferInstance, hc'⟩, inferInstance⟩
  obtain ⟨T₂, f₂, fK₂, hi₂, hl₂, -, hc₂, hy₂⟩ := GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n _ _ F V' hB inferInstance (spMap fK ≫ T.y)

  have hover : ∀ χ : Sp V' ⟶ X₁.M.Z, χ ≫ X₁.π = spMap f ≫ ξ₁ ≫ X₁.π →
      jK T₂.V ≫ (spMap f₂ ≫ χ) ≫ X₁.π = T₂.y ≫ i := by
    intro χ hχ
    rw [Category.assoc, hχ, ← Category.assoc, jK_spMap f₂ fK₂ hc₂, Category.assoc, ← Category.assoc (jK V'),
      jK_spMap f fK hfK, Category.assoc, hgen, hy₂]
    simp only [Category.assoc]
  obtain ⟨a₀, ha₀, h₀⟩ := hord T₂ _ (hover (spMap f ≫ ξ₁) (Category.assoc _ _ _))
  have hj : ∀ j, idlAlong J₁ (spMap f₂ ≫ ψ j) = Ideal.span {T₂.ϖ ^ a₀} := by
    intro j
    obtain ⟨a, ha, h⟩ := hord T₂ _ (hover (ψ j) (hψ j))
    rw [h, show a = a₀ from by exact_mod_cast ha.trans ha₀.symm]
  have hcomp : spMap (f₂.comp f) = spMap f₂ ≫ spMap f := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  haveI : IsLocalHom (f₂.comp f) := RingHom.isLocalHom_comp f₂ f
  apply map_injective (f₂.comp f) (hi₂.comp hfi)
  have hmp := map_prod (Ideal.mapHom f₂) (fun j => idlAlong J₁ (ψ j)) Finset.univ
  simp only [Ideal.mapHom_apply] at hmp
  rw [← Ideal.map_map, hprod, Ideal.map_pow, ← GlobalTheory.TraitOrder.idlAlong_comp, hcomp, Category.assoc, h₀, hmp]
  simp only [← GlobalTheory.TraitOrder.idlAlong_comp, hj, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end GlobalTheory.NormDown
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_descent_ideal_thetaModel_to_clopen_component : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = W → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) → (∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a}) → ∃ (k : ℕ) (J : Z.IdealSheafData), 1 ≤ k ∧ (∀ x ∈ J.support, x ∈ W ∧ x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → idlAlong J (ξ₁ ≫ X₁.π) = idlAlong J₁ ξ₁ ^ k := by
  atlas_forward_decl GlobalTheory.NormDown.normDescent
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.PoincDown

theorem exists_assoc_pow {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    [IsDiscreteValuationRing V'] (f : V →+* V') (hf : Function.Injective f) [IsLocalHom f] {ϖ : V} (hϖ : Irreducible ϖ)
    {ϖ' : V'} (hϖ' : Irreducible ϖ') : ∃ m : ℕ, 1 ≤ m ∧ Associated (f ϖ) (ϖ' ^ m) := by
  have h0 : f ϖ ≠ 0 := fun h => hϖ.ne_zero (hf (by rw [h, map_zero]))
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible h0 hϖ'
  refine ⟨m, Nat.one_le_iff_ne_zero.2 fun e => ?_, hm⟩
  subst e
  rw [pow_zero] at hm
  exact hϖ.not_isUnit ((isUnit_map_iff f ϖ).1 (associated_one_iff_isUnit.1 hm))

theorem map_eq_span_pow {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    [IsDiscreteValuationRing V'] (f : V →+* V') {ϖ : V} (hϖ : Irreducible ϖ) {ϖ' : V'} (hϖ' : Irreducible ϖ') {m : ℕ}
    (hm : Associated (f ϖ) (ϖ' ^ m)) {I : Ideal V} {b : ℕ} (h : I.map f = Ideal.span {ϖ' ^ b}) :
    ∃ a : ℕ, b = m * a ∧ I = Ideal.span {ϖ ^ a} := by
  have hI : I ≠ ⊥ := by
    rintro rfl
    rw [Ideal.map_bot, eq_comm, Ideal.span_singleton_eq_bot] at h
    exact pow_ne_zero _ hϖ'.ne_zero h
  obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  refine ⟨a, ?_, rfl⟩
  rw [Ideal.map_span, Set.image_singleton, map_pow, Ideal.span_singleton_eq_span_singleton] at h
  have h2 : Associated (ϖ' ^ (m * a)) (ϖ' ^ b) := by
    rw [pow_mul]; exact (hm.pow_pow (n := a)).symm.trans h
  have e1 := (pow_dvd_pow_iff hϖ'.ne_zero hϖ'.not_isUnit).1 h2.dvd
  have e2 := (pow_dvd_pow_iff hϖ'.ne_zero hϖ'.not_isUnit).1 h2.symm.dvd
  omega

theorem idealDescent : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = W → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) → (∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a}) → ∃ (d : ℕ) (J : Z.IdealSheafData), 1 ≤ d ∧ (∀ x ∈ J.support, x ∈ W ∧ x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ Z), jK T.V ≫ ξ = T.y ≫ i → ξ (closedPoint T.V) ∈ W → ∃ a : ℕ, (a : ℝ) = d * φ.evalZ T.β ∧ idlAlong J ξ = Ideal.span {T.ϖ ^ a} := by
  intro g n hg hn hodd F Z z i hZ φ hφ W hWc hWi W8 X₁ ι J₁ hι hπ hsupp hord
  obtain ⟨k, J, hk, hJs, hJo⟩ := GlobalTheory.T.norm_descent_ideal_thetaModel_to_clopen_component g n hg hn hodd F Z z i hZ φ hφ W hWc hWi W8 X₁ ι J₁ hι hπ hsupp hord
  refine ⟨k * ι, J, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), hJs, ?_⟩
  intro T ξ hξ hW
  have hc : IsClopen (Set.range X₁.π) := by rw [hπ]; exact hWc
  obtain ⟨T', f, fK, ξ₁, hf, hfl, hfK, hy, hsq, hgen⟩ := GlobalTheory.T.exists_trait_lift_thetaSetup_model_after_extension g n F Z i W8 X₁ hc T ξ hξ (by rw [hπ]; exact hW)
  obtain ⟨a₁, ha₁, hJ₁⟩ := hord T' ξ₁ hgen
  have hJ := hJo T' ξ₁ hgen
  obtain ⟨m, hm1, hm⟩ := exists_assoc_pow f hf T.irr T'.irr
  have hφ' := GlobalTheory.Poinc.TraitRam.evalZ_eq_mul g n _ _ (by omega) (cycBase (show n ≠ 0 by omega)).ζ.isUnit F T T' f fK hf hfl hfK hy m hm φ hφ
  have e1 : (idlAlong J ξ).map f = Ideal.span {T'.ϖ ^ (a₁ * k)} := by
    rw [← GlobalTheory.TraitOrder.idlAlong_comp, hsq, hJ, hJ₁, Ideal.span_singleton_pow, ← pow_mul]
  obtain ⟨a, hb, ha⟩ := map_eq_span_pow f T.irr T'.irr hm e1
  refine ⟨a, ?_, ha⟩
  have hb' : ((a₁ : ℝ) * k) = m * a := by exact_mod_cast hb
  rw [ha₁, hφ'] at hb'
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  push_cast
  apply mul_left_cancel₀ hm0.ne'
  linarith [hb']

end GlobalTheory.PoincDown
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealDescent_thetaModel_to_component_traitOrders : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = W → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) → (∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a}) → ∃ (d : ℕ) (J : Z.IdealSheafData), 1 ≤ d ∧ (∀ x ∈ J.support, x ∈ W ∧ x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ Z), jK T.V ≫ ξ = T.y ≫ i → ξ (closedPoint T.V) ∈ W → ∃ a : ℕ, (a : ℝ) = d * φ.evalZ T.β ∧ idlAlong J ξ = Ideal.span {T.ϖ ^ a} := by
  atlas_forward_decl GlobalTheory.PoincDown.idealDescent
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem idealSt_holds : IdealSt := by
  intro g hg n hn hodd F Z z i hθ φ hφ
  obtain ⟨ι, _, W, hclo, hirr, hpart⟩ := GlobalTheory.T.exists_clopen_irreducible_partition_of_normal_proj n Z z hθ.1 hθ.2.1
  have key : ∀ c, ∃ (d : ℕ) (J : Z.IdealSheafData), 1 ≤ d ∧ (∀ x ∈ J.support, x ∈ W c ∧ x ∉ Set.range i) ∧
      ∀ (T : Trait F) (ξ : Sp T.V ⟶ Z), jK T.V ≫ ξ = T.y ≫ i → ξ (closedPoint T.V) ∈ W c →
        ∃ a : ℕ, (a : ℝ) = d * φ.evalZ T.β ∧ idlAlong J ξ = Ideal.span {T.ϖ ^ a} := by
    intro c
    obtain ⟨W8, X₁, ι₁, J₁, h1, h2, h4, h5⟩ :=
      GlobalTheory.T.exists_thetaSetup_ideal_over_clopen_component g n hg hn hodd F Z z i hθ φ hφ (W c) (hclo c) (hirr c)
    exact GlobalTheory.T.idealDescent_thetaModel_to_component_traitOrders g n hg hn hodd F Z z i hθ φ hφ (W c) (hclo c) (hirr c) W8 X₁ ι₁ J₁ h1 h2 h4 h5
  choose d J hd hJ hv using key
  exact GlobalTheory.T.exists_fanOrder_ideal_glued_clopen_pieces F i φ W J d hclo hpart hd hJ hv

end GlobalTheory.Poinc
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fanOrder_ideal_thetaCompactification : IdealSt := by
  atlas_forward_decl GlobalTheory.Poinc.idealSt_holds
end
