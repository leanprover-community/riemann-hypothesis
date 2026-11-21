import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonomialFormOnChartRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedEtaleCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriod
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryFormBaseChangeDvr

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitRank

theorem evalZ_comb' {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (a : ℕ)
    (ψ : InvFun O) (b : ℕ) (φ : InvFun O) (β : LinearMap.BilinForm ℤ X) :
    (comb a ψ b φ).evalZ β = a * ψ.evalZ β + b * φ.evalZ β := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  unfold InvFun.evalZ
  rw [(comb a ψ b φ).eval_eq hr, ψ.eval_eq hr, φ.eval_eq hr]
  rfl

theorem exists_generic_of_range {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (W : Type) [CommRing W] [IsDomain W] [CharZero W]
    (χ : Sp W ⟶ Z.X) (hχ : Set.range (jK W ≫ χ) ⊆ Set.range Z.j) :
    ∃ y : Sp (FractionRing W) ⟶ Xo.XF c, y ≫ Z.j = jK W ≫ χ := by
  haveI := c.fin
  haveI : NumberField c.F := {}
  haveI : CharZero (FractionRing W) := by
    refine ⟨fun a b h => Nat.cast_injective (R := W) (IsFractionRing.injective W (FractionRing W) ?_)⟩
    simpa using h
  obtain ⟨β₀, hβ₀⟩ := Spec.map_surjective (jK W ≫ χ ≫ Z.s)
  let β' : 𝓞 c.F →+* FractionRing W := β₀.hom
  have hinj : Function.Injective β' := GlobalTheory.LieUnif.injective_of_charZero (E := c.F) β'
  let g : c.F →+* FractionRing W := IsFractionRing.lift (K := c.F) hinj
  have hsq : (jK W ≫ χ) ≫ Z.s = spMap g ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    have hb : β₀ = CommRingCat.ofHom (g.comp (algebraMap (𝓞 c.F) c.F)) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      have := IsFractionRing.lift_algebraMap (K := c.F) hinj a
      exact this.symm
    rw [Category.assoc, ← hβ₀, hb]
    show _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl
  let u : Sp (FractionRing W) ⟶ pullback Z.s (spMap (algebraMap (𝓞 c.F) c.F)) := pullback.lift (jK W ≫ χ) (spMap g) hsq
  have hu : Set.range u ⊆ Set.range Z.jQ := by
    rintro _ ⟨p, rfl⟩
    rw [← Z.ab_gen]
    obtain ⟨v, hv⟩ := hχ ⟨p, rfl⟩
    have e1 : (pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F))) (u p) = (jK W ≫ χ) p := by
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    show (pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F))) (u p) ∈ abLocus Z.t.G
    rw [e1, ← hv]
    have : Z.jQ v ∈ (pullback.fst Z.s (spMap (algebraMap (𝓞 c.F) c.F))) ⁻¹' abLocus Z.t.G := by
      rw [Z.ab_gen]; exact ⟨v, rfl⟩
    exact this
  haveI := Z.jQ_open
  refine ⟨IsOpenImmersion.lift Z.jQ u hu, ?_⟩
  show _ ≫ Z.jQ ≫ pullback.fst _ _ = _
  rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]

theorem finrank_le_min_of_range {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [CharZero R] (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R)) (m : SABMap t Z.t ξ)
    (P : PELUnif (maximalIdeal R) t) (hξ : Set.range (jK R ≫ ξ) ⊆ Set.range Z.j) :
    Module.finrank (𝓞 E) P.D.toPre.X ≤ min D.p D.q := by
  obtain ⟨y, hy⟩ := exists_generic_of_range Z R ξ hξ
  let K := AlgebraicClosure (FractionRing R)
  let f : R →+* K := (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero K := ⟨fun a b h => Nat.cast_injective (R := R) (hf (by simpa using h))⟩
  let x' : Sp K ⟶ Xo.XF c := spMap (algebraMap (FractionRing R) K) ≫ y
  have hx : x' ≫ Z.jQ ≫ pullback.fst _ _ = spMap f ≫ ξ := by
    show (spMap (algebraMap (FractionRing R) K) ≫ y) ≫ Z.j = _
    rw [Category.assoc, hy, ← Category.assoc]
    show (Spec.map _ ≫ Spec.map _) ≫ ξ = _
    rw [← Spec.map_comp]
    rfl
  obtain ⟨β₀, hβ₀⟩ := Spec.map_surjective
    (x' ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)
  have hβ : x' ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s = spMap β₀.hom :=
    hβ₀.symm
  have hdet := (Z.oF.geom K x' β₀.hom hβ).1
  have hr : (β₀.hom (baseKA l).ρ) ^ 2 = -(H.d : K) := by
    rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have bound : ∀ (τ : 𝓞 E →+* K) (N : ℕ), LieMult Z.oF.t.act x' τ N →
      Module.finrank (𝓞 E) P.D.toPre.X ≤ N := by
    intro τ N hN
    have h₅ := (GlobalTheory.lieMult_iff_of_isGrpPullback Z.m.cart Z.oF.t.act Z.t.act Z.m.act x' τ N).1 hN
    rw [hx] at h₅
    have h₆ := (GlobalTheory.lieMult_iff_of_isGrpPullback m.cart t.act Z.t.act m.act (spMap f) τ N).2 h₅
    obtain ⟨n, -, hn⟩ := GlobalTheory.CharRank.lieMult_unif_loc H R t P K f hf τ N h₆
    omega
  obtain ⟨τ₁, τ₂, h₁, h₂⟩ := GlobalTheory.CharRank.exists_chars H K _ hr
  exact le_min (bound τ₁ _ ((hdet τ₁).1 h₁)) (bound τ₂ _ ((hdet τ₂).2 h₂))

theorem order_nat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : EffCartierData Y.X) (π : Z.X ⟶ X.X) (e : gen Y ≅ gen Z) (J : X.X.IdealSheafData) (EX : EffCartierData Z.X) (n d d' k g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) (DX : EffCartierData X.X), Module.finrank ℚ E * min D.p D.q ≤ g → IsPolFan id g φs → Refines H (min D.p D.q) φs 𝒩 φ → HasCones (ConeZ E φs) X → X.N4 → IsPol (comb d (resInt _ φs) 0 φ) k X DX → 0 < d' → IsPhiDiv (comb 0 φ d' φ) Y BY → IsBlowOf X Z Y BY π e J EX n → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ¬ (∀ p : ℕ, p.Prime → IsUnit (p : W)) → ∀ ϖ : W, Irreducible ϖ → ∀ (χ : Sp W ⟶ Z.X) (t : SAB H (Sp W)) (_ : SABMap t Z.t χ) (P : PELUnif (maximalIdeal W) t), Set.range (jK W ≫ χ) ⊆ Set.range Z.j → ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] → ∃ m : ℕ, (m : ℝ) = (comb 0 φ (n * d') φ).evalZ be := by
  intro E _ _ _ H D l Xo c X Z Y BY π e J EX n d d' k g φs 𝒩 φ DX _ _ href _ _ _ _ _ _ W _ _ _ hW _ ϖ _ χ t mt P hχ be
    hbe hmon
  obtain ⟨hdvr, -, hch⟩ := hW
  haveI := hdvr
  haveI := hch
  have hrk := finrank_le_min_of_range Z W χ t mt P hχ
  haveI : Module.Projective (𝓞 E) P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) P.D.toPre.X
  have hF := href.1 P.D.toPre.X hrk
  have hbal : be ∈ balForms H.bar P.D.toPre.X := by rw [balForms_eq_levelForms]; exact hbe
  obtain ⟨a, ha⟩ := hF.exists_nat hbal (fun y => hmon.nonneg 0 y)
  refine ⟨n * d' * a, ?_⟩
  rw [evalZ_comb', ha]
  push_cast
  ring

end GlobalTheory.TraitRank
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

open GlobalTheory.TraitChartForm in

theorem GlobalTheory.TraitBlowForm.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), Z.j ≫ π = X.j → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X.X) (tR : SAB H (Sp R)) (_ : SABMap tR X.t ξ) (PR : PELUnif (maximalIdeal R) tR), IsCN R → PR.TorsionIso → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ¬ (∀ p : ℕ, p.Prime → IsUnit (p : W)) → ∀ ϖ : W, Irreducible ϖ → ∀ (χ : Sp W ⟶ Z.X) (t : SAB H (Sp W)) (_ : SABMap t Z.t χ) (P : PELUnif (maximalIdeal W) t), Set.range (jK W ≫ χ) ⊆ Set.range Z.j → ∀ be : LinearMap.BilinForm ℤ P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (f : W →+* V) (ψ : R →+* V), Function.Injective f → IsLocalHom f → IsLocalHom ψ → Irreducible (f ϖ) → spMap f ≫ χ ≫ π = spMap ψ ≫ ξ → Set.range (jK V ≫ spMap ψ ≫ ξ) ⊆ Set.range X.j → ∃ ε : PR.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X, ∀ y, ∃ (r : R) (n : ℕ), PsiCoord PR.D.toPre y r ∧ be (ε y) (ε y) = 2 * n ∧ Associated (ψ r) (f ϖ ^ n) := by
  intro E _ _ _ H D l Xo c X Z π hπ R _ _ _ ξ tR mR PR hCN hTor W _ _ _ hW _ ϖ hϖ χ t mt P hr be hmon V _ _ _ hV f ψ
    hfi hfl hψl _ hc hrV
  have hV' : CDvr V := hV
  obtain ⟨hWd, hWc, hW0⟩ := hW
  obtain ⟨hVd, hVc, hV0⟩ := hV
  obtain ⟨hRN, hRI, hRA, hR0⟩ := hCN
  obtain ⟨L₁, L₂, L₃, L₄, L₅⟩ := GlobalTheory.firstFiveLaws

  obtain ⟨tV, ⟨mV⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap f) t
  obtain ⟨tRV, ⟨mRV⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap ψ) tR
  obtain ⟨n₀⟩ := GlobalTheory.TraitOrder.comp rfl mt mV
  obtain ⟨n₂⟩ := GlobalTheory.TraitOrder.comp rfl mR mRV
  have j : Function.Injective ((algebraMap V (FractionRing V)).comp f) := (IsFractionRing.injective V _).comp hfi
  let g : FractionRing W →+* FractionRing V := IsFractionRing.lift j
  have eg : jK V ≫ spMap f = spMap g ≫ jK W :=
    (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm
  obtain ⟨yW, hyW⟩ := GlobalTheory.TraitRank.exists_generic_of_range Z W χ hr
  have hZy : jK V ≫ (spMap f ≫ χ) = (spMap g ≫ yW) ≫ Z.j := by
    rw [Category.assoc, hyW, ← Category.assoc (spMap g), ← eg, Category.assoc]
  have hXy : jK V ≫ (spMap f ≫ χ ≫ π) = (spMap g ≫ yW) ≫ X.j := by
    rw [← hπ, ← Category.assoc (spMap g ≫ yW), ← hZy]
    simp only [Category.assoc]
  obtain ⟨n₁⟩ := GlobalTheory.ArcOrder.exists_sabMap_of_generic X Z hV' (spMap g ≫ yW) (spMap f ≫ χ ≫ π) (spMap f ≫ χ)
    hXy hZy n₀
  obtain ⟨k₁⟩ := GlobalTheory.TraitOrder.cancel (show 𝟙 _ ≫ (spMap f ≫ χ ≫ π) = spMap ψ ≫ ξ by rw [Category.id_comp, hc])
    n₁ n₂

  have hpV : PolAt tV (jK V) := GlobalTheory.DatUniq.polAt_pull mV (GlobalTheory.DatUniq.polAt_of_unif P) (jK V) (spMap g) eg.symm
  have hpRV : PolAt tRV (jK V) :=
    GlobalTheory.DatUniq.polAt_pull k₁ hpV (jK V) (𝟙 _) (by rw [Category.id_comp, Category.comp_id])
  obtain ⟨B, -, gen, hg, hw, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H V tV hpV
  obtain ⟨BR, -, genR, hgR, hwR, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H V tRV hpRV

  have hχgen : χ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W) ∈ abLocus Z.t.G := by
    let p : Sp (FractionRing W) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing W))
    obtain ⟨w, hw⟩ := hr ⟨p, rfl⟩
    rw [← jK_apply_eq_bot W p, ← Scheme.Hom.comp_apply, ← hw]
    exact j_mem_abLocus Z w
  have hfbot : spMap f (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W) := by
    rw [← ker_eq_spMap_bot]
    exact PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot f).1 hfi)

  have hlocW : ∀ a ∈ maximalIdeal W, f a ∈ maximalIdeal V := fun a ha =>
    (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit f a h)
  let Ww : Set (Sp W) := abLocus t.G ∩ {p | ϖ ∉ p.asIdeal}
  have hWo : IsOpen Ww :=
    (GlobalTheory.AbLocusOpen.isOpen_abLocus_local t.G t.semi).inter (PrimeSpectrum.isOpen_basicOpen (a := ϖ))
  have hkerW : (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum W) ∈ Ww := by
    rw [ker_eq_spMap_bot, hfbot]
    refine ⟨(abLocus_pullback abLocusOne Z.t.semi mt.cart.1 _).1 hχgen, fun h => hϖ.ne_zero ((Submodule.mem_bot W).1 h)⟩
  have hψW : ∀ y, PsiUnitOn P.D.toPre y Ww := fun y => hmon.psiUnitOn y fun p hp => by simpa using hp.2
  obtain ⟨PV, e₁, he₁⟩ := GlobalTheory.PelCoordPull.exists_pelUnif_psiCoord E H W V f t tV mV P Ww inferInstance inferInstance
    hWc inferInstance inferInstance hVc hlocW hWo Set.inter_subset_left hψW hkerW ⟨B, gen, hg, hw⟩

  have hlocR : ∀ a ∈ maximalIdeal R, ψ a ∈ maximalIdeal V := fun a ha =>
    (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit ψ a h)
  have hRo : IsOpen (abLocus tR.G) := GlobalTheory.AbLocusOpen.isOpen_abLocus_local tR.G tR.semi
  have hAdm : admitted R (maximalIdeal R) := ⟨⟨hRN, inferInstance, hRI, hRA⟩, hRA, hR0, inferInstance,
    by letI := Ideal.Quotient.field (maximalIdeal R); infer_instance⟩
  have hψR : ∀ y, PsiUnitOn PR.D.toPre y (abLocus tR.G) :=
    GlobalTheory.psiUnitOn_abLocus_pel L₁ L₂ L₃ L₄ L₅ E H R (maximalIdeal R) hAdm tR PR hTor hRo
  have hkerR : (⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩ : PrimeSpectrum R) ∈ abLocus tR.G := by
    rw [ker_eq_spMap_bot]
    refine (abLocus_pullback abLocusOne X.t.semi mR.cart.1 _).1 ?_
    let p : Sp (FractionRing V) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
    obtain ⟨w, hw⟩ := hrV ⟨p, rfl⟩
    have key : ξ (spMap ψ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V)) = (jK V ≫ spMap ψ ≫ ξ) p := by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, jK_apply_eq_bot V p]
    rw [key, ← hw]
    exact j_mem_abLocus X w
  obtain ⟨PRV, e₂, he₂⟩ := GlobalTheory.PelCoordPull.exists_pelUnif_psiCoord E H R V ψ tR tRV mRV PR (abLocus tR.G) hRN hRI
    hRA inferInstance inferInstance hVc hlocR hRo subset_rfl hψR hkerR ⟨BR, genR, hgR, hwR⟩

  obtain ⟨e₃, he₃⟩ := GlobalTheory.SameCoord.exists_equiv_psiCoord E H V tV tRV k₁ PV PRV inferInstance inferInstance hVc
  refine ⟨(e₂.trans e₃.symm).trans e₁.symm, fun y => ?_⟩
  obtain ⟨r, hr⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff PR.D.toPre y).2
    (GlobalTheory.PeriodFormCompare.psiIn_top PR.D y)
  set x := ((e₂.trans e₃.symm).trans e₁.symm) y with hx
  have hx2 : e₃ (e₁ x) = e₂ y := by simp [hx]
  obtain ⟨u₀, nW, hnW, hcW⟩ := hmon x
  obtain ⟨u₁, h₁⟩ := he₁ x _ hcW
  obtain ⟨u₃, h₃⟩ := he₃ _ _ h₁
  obtain ⟨u₂, h₂⟩ := he₂ y r hr
  rw [hx2] at h₃
  obtain ⟨w, hw⟩ := GlobalTheory.PsiCoordLocal.exists_unit_of_coord h₃ h₂
  have key : ψ r = ((u₂⁻¹ * w * u₃ * u₁ * Units.map f.toMonoidHom u₀ : Vˣ) : V) * f ϖ ^ nW 0 := by
    have e := congrArg (fun z => ((u₂⁻¹ : Vˣ) : V) * z) hw
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_pow] at e
    rw [← mul_assoc, Units.inv_mul, one_mul] at e
    rw [e]
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    ring
  refine ⟨r, nW 0, hr, by simpa using hnW 0, ?_⟩
  exact Associated.symm (⟨_, by rw [key, mul_comm]⟩ : Associated (f ϖ ^ nW 0) (ψ r))
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

noncomputable section

namespace GlobalTheory.FarTrait

section Algebra
open Polynomial

theorem exists_coefficientField (S : Type) [CommRing S] [IsLocalRing S] [IsAdicComplete (maximalIdeal S) S]
    [CharZero (ResidueField S)] :
    ∃ Λ : Subring S, IsField Λ ∧ ∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S := by
  let T : Set (Subring S) := {Λ | ∀ x ∈ Λ, x ∈ maximalIdeal S → x = 0}
  have hbot : (⊥ : Subring S) ∈ T := by
    intro x hx hm
    obtain ⟨n, rfl⟩ := Subring.mem_bot.1 hx
    rw [← residue_eq_zero_iff, map_intCast, Int.cast_eq_zero] at hm
    simp [hm]
  obtain ⟨Λ, -, hΛ⟩ := zorn_le_nonempty₀ T (fun c hc hch y hy => by
    refine ⟨sSup c, fun x hx => ?_, fun z hz => le_sSup hz⟩
    obtain ⟨K, hK, hxK⟩ := (Subring.mem_sSup_of_directedOn ⟨y, hy⟩ hch.directedOn).1 hx
    exact hc hK x hxK) ⊥ hbot
  have hT : ∀ x ∈ Λ, x ∈ maximalIdeal S → x = 0 := hΛ.prop
  have hF : IsField Λ := by
    refine ⟨exists_pair_ne _, mul_comm, fun {x} hx => ?_⟩
    have hu : IsUnit (x : S) := by
      by_contra h
      exact hx (Subtype.ext (hT _ x.2 h))
    let Λ' : Subring S :=
      { carrier := {s | ∃ n : ℕ, (x : S) ^ n * s ∈ Λ}
        one_mem' := ⟨0, by simp⟩
        zero_mem' := ⟨0, by simp⟩
        mul_mem' := by
          rintro a b ⟨n, hn⟩ ⟨m, hm⟩
          exact ⟨n + m, by convert Λ.mul_mem hn hm using 1; ring⟩
        add_mem' := by
          rintro a b ⟨n, hn⟩ ⟨m, hm⟩
          exact ⟨n + m, by
            convert Λ.add_mem (Λ.mul_mem (Λ.pow_mem x.2 m) hn) (Λ.mul_mem (Λ.pow_mem x.2 n) hm) using 1; ring⟩
        neg_mem' := by
          rintro a ⟨n, hn⟩
          exact ⟨n, by convert Λ.neg_mem hn using 1; ring⟩ }
    have h' : Λ' ∈ T := by
      rintro s ⟨n, hn⟩ hm
      exact (hu.pow n).mul_right_eq_zero.1 (hT _ hn (Ideal.mul_mem_left _ _ hm))
    have hle : Λ' ≤ Λ := hΛ.le_of_ge h' fun s hs => ⟨0, by simpa using hs⟩
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    exact ⟨⟨y, hle ⟨1, by rw [pow_one, hy]; exact Λ.one_mem⟩⟩, Subtype.ext hy⟩
  refine ⟨Λ, hF, fun s => ?_⟩
  letI := hF.toField
  have key : ∀ a : S, (∀ f : Λ[X], aeval a f ∈ maximalIdeal S → aeval a f = 0) → a ∈ Λ := fun a ha => by
    have h' : (aeval (R := Λ) a).toRingHom.range ∈ T := by
      rintro _ ⟨f, rfl⟩ hm
      exact ha f hm
    exact hΛ.le_of_ge h' (fun y hy => ⟨C ⟨y, hy⟩, by simp; rfl⟩) ⟨X, by simp⟩
  have hres : ∀ (a : S) (f : Λ[X]), residue S (aeval a f) = aeval (residue S a) f := fun a f =>
    (aeval_algHom_apply (IsScalarTower.toAlgHom Λ S (ResidueField S)) a f).symm
  by_cases hs : IsAlgebraic Λ (residue S s)
  · have hi := hs.isIntegral
    haveI : CharZero Λ := RingHom.charZero (algebraMap Λ (ResidueField S))
    have hsep : (minpoly Λ (residue S s)).Separable := (minpoly.irreducible hi).separable
    obtain ⟨a, ha, has⟩ := HenselianRing.is_henselian (I := maximalIdeal S)
      ((minpoly Λ (residue S s)).map (algebraMap Λ S)) ((minpoly.monic hi).map _) s
      (by rw [eval_map_algebraMap, ← residue_eq_zero_iff, hres, minpoly.aeval])
      (by
        rw [derivative_map, eval_map_algebraMap]
        have := hsep.aeval_derivative_ne_zero (minpoly.aeval Λ (residue S s))
        rw [← hres] at this
        exact (isUnit_iff_ne_zero (G₀ := ResidueField S)).2 this)
    have e : residue S a = residue S s := by rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact has
    refine ⟨a, key a fun f hf => ?_, by rw [← neg_sub]; exact neg_mem has⟩
    rw [← residue_eq_zero_iff, hres, e] at hf
    obtain ⟨q, rfl⟩ := minpoly.dvd _ _ hf
    rw [IsRoot.def, eval_map_algebraMap] at ha
    rw [map_mul, ha, zero_mul]
  · refine ⟨s, key s fun f hf => ?_, by simp⟩
    rw [← residue_eq_zero_iff, hres] at hf
    by_contra h
    exact hs ⟨f, by rintro rfl; simp at h, hf⟩

end Algebra

open MvPowerSeries GlobalTheory.CohenStructure in

theorem exists_finite_over_normal (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] [CharZero S]
    [IsNoetherianRing S] [hc : IsAdicComplete (maximalIdeal S) S] :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (i : A →+* S),
      Function.Injective i ∧ i.Finite ∧ IsNoetherianRing A ∧ IsIntegrallyClosed A := by
  obtain ⟨p, hp⟩ := CharP.exists (ResidueField S)
  rcases CharP.char_is_prime_or_zero (ResidueField S) p with h | rfl
  · obtain ⟨A, _, _, _, i, h1, h2, h3, h4, -⟩ := exists_finite_injective_of_isAdicComplete S p h
      (by rw [← residue_eq_zero_iff, map_natCast]; exact CharP.cast_eq_zero _ p) inferInstance hc
    exact ⟨A, inferInstance, inferInstance, i, h1, h2, h3, h4⟩
  haveI := CharP.charP_to_charZero (ResidueField S)
  by_cases hm : maximalIdeal S = ⊥
  · letI := (isField_iff_maximalIdeal_eq.2 hm).toField
    exact ⟨S, inferInstance, inferInstance, RingHom.id S, Function.injective_id, RingHom.Finite.id S, inferInstance,
      inferInstance⟩
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  obtain ⟨Λ, hF, h1⟩ := exists_coefficientField S
  letI := hF.toField
  obtain ⟨n, x₀, hx₀, hd, N, hN⟩ := GlobalTheory.exists_systemOfParameters_insert S a ha0 ha
  let x : Fin (n + 1) → S := Fin.cons a x₀
  have hx : ∀ i, x i ∈ maximalIdeal S := fun i => Fin.cases ha hx₀ i
  let A := MvPowerSeries (Fin (n + 1)) Λ
  let φ : A →ₐ[Λ] S := mvEvalAdic Λ (maximalIdeal S) x hx
  letI : Algebra A S := φ.toRingHom.toAlgebra
  have : IsDomain A := isDomain_mvPowerSeries Λ (n + 1)
  have hb : maximalIdeal Λ = ⊥ := isField_iff_maximalIdeal_eq.1 hF
  have : IsAdicComplete (maximalIdeal Λ) Λ := by rw [hb]; infer_instance
  have hA := isAdicComplete_mvPowerSeries Λ (n + 1)
  have hle : (maximalIdeal A).map (algebraMap A S) ≤ maximalIdeal S := by
    refine Ideal.map_le_iff_le_comap.2 fun g hg => ?_
    have h4 := algHom_sub_constantCoeff_mem φ (K := maximalIdeal S)
      (fun j => by simpa [φ] using hx j) g
    have h5 := FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.1 hg
    rw [hb, Ideal.mem_bot] at h5
    rwa [h5, map_zero, sub_zero] at h4
  have hge : maximalIdeal S ^ N ≤ (maximalIdeal A).map (algebraMap A S) := by
    refine hN.trans (Ideal.span_le.2 ?_)
    rw [← Fin.range_cons]
    rintro _ ⟨i, rfl⟩
    show x i ∈ _
    rw [← mvEvalAdic_X (A := Λ) (maximalIdeal S) x hx i]
    exact Ideal.mem_map_of_mem (algebraMap A S)
      (FormalIsogeny.mem_maximalIdeal_iff_constantCoeff.2 (by simp))
  have : IsHausdorff ((maximalIdeal A).map (algebraMap A S)) S :=
    IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hle)
  have : Module.Finite A (S ⧸ (maximalIdeal A).map (algebraMap A S)) := by
    refine finite_quotient_of_pow_le (fun s => ?_) hge
    obtain ⟨a, ha, h⟩ := h1 s
    refine ⟨C ⟨a, ha⟩, ?_⟩
    rwa [show algebraMap A S (C ⟨a, ha⟩) = a from mvEvalAdic_C _ x hx _]
  have hfin : Module.Finite A S := FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal A)
  refine ⟨A, inferInstance, inferInstance, algebraMap A S,
    injective_of_ringKrullDim_eq (n := n + 1) ?_ (by rw [hd]; norm_cast), hfin, inferInstance,
    isIntegrallyClosed_mvPowerSeries Λ (n + 1)⟩
  rw [FormalIsogeny.ringKrullDim_mvPowerSeries, ringKrullDim_eq_zero_of_isField hF,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]

theorem exists_factor {R W : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing W] [IsDomain W] [IsIntegrallyClosed W] [CharZero W] (g : R →+* W) :
    ∃ (N : Type) (_ : CommRing N) (_ : IsDomain N) (_ : IsLocalRing N) (φ : R →+* N) (g' : N →+* W),
      IsCN N ∧ IsLocalHom φ ∧ Function.Injective g' ∧ ∀ r, g' (φ r) = g r := by
  haveI := RingHom.ker_isPrime g
  let S := R ⧸ RingHom.ker g
  let k : S →+* W := RingHom.kerLift g
  have hk : Function.Injective k := RingHom.kerLift_injective g
  haveI : IsLocalRing S := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R) S
  haveI : IsAdicComplete (maximalIdeal S) S := CompleteFiniteExtension.isAdicComplete_of_finite_local R S
  haveI : CharZero S := RingHom.charZero k
  obtain ⟨A, _, _, i, hi, hfin, _, _⟩ := exists_finite_over_normal S
  letI : Algebra A S := i.toAlgebra
  have : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).2 hi
  have : Module.Finite A S := hfin
  let N := integralClosure S (FractionRing S)
  have hf : Module.Finite S N := finite_normalisation_of_finite_over_normal A S
  haveI : IsLocalRing N := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := S) _
  have j : Function.Injective ((algebraMap W (FractionRing W)).comp k) := (IsFractionRing.injective W _).comp hk
  let K : FractionRing S →+* FractionRing W := IsFractionRing.lift j
  have hK : ∀ s, K (algebraMap S _ s) = algebraMap W _ (k s) := IsFractionRing.lift_algebraMap j
  have hint : ∀ x : N, K x ∈ (algebraMap W (FractionRing W)).range := fun x =>
    IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.map_of_comp_eq k K (RingHom.ext fun s => (hK s).symm) x.2)
  let eW : W ≃+* (algebraMap W (FractionRing W)).range :=
    RingEquiv.ofBijective (algebraMap W (FractionRing W)).rangeRestrict
      ⟨fun a b h => IsFractionRing.injective W (FractionRing W) (congrArg Subtype.val h),
        RingHom.rangeRestrict_surjective _⟩
  let g' : N →+* W := eW.symm.toRingHom.comp ((K.comp N.val.toRingHom).codRestrict _ hint)
  have hg' : ∀ x : N, algebraMap W (FractionRing W) (g' x) = K x := fun x =>
    congrArg Subtype.val (eW.apply_symm_apply ⟨K x, hint x⟩)
  have hinj : Function.Injective g' := fun a b h =>
    Subtype.ext (K.injective ((hg' a).symm.trans ((congrArg _ h).trans (hg' b))))
  haveI : FaithfulSMul S N := (faithfulSMul_iff_algebraMap_injective S N).2 fun a b h =>
    IsFractionRing.injective S (FractionRing S) (congrArg Subtype.val h)
  haveI : IsLocalHom (Ideal.Quotient.mk (RingHom.ker g)) := IsLocalHom.of_surjective (S := S) _ Ideal.Quotient.mk_surjective
  refine ⟨N, inferInstance, inferInstance, inferInstance, (algebraMap S N).comp (Ideal.Quotient.mk _), g',
    ⟨IsNoetherianRing.of_finite S _, integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing S),
      CompleteFiniteExtension.isAdicComplete_of_finite_local S _, RingHom.charZero g'⟩, inferInstance, hinj, fun r => ?_⟩
  exact IsFractionRing.injective W (FractionRing W) ((hg' _).trans (hK _))

open GlobalTheory.TraitChartForm in

theorem exists_quot_coord {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R)) (m : SABMap t Z.t ξ) (P : PELUnif (maximalIdeal R) t) (hR : IsCN R)
    (hT : P.TorsionIso) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V) (g : R →+* V)
    (hg : ¬ IsLocalHom g) (hgen : ∀ p, (jK V ≫ spMap g ≫ ξ) p ∈ Set.range Z.j) (tV : SAB H (Sp V))
    (mV : SABMap tV Z.t (spMap g ≫ ξ)) (PV : PELUnif (maximalIdeal V) tV) :
    ∃ ρ : P.D.toPre.X →ₗ[𝓞 E] PV.D.toPre.X, Function.Surjective ρ ∧
      ∀ y r r', PsiCoord P.D.toPre y r → PsiCoord PV.D.toPre (ρ y) r' → Associated (g r) r' := by
  obtain ⟨hRN, hRI, hRA, hR0⟩ := hR
  have hV' := hV
  obtain ⟨hVd, hVc, hV0⟩ := hV'
  obtain ⟨L₁, L₂, L₃, L₄, L₅⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨N, _, _, _, φ, g', hN, hφ, hg', hfac⟩ := exists_factor g
  have hN' := hN
  obtain ⟨hNN, hNI, hNA, hN0⟩ := hN'
  have hsp : spMap g' ≫ spMap φ = spMap g := GlobalTheory.Ex.UnifModel.spMap_comp hfac
  obtain ⟨tN, ⟨mN⟩⟩ := GlobalTheory.TraitOrder.exists_pull (spMap φ) t
  obtain ⟨nN⟩ := GlobalTheory.TraitOrder.comp rfl m mN
  obtain ⟨k⟩ := GlobalTheory.TraitOrder.cancel (show spMap g' ≫ (spMap φ ≫ ξ) = spMap g ≫ ξ by rw [← Category.assoc, hsp]) nN mV
  have hbot : spMap g' (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V) = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum N) := by
    rw [← ker_eq_spMap_bot]
    exact PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot g').1 hg')
  have hj : ξ (spMap φ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum N)) ∈ Set.range Z.j := by
    let p : Sp (FractionRing V) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
    have := hgen p
    rwa [← hsp, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, jK_apply_eq_bot V p, hbot] at this
  obtain ⟨y, hy⟩ := GlobalTheory.TraitRank.exists_generic_of_range Z N (spMap φ ≫ ξ) (by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, jK_apply_eq_bot N p]
    exact hj)
  obtain ⟨B, -, gen, hB, hw, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H N tN
    (GlobalTheory.GoodTrait.polAt_of_point Z nN _ y hy)
  have hloc : ∀ a ∈ maximalIdeal R, φ a ∈ maximalIdeal N := fun a ha =>
    (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit φ a h)
  have hRo : IsOpen (abLocus t.G) := GlobalTheory.AbLocusOpen.isOpen_abLocus_local t.G t.semi
  have hAdm : admitted R (maximalIdeal R) := ⟨⟨hRN, inferInstance, hRI, hRA⟩, hRA, hR0, inferInstance,
    by letI := Ideal.Quotient.field (maximalIdeal R); infer_instance⟩
  have hψ : ∀ y, PsiUnitOn P.D.toPre y (abLocus t.G) :=
    GlobalTheory.psiUnitOn_abLocus_pel L₁ L₂ L₃ L₄ L₅ E H R (maximalIdeal R) hAdm t P hT hRo
  have hker : (⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ : PrimeSpectrum R) ∈ abLocus t.G := by
    rw [ker_eq_spMap_bot]
    refine (abLocus_pullback abLocusOne Z.t.semi m.cart.1 _).1 ?_
    obtain ⟨w, hw⟩ := hj
    rw [← hw]
    exact j_mem_abLocus Z w
  obtain ⟨PN, e, he⟩ := GlobalTheory.PelCoordPull.exists_pelUnif_psiCoord E H R N φ t tN mN P (abLocus t.G) hRN hRI hRA
    hNN hNI hNA hloc hRo subset_rfl hψ hker ⟨B, gen, hB, hw⟩
  have hg'l : ¬ IsLocalHom g' := fun h => hg ⟨fun a ha => isUnit_of_map_unit φ a
    (isUnit_of_map_unit g' _ (by rwa [hfac]))⟩
  obtain ⟨ρ, hρ, hc⟩ := GlobalTheory.T.boundary_form_base_change_dvr E H N tN PN hN
    (GlobalTheory.FlatTors.torsionIso_holds E H N _ (admissibleBase_of_completeNormalLocalCharZero hN) tN PN) V hV g' hg' hg'l tV k PV
  refine ⟨ρ ∘ₗ e.toLinearMap, hρ.comp e.surjective, fun x r r' hr hr' => ?_⟩
  obtain ⟨u, hu⟩ := he x r hr
  have := hc (e x) _ r' hu hr'
  rw [map_mul, hfac] at this
  exact (associated_unit_mul_left _ _ (u.isUnit.map g')).symm.trans this

open GlobalTheory.TraitChartForm in

theorem main : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Z.X) (t : SAB H (Sp R)) (_ : SABMap t Z.t ξ) (P : PELUnif (maximalIdeal R) t), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ (χ : Sp W ⟶ Z.X) (tW : SAB H (Sp W)) (_ : SABMap tW Z.t χ) (PW : PELUnif (maximalIdeal W) tW), Set.range (jK W ≫ χ) ⊆ Set.range Z.j → ∀ be ∈ levelForms H 1 PW.D.toPre.X, IsMonomial PW.D.toPre ![ϖ] ![be] → ∀ hs : χ (closedPoint W) ⤳ ξ (closedPoint R), χ (closedPoint W) ≠ ξ (closedPoint R) → ringKrullDim (Z.X.presheaf.stalk (χ (closedPoint W))) = 1 → ∀ (W' : Type) [CommRing W'] [IsDomain W'] [IsLocalRing W'] (ι : W →+* W') (g : R →+* W'), CDvr W' → Irreducible (ι ϖ) → (∀ a, g ((Scheme.stalkClosedPointTo ξ).hom a) = ι ((Scheme.stalkClosedPointTo χ).hom ((Z.X.presheaf.stalkSpecializes hs).hom a))) → ∃ (e : P.D.toPre.X →ₗ[𝓞 E] PW.D.toPre.X), Function.Surjective e ∧ FormAt P.D.toPre g (ι ϖ) (be.compl₁₂ e.toAddMonoidHom.toIntLinearMap e.toAddMonoidHom.toIntLinearMap) := by
  intro E _ _ _ H D l Xo c Z R _ _ _ ξ t m P hR _ _ hT W _ _ _ hW ϖ hϖ χ tW mW PW hχ be _ hmon hs hne _ W' _ _ _ ι g
    hW' hι hcomm
  have hWc := hW
  obtain ⟨hWd, hWa, hW0⟩ := hWc
  have hWc' := hW'
  obtain ⟨hWd', hWa', hW0'⟩ := hWc'
  have cW : IsCN W := ⟨inferInstance, inferInstance, hWa, hW0⟩
  have cW' : IsCN W' := ⟨inferInstance, inferInstance, hWa', hW0'⟩
  have hloc : IsLocalHom ι := ⟨fun a ha => by
    by_contra h
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.1 (hϖ.maximalIdeal_eq.le h)
    exact hι.not_isUnit (isUnit_of_mul_isUnit_left (by rwa [map_mul] at ha))⟩
  have hinj : Function.Injective ι := (injective_iff_map_eq_zero ι).2 fun a ha => by
    by_contra h
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h hϖ
    rw [map_mul, map_pow, (u.isUnit.map ι).mul_right_eq_zero] at ha
    exact pow_ne_zero n hι.ne_zero ha
  have hc : spMap g ≫ ξ = spMap ι ≫ χ := by
    conv_lhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ]
    conv_rhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk χ, ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hs]
    simp only [← Category.assoc, ← Spec.map_comp]
    congr 2
    exact CommRingCat.hom_ext (RingHom.ext hcomm)
  have hg : ¬ IsLocalHom g := fun h => hne (by
    have e : ξ (spMap g (closedPoint W')) = χ (spMap ι (closedPoint W')) :=
      (Scheme.Hom.comp_apply _ _ _).symm.trans
        ((congrArg (fun f : Sp W' ⟶ Z.X => f (closedPoint W')) hc).trans (Scheme.Hom.comp_apply _ _ _))
    have e₁ : spMap g (closedPoint W') = closedPoint R := comap_closedPoint g
    have e₂ : spMap ι (closedPoint W') = closedPoint W := comap_closedPoint ι
    rw [e₁, e₂] at e
    exact e.symm)
  have hgen : ∀ p, (jK W' ≫ spMap g ≫ ξ) p ∈ Set.range Z.j := fun p => by
    let q : Sp (FractionRing W) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing W))
    have hb : spMap ι (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W') = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum W) := by
      rw [← ker_eq_spMap_bot]
      exact PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot ι).1 hinj)
    rw [hc, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, jK_apply_eq_bot W' p, hb, ← jK_apply_eq_bot W q,
      ← Scheme.Hom.comp_apply]
    exact hχ ⟨q, rfl⟩
  obtain ⟨tV, mV, PV, e, -, he⟩ := pullSt E H W W' ι tW PW cW cW' hinj hloc
    (GlobalTheory.FlatTors.torsionIso_holds E H W _ (admissibleBase_of_completeNormalLocalCharZero cW) tW PW)
  obtain ⟨nV⟩ := GlobalTheory.TraitOrder.comp hc.symm mW mV
  obtain ⟨ρ, hρ, hρc⟩ := exists_quot_coord Z ξ t m P hR hT hW' g hg hgen tV nV PV
  refine ⟨e.toLinearMap ∘ₗ ρ, e.surjective.comp hρ, fun y => ?_⟩
  obtain ⟨r, hr⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff P.D.toPre y).2
    (GlobalTheory.PeriodFormCompare.psiIn_top P.D y)
  obtain ⟨u₀, n, hn, hcW⟩ := hmon (e (ρ y))
  obtain ⟨u₁, h₁⟩ := he (ρ y) _ hcW
  refine ⟨r, n 0, hr, by simpa using hn 0, (hρc y r _ hr h₁).trans ?_⟩
  simp only [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_pow]
  exact (associated_unit_mul_left _ _ u₁.isUnit).trans (associated_unit_mul_left _ _ (u₀.isUnit.map ι))

end GlobalTheory.FarTrait
end
end
