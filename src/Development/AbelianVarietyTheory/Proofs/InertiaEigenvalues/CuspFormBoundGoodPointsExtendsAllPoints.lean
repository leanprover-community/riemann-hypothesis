import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtIn
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridgeU
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFiniteIntegralChartCoverFlagSpace
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsValuationSubringComapEqNonunits
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliExistenceAndModuliScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DataAtTraitsOfTraitData
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcClauseClosed
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.FiniteExtensionRamificationEmbedding
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsArcFr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointUniqueAndBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointIntegralOpenDisc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.DegenerationDataBaseChangesExistPid
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFramedPointOfArcBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumSectionValueArcFramedPoint
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcModelWitnessExtension
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLetterAnalyticVectorsIndependentBlockType
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.EqZeroOfMulEventually
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyUnifWitnessDataOfIsUnf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralFramedPointBaseChangeStable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsProperSemiAbelianTripleOfAbelianLocusEqUniv
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SubsingletonOfScalar
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.AdjoinRatiosOfSpanEqTop
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsNormalChartsOfCoveringCharts
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralPointThrough
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIsMaximalTensorProductOfIsLocalHom
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsIntegralCoeffZeroMulOfAevalInv
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsArcDataOfBadReductionFiniteExtensionStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFrameChangeByConstantsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeExistsUniqueInvertible
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeComposeInvertBaseChangeTriangular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexEmbeddingFractionFieldCdvr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormValuesBoundedOnHolomorphicArc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LaurentCoeffNegEqZeroOfBounded
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsOpenImmersionJKPowerSeries

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts GlobalTheory.GoodTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_semiAbelian_triple_of_abelianLocus_eq_univ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : CDVR) (x : Sp T.Fr ⟶ Xo.X) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (_ : SABMap t' Xo.univ.t x) (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))), abLocus G.G = Set.univ → IsProper G.G.hom := by
  first | exact @GlobalTheory.GoodProper.isProper_of_abLocus_eq_univ | exact GlobalTheory.GoodProper.isProper_of_abLocus_eq_univ | (intros; apply GlobalTheory.GoodProper.isProper_of_abLocus_eq_univ <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GoodPts GlobalTheory.DefiniteAbelian
open scoped CategoryTheory.Obj

namespace GlobalTheory.GoodDefinite

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem abLocus_eq_univ_of_definite (Xo : Moduli Dw l) (hq : Dw.q = 0) (T : CDVR) (x : Sp T.Fr ⟶ Xo.X)
    (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m₁ : SABMap t' Xo.univ.t x)
    (m₂ : SABMap t' G (spMap (algebraMap T.V T.Fr))) : abLocus G.G = Set.univ := by
  obtain ⟨m, hm, hw⟩ := exists_w0_relation H
  obtain ⟨b, hb⟩ := Spec.map_surjective (x ≫ Xo.s)
  let β : KA l →+* T.Fr := b.hom
  have hβ : x ≫ Xo.s = spMap β := hb.symm
  have : CharZero T.Fr := (RingHom.charZero_iff β.injective).1 inferInstance
  let ρ : T.Fr := β (baseKA l).ρ
  have hρ : ρ ^ 2 = -(H.d : T.Fr) := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have hm' : (4 : T.Fr) * m = 1 + H.d := by exact_mod_cast hm
  let z : T.Fr := (1 + ρ) / 2
  have hz2 : 2 * z = 1 + ρ := mul_div_cancel₀ _ two_ne_zero
  have hz : z * z + m = z := mul_left_cancel₀ (show (4 : T.Fr) ≠ 0 by norm_num) (by
    linear_combination (2 * z + ρ - 1) * hz2 + hρ + hm')
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : T.V, algebraMap T.V T.Fr z₀ = z := by
    rcases ValuationRing.isInteger_or_isInteger T.V z with h | ⟨u, hu⟩
    · exact h
    · by_cases h0 : z = 0
      · exact ⟨0, by rw [h0, map_zero]⟩
      · refine ⟨1 - m * u, ?_⟩
        rw [map_sub, map_one, map_mul, map_natCast, hu]
        field_simp
        linear_combination -hz
  let L := AlgebraicClosure T.Fr
  let a : T.Fr →+* L := algebraMap T.Fr L
  have : CharZero L := (RingHom.charZero_iff a.injective).1 inferInstance
  have hdet := (Xo.univ.geom L (spMap a ≫ x) (a.comp β) (by rw [Category.assoc, hβ, sp_comp])).1
  have h₁ := actsBy_of_detCond Dw hq _ (spMap a ≫ x) _ (a z)
    (by rw [← map_ofNat a 2, ← map_mul, hz2, map_add, map_one]; rfl) hdet
  have h₂ := (actsBy_pull m₂.cart (m₂.act H.w0) (spMap a) _).1 ((actsBy_pull m₁.cart (m₁.act H.w0) (spMap a) _).2 h₁)
  have := G.semi.smooth
  have := G.semi.separated
  have := G.act.hom H.w0
  have h₃ : ActsBy G.G (G.act.act H.w0) (𝟙 _) z₀ := by
    refine actsBy_of_injective (a.comp (algebraMap T.V T.Fr))
      (a.injective.comp (IsFractionRing.injective T.V T.Fr)) _ _ ?_
    rw [Category.comp_id, ← sp_comp, RingHom.comp_apply, hz₀]
    exact h₂
  refine Set.eq_univ_of_forall fun p K _ _ t _ => ?_
  obtain ⟨j, hj⟩ := Spec.map_surjective t
  have h₄ := actsBy_baseChange (k := K) j.hom (𝟙 _) _ h₃
  have ht : spMap j.hom ≫ 𝟙 _ = t := (Category.comp_id _).trans hj
  rw [ht] at h₄
  obtain ⟨X⟩ := G.semi.fibres K t
  exact isProper_of_actsBy X (OAct.pullback t G.G G.act) H.d_prime hm hw _
    ((actsBy_pull (isGrpPullback_pullback G.G t) (pullback.lift_fst _ _ _) _ _).2 (by rwa [Category.id_comp]))

theorem good_of_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Dw.q = 0 →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), Good y := by
  intro E _ _ _ H Dw l Xo c hq T io y
  obtain ⟨G, t', m₁, m₂, -⟩ := y.2.2
  exact ⟨G, t', m₁, m₂, GlobalTheory.GoodProper.isProper_of_abLocus_eq_univ E H Dw l Xo T _ G t' m₁ m₂
    (abLocus_eq_univ_of_definite Xo hq T _ G t' m₁ m₂)⟩

end GlobalTheory.GoodDefinite
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts GlobalTheory.GoodTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_framed_point_good_reduction_definite_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), Dw.q = 0 → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), Good y := by
  atlas_forward_decl GlobalTheory.GoodDefinite.good_of_definite
end

section
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts GlobalTheory.GoodTransfer

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.GoodRefine

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem sp_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem exists_lift {X : Scheme.{0}} {C A : Type} [CommRing C] [CommRing A] (ι : Sp C ⟶ X) [IsOpenImmersion ι]
    (f : Sp A ⟶ X) (h : Set.range f ⊆ Set.range ι) : ∃ φ : C →+* A, spMap φ ≫ ι = f := by
  refine ⟨(Spec.preimage (IsOpenImmersion.lift ι f h)).hom, ?_⟩
  have : spMap (Spec.preimage (IsOpenImmersion.lift ι f h)).hom = IsOpenImmersion.lift ι f h :=
    Spec.map_preimage _
  rw [this, IsOpenImmersion.lift_fac]

theorem exists_gens {O : Type} [CommRing O] {X : Scheme.{0}} (s : X ⟶ Sp O) [LocallyOfFiniteType s]
    {S : Set X} (hS : IsOpen S) {R V F : Type} [CommRing R] [CommRing V] [IsLocalRing V] [Field F]
    (w : Sp R ⟶ X) (b : O →+* R) (hb : w ≫ s = spMap b) (a : V →+* F) (ψ : R →+* F) (y' : Sp V ⟶ X)
    (hy : spMap ψ ≫ w = spMap a ≫ y') (hr : Set.range y' ⊆ S) :
    ∃ g : R, ψ g ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (i : R →+* R'), IsUnit (i g) → ∃ cs : Finset R',
      (∀ ψ' : R' →+* F, ψ'.comp i = ψ → ∀ x ∈ cs, ψ' x ∈ a.range) ∧
      ∀ (V₁ F₁ : Type) [CommRing V₁] [CommRing F₁] (a₁ : V₁ →+* F₁), Function.Injective a₁ →
        ∀ ψ₁ : R' →+* F₁, (∀ o, ψ₁ (i (b o)) ∈ a₁.range) → (∀ x ∈ cs, ψ₁ x ∈ a₁.range) →
        ∃ y₁ : Sp V₁ ⟶ X, spMap (ψ₁.comp i) ≫ w = spMap a₁ ≫ y₁ ∧ Set.range y₁ ⊆ S := by
  classical
  obtain ⟨C, ι, hι, hmem, hsub⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (X := X) (x := y' (IsLocalRing.closedPoint V)) (U := ⟨S, hS⟩) (hr ⟨_, rfl⟩)
  change Sp C ⟶ X at ι
  have hry : Set.range y' ⊆ Set.range ι := by
    have htop : y' ⁻¹ᵁ ι.opensRange = ⊤ := (IsLocalRing.closedPoint_mem_iff (y' ⁻¹ᵁ ι.opensRange)).1 hmem
    rintro _ ⟨p, rfl⟩
    have : p ∈ y' ⁻¹ᵁ ι.opensRange := by rw [htop]; trivial
    exact this
  obtain ⟨γ, hγ⟩ := exists_lift ι y' hry
  obtain ⟨β, hβ⟩ : ∃ β : O →+* C, spMap β = ι ≫ s := ⟨(Spec.preimage (ι ≫ s)).hom, Spec.map_preimage _⟩
  have hft : β.FiniteType := by
    have : LocallyOfFiniteType (spMap β) := by rw [hβ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  letI := β.toAlgebra
  obtain ⟨t, ht⟩ := (show Algebra.FiniteType O C from hft).out
  let p₀ : Sp F := (⊥ : PrimeSpectrum F)
  have hp : spMap ψ p₀ ∈ w ⁻¹ᵁ ι.opensRange := by
    apply hry
    refine ⟨spMap a p₀, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hy, Scheme.Hom.comp_apply]
  obtain ⟨_, ⟨g, rfl⟩, hg1, hg2⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show (spMap ψ p₀ : PrimeSpectrum R) ∈ ((w ⁻¹ᵁ ι.opensRange : (Sp R).Opens) : Set (Sp R)) from hp)
    (w ⁻¹ᵁ ι.opensRange).isOpen
  refine ⟨g, fun h0 => hg1 (show ψ g ∈ (⊥ : Ideal F) from h0), fun R' _ i hu => ?_⟩
  have hri : Set.range (spMap i ≫ w) ⊆ Set.range ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Hom.comp_apply]
    apply hg2
    intro hm
    exact (show PrimeSpectrum R' from p).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)
  obtain ⟨φ, hφ⟩ := exists_lift ι _ hri
  have hφβ : φ.comp β = i.comp b := by
    apply sp_inj
    rw [← sp_comp, ← sp_comp, hβ, ← hb, ← Category.assoc, hφ, Category.assoc]
  refine ⟨t.image φ, fun ψ' hψ x hx => ?_, fun V₁ F₁ _ _ a₁ ha ψ₁ h1 h2 => ?_⟩
  · obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hx
    have : ψ'.comp φ = a.comp γ := by
      apply sp_inj
      rw [← cancel_mono ι, ← sp_comp, ← sp_comp, Category.assoc, Category.assoc, hφ, hγ, ← hy, ← hψ, ← sp_comp,
        Category.assoc]
    exact ⟨γ u, (DFunLike.congr_fun this u).symm⟩
  · have hall : ∀ u : C, (ψ₁.comp φ) u ∈ a₁.range := by
      intro u
      have hu : u ∈ Algebra.adjoin O (t : Set C) := by rw [ht]; trivial
      induction hu using Algebra.adjoin_induction with
      | mem x hx => exact h2 _ (Finset.mem_image_of_mem _ hx)
      | algebraMap r =>
        have := DFunLike.congr_fun hφβ r
        change ψ₁ ((φ.comp β) r) ∈ _
        rw [this]; exact h1 r
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
    let eq := RingEquiv.ofBijective a₁.rangeRestrict ⟨fun x y h => ha (congrArg Subtype.val h), a₁.rangeRestrict_surjective⟩
    let γ₁ : C →+* V₁ := eq.symm.toRingHom.comp ((ψ₁.comp φ).codRestrict a₁.range hall)
    have hγ₁ : a₁.comp γ₁ = ψ₁.comp φ := by
      ext u
      exact congrArg Subtype.val (eq.apply_symm_apply ((ψ₁.comp φ).codRestrict a₁.range hall u))
    refine ⟨spMap γ₁ ≫ ι, ?_, ?_⟩
    · rw [← Category.assoc, sp_comp, hγ₁, ← sp_comp, ← sp_comp, Category.assoc, Category.assoc, hφ]
    · rintro _ ⟨p, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact hsub ⟨_, rfl⟩

theorem exists_invert {K Ω L V : Type} [Field K] [Field Ω] [Field L] [Algebra K Ω] [Algebra K L] [CommRing V]
    [IsDomain V] [ValuationRing V] [Algebra V L] [IsFractionRing V L] (R : Subalgebra K Ω) (g : R) (ψ : R →ₐ[K] L)
    (hg : ψ g ≠ 0) :
    ∃ (R₀ : Subalgebra K Ω) (hle : R ≤ R₀) (ψ₀ : R₀ →ₐ[K] L) (h : R₀), (g : Ω) ≠ 0 ∧ (g : Ω)⁻¹ ∈ R₀ ∧
      (Algebra.Smooth K R → Algebra.Smooth K R₀) ∧ ψ₀.comp (Subalgebra.inclusion hle) = ψ ∧ (h : Ω) ≠ 0 ∧
      (h : Ω)⁻¹ ∈ R₀ ∧ ψ₀ h ∈ (algebraMap V L).range ∧
      ∀ R' : Subalgebra K Ω, R ≤ R' → (h : Ω) ∈ R' → (h : Ω)⁻¹ ∈ R' → R₀ ≤ R' := by
  have hg0 : (g : Ω) ≠ 0 := fun h0 => hg (by rw [show g = 0 from Subtype.ext h0, map_zero])
  obtain ⟨hle, hinv, hsm, hext⟩ := GlobalTheory.adjoin_ratios_of_span_eq_top K Ω R 2 ![1, g] 1
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩) isUnit_one) hg0 _ rfl
  obtain ⟨ψ₀, hc, hr⟩ := hext L ψ hg
  have hmin : ∀ R' : Subalgebra K Ω, R ≤ R' → (g : Ω)⁻¹ ∈ R' →
      Algebra.adjoin K ((R : Set Ω) ∪ Set.range fun i => ((![1, g] i : R) : Ω) / ((![1, g] 1 : R) : Ω)) ≤ R' := by
    intro R' h1 h2
    apply Algebra.adjoin_le
    rintro z (hz | ⟨i, rfl⟩)
    · exact h1 hz
    · beta_reduce
      rw [div_eq_mul_inv]
      exact R'.mul_mem (h1 (![1, g] i).2) h2
  have e1 : ψ₀ (Subalgebra.inclusion hle g) = ψ g := DFunLike.congr_fun hc g
  rcases ValuationRing.isInteger_or_isInteger V (ψ g) with hi | hi
  · refine ⟨_, hle, ψ₀, Subalgebra.inclusion hle g, hg0, hinv, hsm, hc, hg0, hinv, ?_, fun R' h1 _ h3 => hmin R' h1 h3⟩
    rw [e1]; exact hi
  · refine ⟨_, hle, ψ₀, ⟨_, hinv⟩, hg0, hinv, hsm, hc, inv_ne_zero hg0, ?_, ?_, fun R' h1 h2 _ => hmin R' h1 h2⟩
    · change ((g : Ω)⁻¹)⁻¹ ∈ _
      rw [inv_inv]; exact hle g.2
    · have e2 : ψ₀ ⟨_, hinv⟩ = (ψ g)⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← e1, ← map_mul, ← map_one ψ₀]
        congr 1
        exact Subtype.ext (inv_mul_cancel₀ hg0)
      rw [e2]; exact hi

set_option maxHeartbeats 800000 in

theorem exists_refine_extIn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [Algebra O c.F] [IsFractionRing O c.F] (Y : Model Xo c (algebraMap O c.F)) (S : Set Y.X) (P : PChart Xo c (algebraMap O c.F)) (T : CDVR) (io : c.F →+* T.Fr), IsOpen S → letI := io.toAlgebra; ∀ (e : P.Ω) (he : e ∈ P.es) (ψ : P.R e →ₐ[c.F] T.Fr) (z : FrPt Xo c T.Fr), (∀ g : P.R e, (g : P.Ω) ∈ P.gens → InV T (ψ g)) → FrMap ψ (P.y e he) z → ExtIn Y S T io z.x → ∃ (P' : PChart Xo c (algebraMap O c.F)) (e' : P'.Ω) (he' : e' ∈ P'.es) (ψ' : P'.R e' →ₐ[c.F] T.Fr), (∀ g : P'.R e', (g : P'.Ω) ∈ P'.gens → InV T (ψ' g)) ∧ FrMap ψ' (P'.y e' he') z ∧ ∀ (T₁ : CDVR) (io₁ : c.F →+* T₁.Fr), (∀ a : O, InV T₁ (io₁ (algebraMap O c.F a))) → letI := io₁.toAlgebra; ∀ (ψ₁ : P'.R e' →ₐ[c.F] T₁.Fr) (z₁ : FrPt Xo c T₁.Fr), (∀ g : P'.R e', (g : P'.Ω) ∈ P'.gens → InV T₁ (ψ₁ g)) → FrMap ψ₁ (P'.y e' he') z₁ → ExtIn Y S T₁ io₁ z₁.x := by
  intro E _ _ _ H Dw l Xo c O _ _ _ _ Y S P T io hS
  letI := io.toAlgebra
  intro e he ψ z hgen hz hext
  classical
  obtain ⟨y', z₀, hz1, hz2, hz3, hz4⟩ := hext
  haveI : IsProper Y.s := by
    obtain ⟨N, i, hi, hs⟩ := Y.proj
    haveI := isProper_str O N
    rw [← hs]; infer_instance
  let zR : Sp (P.R e) ⟶ Xo.XF c := pullback.lift (P.y e he).x (spMap (algebraMap c.F (P.R e)))
    (by rw [(P.y e he).x_over, sp_comp]; rfl)
  have hzR1 : zR ≫ pullback.fst _ _ = (P.y e he).x := pullback.lift_fst _ _ _
  have hzR2 : zR ≫ pullback.snd _ _ = spMap (algebraMap c.F (P.R e)) := pullback.lift_snd _ _ _
  have hb : (zR ≫ Y.j) ≫ Y.s = spMap ((algebraMap c.F (P.R e)).comp (algebraMap O c.F)) := by
    rw [Model.j, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over,
      ← Category.assoc, hzR2, sp_comp]
  have hz0 : spMap ψ.toRingHom ≫ zR = z₀ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hzR1, hz1, hz.1]
    · rw [Category.assoc, hzR2, hz2, sp_comp]
      exact congrArg spMap (RingHom.ext fun x => ψ.commutes x)
  obtain ⟨g, hg, hcs⟩ := exists_gens Y.s hS (zR ≫ Y.j) _ hb (algebraMap T.V T.Fr) ψ.toRingHom y'
    (by rw [← Category.assoc, hz0, hz3]) hz4
  obtain ⟨R₀, hle, ψ₀, h, hg0, hginv, hsm, hc, hh0, hhinv, hhV, hmin⟩ := exists_invert (V := T.V) (P.R e) g ψ hg
  obtain ⟨cs, hcs1, hcs2⟩ := hcs R₀ (Subalgebra.inclusion hle).toRingHom
    (IsUnit.of_mul_eq_one ⟨_, hginv⟩ (Subtype.ext (mul_inv_cancel₀ hg0)))
  obtain ⟨G, hGdef⟩ : ∃ G : Finset P.Ω, ∀ x, x ∈ G ↔ x ∈ P.gens ∨ ∃ u ∈ insert h cs, (u : P.Ω) = x :=
    ⟨P.gens ∪ (insert h cs).image Subtype.val, fun x => by rw [Finset.mem_union, Finset.mem_image]⟩
  have hG : (P.gens : Set P.Ω) ⊆ G := fun g hg => (hGdef g).2 (Or.inl hg)
  have hGc : ∀ x ∈ insert h cs, (x : P.Ω) ∈ G := fun x hx => (hGdef x).2 (Or.inr ⟨x, hx, rfl⟩)
  have hGh : (h : P.Ω) ∈ G := hGc h (Finset.mem_insert_self _ _)
  obtain ⟨he0, heB⟩ := P.es_mem e he
  let R' : Subalgebra c.F P.Ω := Algebra.adjoin c.F (insert (e * h)⁻¹ (G : Set P.Ω))
  have hGR : ∀ x ∈ G, x ∈ R' := fun x hx => Algebra.subset_adjoin (Or.inr hx)
  have hi : (e * h)⁻¹ ∈ R' := Algebra.subset_adjoin (Or.inl rfl)
  have heR : e ∈ R' := by
    refine (Subring.closure_le (t := R'.toSubring)).2 ?_ heB
    rintro x (⟨o, rfl⟩ | hx)
    · exact R'.algebraMap_mem _
    · exact hGR _ (hG hx)
  have hle' : P.R e ≤ R' := by
    apply Algebra.adjoin_le
    rintro x (rfl | hx)
    · have : e⁻¹ = h * (e * h)⁻¹ := by field_simp
      rw [this]; exact R'.mul_mem (hGR _ hGh) hi
    · exact hGR _ (hG hx)
  have h0' : R₀ ≤ R' := by
    refine hmin R' hle' (hGR _ hGh) ?_
    have : (h : P.Ω)⁻¹ = e * (e * h)⁻¹ := by field_simp
    rw [this]; exact R'.mul_mem heR hi
  have h'0 : R' ≤ R₀ := by
    apply Algebra.adjoin_le
    rintro x (rfl | hx)
    · rw [mul_inv]
      exact R₀.mul_mem (hle (Algebra.subset_adjoin (Or.inl rfl))) hhinv
    · rcases (hGdef x).1 hx with hx | hx
      · exact hle (Algebra.subset_adjoin (Or.inr hx))
      · obtain ⟨u, -, rfl⟩ := hx
        exact u.2
  have hsm' : Algebra.Smooth c.F R' := le_antisymm h0' h'0 ▸ hsm (P.sm e he)
  obtain ⟨y₁, hy₁⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _
    (Subalgebra.inclusion hle') (P.y e he)
  have k1 : ∀ x : R', (x : P.Ω) ∈ G → InV T ((ψ₀.comp (Subalgebra.inclusion h'0)) x) := by
    intro x hx
    rcases (hGdef _).1 hx with hx' | hx'
    · have e2 := hgen ⟨x, Algebra.subset_adjoin (Or.inr hx')⟩ hx'
      have e3 := DFunLike.congr_fun hc ⟨x, Algebra.subset_adjoin (Or.inr hx')⟩
      rw [← e3] at e2
      exact e2
    · obtain ⟨u, hu, hux⟩ := hx'
      have e1 : Subalgebra.inclusion h'0 x = u := Subtype.ext hux.symm
      change ψ₀ (Subalgebra.inclusion h'0 x) ∈ (algebraMap T.V T.Fr).range
      rw [e1]
      rcases Finset.mem_insert.1 hu with rfl | hu
      · exact hhV
      · exact hcs1 ψ₀.toRingHom (RingHom.ext fun x => DFunLike.congr_fun hc x) u hu
  have k2 : FrMap (ψ₀.comp (Subalgebra.inclusion h'0)) y₁ z := by
    refine frMap_cancel _ _ _ (Subalgebra.inclusion hle') _ (P.y e he) _ _ hy₁ ?_
    have : (ψ₀.comp (Subalgebra.inclusion h'0)).comp (Subalgebra.inclusion hle') = ψ :=
      AlgHom.ext fun x => DFunLike.congr_fun hc x
    exact this.symm ▸ hz
  have k3 : ∀ (T₁ : CDVR) (io₁ : c.F →+* T₁.Fr), (∀ a : O, InV T₁ (io₁ (algebraMap O c.F a))) →
      letI := io₁.toAlgebra; ∀ (ψ₁ : R' →ₐ[c.F] T₁.Fr) (z₁ : FrPt Xo c T₁.Fr),
      (∀ g : R', (g : P.Ω) ∈ G → InV T₁ (ψ₁ g)) → FrMap ψ₁ y₁ z₁ → ExtIn Y S T₁ io₁ z₁.x := by
    intro T₁ io₁ hO
    letI := io₁.toAlgebra
    intro ψ₁ z₁ h2 hz₁
    have hz₁' := frMap_trans _ _ _ _ _ _ _ _ hy₁ hz₁
    obtain ⟨y₂, hy₂, hr₂⟩ := hcs2 T₁.V T₁.Fr (algebraMap T₁.V T₁.Fr) (IsFractionRing.injective _ _)
      (ψ₁.comp (Subalgebra.inclusion h0')).toRingHom
      (fun o => by
        have e1 := (ψ₁.comp (Subalgebra.inclusion hle')).commutes (algebraMap O c.F o)
        have e2 := hO o
        change algebraMap c.F T₁.Fr _ ∈ (algebraMap T₁.V T₁.Fr).range at e2
        rw [← e1] at e2
        exact e2)
      (fun x hx => h2 (Subalgebra.inclusion h0' x) (hGc x (Finset.mem_insert_of_mem hx)))
    refine ⟨y₂, spMap (ψ₁.comp (Subalgebra.inclusion hle')).toRingHom ≫ zR, ?_, ?_, ?_, hr₂⟩
    · rw [Category.assoc, hzR1]; exact hz₁'.1.symm
    · rw [Category.assoc, hzR2, sp_comp]
      exact congrArg spMap (RingHom.ext fun x => (ψ₁.comp (Subalgebra.inclusion hle')).commutes x)
    · rw [Category.assoc]; exact hy₂
  have hes : ∀ e' ∈ ({e * h} : Finset P.Ω), e' = e * h := fun e' he' => Finset.mem_singleton.1 he'
  let yy : ∀ e' ∈ ({e * h} : Finset P.Ω), FrPt Xo c (Algebra.adjoin c.F (insert e'⁻¹ (G : Set P.Ω))) :=
    fun e' he' => (hes e' he').symm ▸ y₁
  refine ⟨{ Ω := P.Ω
            gens := G
            frac := ?_
            es := {e * h}
            es_ne := Finset.singleton_nonempty _
            es_mem := fun e' he' => ?_
            sm := fun e' he' => ?_
            yg := P.yg
            y := yy
            gen := fun e' he' => ?_
            int := fun e' he' => ?_ }, e * h, Finset.mem_singleton_self _,
            ψ₀.comp (Subalgebra.inclusion h'0), k1, k2, k3⟩
  · rw [eq_top_iff, ← P.frac]
    exact Subfield.closure_mono (Set.union_subset_union_right _ hG)
  · obtain rfl := hes e' he'
    exact ⟨mul_ne_zero he0 hh0, mul_mem (Subring.closure_mono (Set.union_subset_union_right _ hG) heB)
      (Subring.subset_closure (Or.inr hGh))⟩
  · obtain rfl := hes e' he'
    exact hsm'
  · obtain rfl := hes e' he'
    exact frMap_cancel _ _ _ (Subalgebra.inclusion hle') _ (P.y e he) _ _ hy₁ (P.gen e he)
  · obtain rfl := hes e' he'
    intro T₁ io₁
    letI := io₁.toAlgebra
    intro ψ₁ h1 h2 z₁ hz₁
    refine P.int e he T₁ io₁ (ψ₁.comp (Subalgebra.inclusion hle')) h1 (fun g hg => ?_) z₁
      (frMap_trans _ _ _ _ _ _ _ _ hy₁ hz₁)
    exact h2 (Subalgebra.inclusion hle' g) (hG hg)

end GlobalTheory.GoodRefine
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts GlobalTheory.GoodTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_refined_flagChart_integral_points_in_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [Algebra O c.F] [IsFractionRing O c.F] (Y : Model Xo c (algebraMap O c.F)) (S : Set Y.X) (P : PChart Xo c (algebraMap O c.F)) (T : CDVR) (io : c.F →+* T.Fr), IsOpen S → letI := io.toAlgebra; ∀ (e : P.Ω) (he : e ∈ P.es) (ψ : P.R e →ₐ[c.F] T.Fr) (z : FrPt Xo c T.Fr), (∀ g : P.R e, (g : P.Ω) ∈ P.gens → InV T (ψ g)) → FrMap ψ (P.y e he) z → ExtIn Y S T io z.x → ∃ (P' : PChart Xo c (algebraMap O c.F)) (e' : P'.Ω) (he' : e' ∈ P'.es) (ψ' : P'.R e' →ₐ[c.F] T.Fr), (∀ g : P'.R e', (g : P'.Ω) ∈ P'.gens → InV T (ψ' g)) ∧ FrMap ψ' (P'.y e' he') z ∧ ∀ (T₁ : CDVR) (io₁ : c.F →+* T₁.Fr), (∀ a : O, InV T₁ (io₁ (algebraMap O c.F a))) → letI := io₁.toAlgebra; ∀ (ψ₁ : P'.R e' →ₐ[c.F] T₁.Fr) (z₁ : FrPt Xo c T₁.Fr), (∀ g : P'.R e', (g : P'.Ω) ∈ P'.gens → InV T₁ (ψ₁ g)) → FrMap ψ₁ (P'.y e' he') z₁ → ExtIn Y S T₁ io₁ z₁.x := by
  atlas_forward_decl GlobalTheory.GoodRefine.exists_refine_extIn
end

section
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts GlobalTheory.GoodTransfer

namespace GlobalTheory.ChartIntegral

open GlobalTheory.Reg.NormalCharts GlobalTheory.PlaceCompletion

theorem exists_quotient_of_bounded (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O] [CommRing A] [IsDomain A]
    [Algebra O A] [Algebra.FiniteType O A] [IsIntegrallyClosed A]
    (hOA : Function.Injective (algebraMap O A)) (e : A) (he : e ≠ 0) (f : FractionRing A)
    (hf : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →+* V), (∀ a, φ (algebraMap O A a) = algebraMap O V a) → φ e ≠ 0 →
      ∀ a b : A, f * algebraMap A _ b = algebraMap A _ a → φ b ≠ 0 → φ b ∣ φ a) :
    ∃ x s : A, s - 1 ∈ Ideal.map (algebraMap O A) (IsLocalRing.maximalIdeal O) ∧
      f * algebraMap A _ s = algebraMap A _ x := by
  have hid : Function.Injective (algebraMap O O) := fun _ _ h => h
  have : IsLocalHom (algebraMap O O) := ⟨fun _ h => h⟩
  obtain ⟨s, hs, hint⟩ := GlobalTheory.isIntegral_mul_of_bounded_at_points O O hid
    (GlobalTheory.exists_integral_point_of_complete_case
      (fun O B _ _ _ _ _ _ _ _ _ _ M hM hsp e he => GlobalTheory.exists_integral_point_through O B M hM hsp e he)
      O O hid) A (FractionRing A) hOA e he f
    (fun V _ _ _ _ _ φ hφ => hf V φ (fun a => RingHom.congr_fun hφ a))
  obtain ⟨x, hx⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  exact ⟨x, s, hs, by rw [hx, _root_.mul_comm]⟩

theorem integral_of_integral_at_algebraic_points :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (la : HeightOneSpectrum (𝓞 K)) (gens : Finset Ω) (e : Ω), Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = ⊤ → e ≠ 0 → e ∈ Subring.closure (Set.range ((algebraMap K Ω).comp (la.valuation K).valuationSubring.subtype) ∪ (gens : Set Ω)) → Algebra.Smooth K (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))) → ∀ r : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (∀ (T : CDVR) (io : K →+* T.Fr) (n : ℕ), OverLa la T.V io n → T.FinRes → ∀ ψ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) →+* T.Fr, (∀ k : K, ψ (algebraMap K _ k) = io k) → (∀ g : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (g : Ω) ∈ gens → InV T (ψ g)) → InV T (ψ r)) → ∀ (T : CDVR) (io : K →+* T.Fr) (n : ℕ), OverLa la T.V io n → ∀ ψ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) →+* T.Fr, (∀ k : K, ψ (algebraMap K _ k) = io k) → (∀ g : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (g : Ω) ∈ gens → InV T (ψ g)) → InV T (ψ r) := by
  intro K Ω _ _ _ _ la gens e hgen he hemem hsm r hr T io n ho ψ hψK hψg
  obtain ⟨T₀, io₀, hov, hfin, hinit⟩ := exists_initial_completion K la
  have hβ : ∀ a : (la.valuation K).valuationSubring,
      io₀ ((la.valuation K).valuationSubring.subtype a) ∈ Set.range (algebraMap T₀.V T₀.Fr) := fun a =>
    exists_algebraMap_eq_of_valV_le_one (by
      rw [valV_eq_pow_of_overLa hov]
      exact pow_le_one₀ zero_le a.2)
  obtain ⟨J, finJ, A, acr, adom, alg, α, hA, hK, hg, hcov⟩ :=
    GlobalTheory.exists_normal_charts_over_dvr K Ω T₀.V io₀ gens {e} hgen
      (fun e' he' => by
        obtain rfl := Finset.mem_singleton.1 he'
        refine ⟨he, Subring.closure_mono ?_ hemem⟩
        refine Set.union_subset_union_left _ ?_
        rintro _ ⟨a, rfl⟩
        exact ⟨_, hβ a, rfl⟩)
      (fun e' he' => by
        obtain rfl := Finset.mem_singleton.1 he'
        exact hsm)
  obtain ⟨g, χ, hloc, hχio, hχg, -⟩ := hinit T io n ho
  have hχg' : ∀ a, χ (algebraMap T₀.V T₀.Fr a) = algebraMap T.V T.Fr (g a) :=
    fun a => RingHom.congr_fun hχg a
  obtain ⟨j, φ, hφW, hφO, hφψ⟩ := hcov e (Finset.mem_singleton_self e) T.Fr (imageVal T.V T.Fr) χ ψ
    (fun k => (hψK k).trans (RingHom.congr_fun hχio k).symm)
    (fun a => (mem_imageVal _).2 ⟨g a, (hχg' a).symm⟩)
    (fun x hx => (mem_imageVal _).2 (hψg x hx))
  obtain ⟨φ', hφ'⟩ := exists_corestrict (V := T.V) φ fun x => (mem_imageVal _).1 (hφW x)
  have hc : ∀ a, φ' (algebraMap T₀.V (A j) a) = g a := fun a =>
    IsFractionRing.injective T.V T.Fr (by rw [hφ', hφO, hχg'])
  obtain ⟨hft, -, hic⟩ := hA j
  have hOA : Function.Injective (algebraMap T₀.V (A j)) := by
    intro a b hab
    apply IsFractionRing.injective T₀.V T₀.Fr
    apply χ.injective
    exact (hφO a).symm.trans ((congrArg φ hab).trans (hφO b))
  obtain ⟨eb, heb⟩ : α j e ∈ Set.range (algebraMap (A j) (FractionRing (A j))) := by
    refine (Subring.closure_le (t := (algebraMap (A j) (FractionRing (A j))).range.comap (α j))).2 ?_ hemem
    rintro x (⟨a, rfl⟩ | hx)
    · obtain ⟨x, hx⟩ := hβ a
      have := hK j ((la.valuation K).valuationSubring.subtype a) x 1 (by rw [map_one, _root_.mul_one, hx])
      rw [map_one, map_one, _root_.mul_one] at this
      exact ⟨_, this.symm⟩
    · exact hg j x hx
  have heb0 : eb ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, map_eq_zero] at heb
    exact he heb
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T₀.V
  obtain ⟨x, s, hs, hxs⟩ := exists_quotient_of_bounded T₀.V (A j) hOA eb heb0 (α j r) (by
    intro V _ _ _ _ _ ρ hρ h0 a b hab hb
    obtain ⟨hinj, hlocV, hcpl, hch, hfin'⟩ := GlobalTheory.dvr_finite_over_complete_dvr T₀.V V
    obtain ⟨χ', m, hm, hχ', hv⟩ := exists_ramification (K' := FractionRing V) (F := T₀.Fr)
      (algebraMap T₀.V V) hinj hlocV
    obtain ⟨ψ', hψ'⟩ := (GlobalTheory.Reg.openChart_regular_away K Ω T₀.V (A j) io₀ gens e (α j) eb ϖ hϖ he heb
      (hK j) (hg j)).2 (FractionRing V) ((algebraMap V (FractionRing V)).comp ρ) (by
        change algebraMap V (FractionRing V) (ρ _) ≠ 0
        rw [map_mul, hρ]
        simpa using mul_ne_zero ((map_ne_zero_iff _ hinj).2 hϖ.ne_zero) h0)
    replace hψ' : ∀ (r : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))) (x s : A j),
        α j r * algebraMap (A j) _ s = algebraMap (A j) _ x →
        ψ' r * algebraMap V _ (ρ s) = algebraMap V _ (ρ x) := hψ'
    let T' : CDVR := { V := V }
    have hψK' : ∀ k : K, ψ' (algebraMap K _ k) = (χ'.comp io₀) k := by
      intro k
      obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := T₀.V) (io₀ k)
      have hb0 : algebraMap T₀.V T₀.Fr b ≠ 0 := by simpa using nonZeroDivisors.ne_zero hb
      have h1 : io₀ k * algebraMap T₀.V _ b = algebraMap T₀.V _ a := by
        rw [← hab, div_mul_cancel₀ _ hb0]
      have h2 := hψ' (algebraMap K _ k) _ _ (hK j k a b h1)
      rw [hρ, hρ, ← hχ', ← hχ', ← h1, map_mul] at h2
      exact mul_right_cancel₀ ((map_ne_zero χ').2 hb0) h2
    obtain ⟨v, hv'⟩ : ψ' r ∈ Set.range (algebraMap V (FractionRing V)) :=
      hr T' (χ'.comp io₀) (m * 1) (hov.bc χ' hm hv) (hfin' hfin) ψ' hψK' (fun y hy => by
        obtain ⟨x, hx⟩ := hg j y hy
        have := hψ' y x 1 (by rw [map_one, _root_.mul_one, hx])
        rw [map_one, map_one, _root_.mul_one] at this
        exact ⟨ρ x, this.symm⟩)
    refine ⟨v, IsFractionRing.injective V (FractionRing V) ?_⟩
    rw [← hψ' r a b hab, ← hv', map_mul, _root_.mul_comm])
  have hm : φ' (s - 1) ∈ IsLocalRing.maximalIdeal T.V := by
    refine (Ideal.map_le_iff_le_comap (K := (IsLocalRing.maximalIdeal T.V).comap φ')).2 ?_ hs
    intro a ha
    change φ' (algebraMap T₀.V (A j) a) ∈ IsLocalRing.maximalIdeal T.V
    rw [hc]
    exact fun hu => ha (hloc.map_nonunit a hu)
  have hu : IsUnit (φ' s) := by
    by_contra hnu
    have h1 : φ' s - φ' (s - 1) ∈ IsLocalRing.maximalIdeal T.V := sub_mem hnu hm
    rw [← map_sub, sub_sub_cancel, map_one] at h1
    exact h1 isUnit_one
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have h2 := hφψ r x s hxs
  refine ⟨φ' x * w, ?_⟩
  rw [map_mul, hφ', ← h2, ← hφ', _root_.mul_assoc, ← map_mul, hw, map_one, _root_.mul_one]

end GlobalTheory.ChartIntegral
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts GlobalTheory.GoodTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_of_integral_at_algebraic_points_smooth : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (la : HeightOneSpectrum (𝓞 K)) (gens : Finset Ω) (e : Ω), Subfield.closure (Set.range (algebraMap K Ω) ∪ (gens : Set Ω)) = ⊤ → e ≠ 0 → e ∈ Subring.closure (Set.range ((algebraMap K Ω).comp (la.valuation K).valuationSubring.subtype) ∪ (gens : Set Ω)) → Algebra.Smooth K (Algebra.adjoin K (insert e⁻¹ (gens : Set Ω))) → ∀ r : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (∀ (T : CDVR) (io : K →+* T.Fr) (n : ℕ), OverLa la T.V io n → T.FinRes → ∀ ψ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) →+* T.Fr, (∀ k : K, ψ (algebraMap K _ k) = io k) → (∀ g : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (g : Ω) ∈ gens → InV T (ψ g)) → InV T (ψ r)) → ∀ (T : CDVR) (io : K →+* T.Fr) (n : ℕ), OverLa la T.V io n → ∀ ψ : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)) →+* T.Fr, (∀ k : K, ψ (algebraMap K _ k) = io k) → (∀ g : Algebra.adjoin K (insert e⁻¹ (gens : Set Ω)), (g : Ω) ∈ gens → InV T (ψ g)) → InV T (ψ r) := by
  atlas_forward_decl GlobalTheory.ChartIntegral.integral_of_integral_at_algebraic_points
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts
  GlobalTheory.GoodTransfer

namespace GlobalTheory.ArcFrame

open Matrix GlobalTheory.LieEigen MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts)

theorem iwasawa_lower {V F : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field F] [Algebra V F]
    [IsFractionRing V F] {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (hA : A.det ≠ 0) :
    ∃ (k : Matrix (Fin n) (Fin n) V) (L : Matrix (Fin n) (Fin n) F), IsUnit k.det ∧ (∀ i j, i < j → L i j = 0) ∧
      (∀ i, L i i ≠ 0) ∧ A = L * k.map (algebraMap V F) := by
  obtain ⟨k, U, hk, hU, hd, e⟩ := GlobalTheory.ValIwasawa.iwasawa_matrix (V := V) Aᵀ (by rwa [det_transpose])
  refine ⟨kᵀ, Uᵀ, by rwa [det_transpose], fun i j h => hU h, hd, ?_⟩
  rw [← transpose_transpose A, e, transpose_mul, transpose_map]

section Lie

variable {R O : Type} [CommRing R] [IsLocalRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
  [Smooth G.hom] (act : OAct O G) {n : ℕ} {v : Fin n → (epsR R ⟶ G)}

theorem eig_prodPts (hv : ∀ i, IsTangent (v i)) (x : O) (s : R)
    (he : ∀ i, (v i ≫ act.act x).left = spMap (epsScaleR s) ≫ (v i).left) (c : Fin n → R) :
    (prodPts c v ≫ act.act x).left = spMap (epsScaleR s) ≫ (prodPts c v).left := by
  have := act.hom x
  have e : prodPts c v ≫ act.act x = prodPts c fun i => v i ≫ act.act x := by
    refine (map_list_prod (IsMonHom.monoidHom (act.act x) _) _).trans ?_
    rw [prodPts, List.map_ofFn]
    exact congrArg (fun f => (List.ofFn f).prod) (funext fun i => Category.assoc _ (v i) (act.act x))
  have e₁ : ∀ i, v i ≫ act.act x = prodPts (s • Pi.single i 1) v := fun i => by
    rw [prodPts_smul, ← (Chart.isLieComb_iff _ _ _).1 (IntModelExists.isLieComb_single hv i)]
    exact Over.OverMorphism.ext (he i)
  have e₂ : ∑ i, c i • (s • Pi.single i (1 : R) : Fin n → R) = s • c := by
    ext j; simp [Pi.single_apply, mul_comm]
  rw [e, funext e₁, prodPts_prodPts hv, e₂, prodPts_smul]
  rfl

omit [IsLocalRing R] [Smooth G.hom] in

theorem existsUnique_change (hv : ∀ i, IsTangent (v i)) (k : Matrix (Fin n) (Fin n) R) (hk : IsUnit k.det)
    {w : epsR R ⟶ G} (h : ∃! cf : Fin n → R, IsLieComb cf v w) :
    ∃! cf : Fin n → R, IsLieComb cf (fun i => prodPts (k i) v) w := by
  have key : ∀ cf : Fin n → R, IsLieComb cf (fun i => prodPts (k i) v) w ↔ IsLieComb (cf ᵥ* k) v w := fun cf => by
    rw [Chart.isLieComb_iff, Chart.isLieComb_iff, vecMul_eq_sum]
    exact Eq.congr_right (prodPts_prodPts hv cf fun i => k i)
  obtain ⟨d, hd, hu⟩ := h
  refine ⟨d ᵥ* k⁻¹, (key _).2 ?_, fun cf hcf => ?_⟩
  · rwa [vecMul_vecMul, nonsing_inv_mul _ hk, vecMul_one]
  · rw [← hu _ ((key _).1 hcf), vecMul_vecMul, mul_nonsing_inv _ hk, vecMul_one]

end Lie

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem arcBasis_change (hG : Out.GlobalFnsSt) {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] {b : O →+* A} {a : ArcIn Dw l β A b} {χ : Sp (PowerSeries A) ⟶ Y.X} (W : Wit Y a χ)
    {ρ : (E →+* ℂ) → (𝓞 E →+* A)} {e e' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)}
    (h : ArcBasis W ρ e) (k : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A)
    (hk : ∀ τ, IsUnit (k τ).det) (he : ∀ τ i, GtComb (k τ i) (e τ) (e' τ i)) :
    ArcBasis W ρ e' ∧ ∀ τ i, GtTanR (e' τ i) := by
  obtain ⟨v, hi, hb⟩ := h
  have := W.t.semi.smooth
  let k' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (PowerSeries A) :=
    fun τ => (k τ).map (PowerSeries.C (R := A))
  have hk' : ∀ τ, IsUnit (k' τ).det := fun τ => by
    have := (hk τ).map (PowerSeries.C (R := A))
    rwa [RingHom.map_det] at this
  have ht : ∀ τ i, IsTangent (v τ i) := fun τ i => ((hb τ).1 i).1
  have img : ∀ τ i, LieImg W (e' τ i) (prodPts (k' τ i) (v τ)) := fun τ i =>
    (GlobalTheory.T.lieImg_iff_isLieComb_of_gtComb hG E H Dw l Xo c O β Y A b a χ W _ _ (e τ) _ (v τ) _ (hi τ) (he τ i)).2
      ((Chart.isLieComb_iff _ _ _).2 rfl)
  refine ⟨⟨_, img, fun τ => ⟨fun i => ⟨isTangent_prodPts (ht τ) _, fun x => ?_⟩, fun w hw hw' => ?_⟩⟩, fun τ i =>
    ((GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hG E H Dw l Xo c O β Y A b a χ W _).2 _ (img τ i)).2 (isTangent_prodPts (ht τ) _)⟩
  · exact eig_prodPts W.t.act (ht τ) x _ (fun j => ((hb τ).1 j).2 x) _
  · exact existsUnique_change (ht τ) (k' τ) (hk' τ) ((hb τ).2 w hw hw')

theorem exists_values (c : Coeff l) (V : ValuationSubring c.F) :
    ∃ r z : V, ((V.subtype r : c.F) : ℂ) = H.rt0 ∧ ((V.subtype z : c.F) : ℂ) = zeta l.A := by
  have key : ∀ (x : c.F) (n : ℕ), 0 < n → ∀ m : ℤ, x ^ n = m → x ∈ V := fun x n hn m h =>
    IntModelExists.mem_of_isIntegral _ (IsIntegral.of_pow hn (by
      rw [h]; simpa using isIntegral_algebraMap (R := ℤ) (A := c.F) (x := m)))
  refine ⟨⟨⟨_, GlobalTheory.HostModel.sqrtNegDisc_mem_coeffField c⟩, key _ 2 two_pos (-(H.d : ℤ)) ?_⟩,
    ⟨⟨_, GlobalTheory.HostModel.zeta_A_mem_coeff c⟩, key _ l.A l.A_pos 1 ?_⟩, rfl, rfl⟩
  · apply Subtype.ext
    simpa using H.sqrt_neg_disc_sq
  · apply Subtype.ext
    simpa [zeta] using (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one

theorem exists_arcFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (T : CDVR) (io : c.F →+* T.Fr) (b : V →+* T.V) (a : ArcIn Dw l V.subtype T.V b) (χ : Sp (PowerSeries T.V) ⟶ Y.X) (W : Wit Y a χ) (ev : PowerSeries T.V →+* T.V) (z : Sp T.Fr ⟶ Xo.XF c), PushInvertible Y.t.G Y.t.PP.L → (algebraMap T.V T.Fr).comp b = io.comp V.subtype → χ ≫ Y.s = spMap (PowerSeries.C (R := T.V)) ≫ spMap b → (∀ x, ev (PowerSeries.C x) = x) → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp ev) ≫ χ → letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, z ≫ pullback.fst _ _ = y.x → ∃ (ρ : (E →+* ℂ) → (𝓞 E →+* T.V)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR T.V)) (th : a.D₀.P.L.Sec) (y₀ : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), ArcBasis W ρ e ∧ ThNZ th ∧ (∀ τ k, GtTanR (e τ k)) ∧ (∀ τ x, io (embK c τ x) = algebraMap T.V T.Fr (ρ τ x)) ∧ IsArcFr W e th ((algebraMap T.V T.Fr).comp ev) y₀ ∧ FrBor t y₀ y := by
  intro E _ _ _ H Dw l Xo c V Y T io b a χ W ev z hP hb hχ hev hz hj
  letI := io.toAlgebra
  intro y hy
  obtain ⟨hL, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  have hG := hL.globalFns
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  let em : (E →+* ℂ) → (𝓞 E →+* V) := fun τ => (embK c τ).codRestrict V.toSubring fun x =>
    IntModelExists.mem_of_isIntegral _ ((RingOfIntegers.isIntegral x).map (embK c τ).toIntAlgHom)
  let ρ : (E →+* ℂ) → (𝓞 E →+* T.V) := fun τ => b.comp (em τ)
  have hρ : ∀ τ x, algebraMap T.V T.Fr (ρ τ x) = io (embK c τ x) := fun τ x => RingHom.congr_fun hb (em τ x)
  have hC : ((algebraMap T.V T.Fr).comp ev).comp (PowerSeries.C (R := T.V)) = algebraMap T.V T.Fr :=
    RingHom.ext fun x => congrArg (algebraMap T.V T.Fr) (hev x)
  have hm : Mono Y.j := by
    have : IsPreimmersion (spMap V.subtype) :=
      IsPreimmersion.of_isLocalization (R := V) (S := c.F) (nonZeroDivisors V)
    have := Y.jQ_open
    unfold Model.j
    infer_instance
  obtain ⟨e₁, -, he₁⟩ := GlobalTheory.ConstBasis.exists_arcBasis hL hL₂ E H Dw l Xo c _ _ Y T.V b a χ W ρ io hb.symm hρ
    (exists_values c V)
  obtain ⟨th, hth, -⟩ := GlobalTheory.KeyOnPol.exists_generator hL.secBaseChange a.D₀.P
  obtain ⟨y₁, hx₁, hy₁⟩ := GlobalTheory.ArcQ.exists_isArcFr hL hL₂ E H Dw l Xo c _ _ Y T.V b a χ W ρ e₁ th he₁ hth (Or.inr hP)
    T.Fr ((algebraMap T.V T.Fr).comp ev) z (by rw [hC]; exact IntModelExists.flat_of_injective _ hinj) hj
    (by rw [← Category.assoc, hy]; exact y.2)
    (fun τ x => ((RingHom.congr_fun hC (ρ τ x)).trans (hρ τ x)).symm)
  obtain ⟨g, s, hg⟩ := (frChg_exists_unique_units E H Dw l Xo c T.Fr (fun _ => 1) 1 y₁).2.2.2 y (hx₁.trans hy).symm
  obtain ⟨hgu, hsu⟩ := (frChg_exists_unique_units E H Dw l Xo c T.Fr g s y₁).2.2.1 y hg
  choose k L hk hL0 hLd hkL using fun τ => iwasawa_lower (V := T.V) (g τ) (hgu τ).ne_zero
  choose e he using fun τ i => ConstLie.exists_gtComb (k τ i) (e₁ τ)
  obtain ⟨hbe, hte⟩ := arcBasis_change hG W he₁ k hk he
  obtain ⟨y₀, hy₀⟩ := (frChg_exists_unique_units E H Dw l Xo c T.Fr (fun τ => (k τ).map (algebraMap T.V T.Fr)) 1
    y₁).1 (fun τ => by
      have := (hk τ).map (algebraMap T.V T.Fr)
      rwa [RingHom.map_det] at this) isUnit_one
  obtain ⟨hcomp, -, -, hbor⟩ := frChg_calculus E H Dw l Xo c T.Fr
  refine ⟨ρ, e, th, y₀, fun i => match i with
    | none => hsu.unit
    | some p => Units.mk0 _ (hLd p.1 p.2), hbe, hth, hte, fun τ x => (hρ τ x).symm, ?_, ?_⟩
  · refine GlobalTheory.T.arcFrame_change_by_constants hL hL₂ E H Dw l Xo c _ _ Y T.V b a χ W e₁ e th th k 1 hth he (ThMul.refl th) T.Fr _ y₁ y₀
      hm hy₁ ?_
    rw [hC, map_one, map_one]
    exact hy₀
  · refine (hbor _ _ _).2 ⟨L, fun _ _ => rfl, hL0, (hcomp _ L _ _ y₁ y₀ y hy₀).2 ?_⟩
    rw [_root_.mul_one, ← funext hkL]
    exact hg

end GlobalTheory.ArcFrame
end
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts GlobalTheory.GoodTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constant_integral_arc_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (T : CDVR) (io : c.F →+* T.Fr) (b : V →+* T.V) (a : ArcIn Dw l V.subtype T.V b) (χ : Sp (PowerSeries T.V) ⟶ Y.X) (W : Wit Y a χ) (ev : PowerSeries T.V →+* T.V) (z : Sp T.Fr ⟶ Xo.XF c), PushInvertible Y.t.G Y.t.PP.L → (algebraMap T.V T.Fr).comp b = io.comp V.subtype → χ ≫ Y.s = spMap (PowerSeries.C (R := T.V)) ≫ spMap b → (∀ x, ev (PowerSeries.C x) = x) → z ≫ pullback.snd _ _ = spMap io → z ≫ Y.j = spMap ((algebraMap T.V T.Fr).comp ev) ≫ χ → letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, z ≫ pullback.fst _ _ = y.x → ∃ (ρ : (E →+* ℂ) → (𝓞 E →+* T.V)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR T.V)) (th : a.D₀.P.L.Sec) (y₀ : FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), ArcBasis W ρ e ∧ ThNZ th ∧ (∀ τ k, GtTanR (e τ k)) ∧ (∀ τ x, io (embK c τ x) = algebraMap T.V T.Fr (ρ τ x)) ∧ IsArcFr W e th ((algebraMap T.V T.Fr).comp ev) y₀ ∧ FrBor t y₀ y := by
  atlas_forward_decl GlobalTheory.ArcFrame.exists_arcFrame
end

section
section
open NumberField IsDedekindDomain Formalism.L2.Pj IsLocalRing

namespace GlobalTheory.GaussPoint

theorem C_dvd_iff {V : Type*} [CommRing V] (a : V) (f : PowerSeries V) :
    PowerSeries.C a ∣ f ↔ ∀ n, a ∣ PowerSeries.coeff n f := by
  constructor
  · rintro ⟨g, rfl⟩ n
    rw [PowerSeries.coeff_C_mul]
    exact dvd_mul_right _ _
  · intro h
    choose c hc using h
    refine ⟨PowerSeries.mk c, ?_⟩
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc]

theorem isPrime_span_C {V : Type*} [CommRing V] {a : V} (ha : Prime a) :
    (Ideal.span {(PowerSeries.C a : PowerSeries V)}).IsPrime := by
  have h1 : (Ideal.span {a}).IsPrime := (Ideal.span_singleton_prime ha.ne_zero).2 ha
  have h2 : Ideal.span {(PowerSeries.C a : PowerSeries V)} =
      RingHom.ker (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {a}))) := by
    ext f
    rw [Ideal.mem_span_singleton, C_dvd_iff, RingHom.mem_ker, PowerSeries.ext_iff]
    refine forall_congr' fun n => ?_
    rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rw [h2]
  exact RingHom.ker_isPrime _

section Val

variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
  [Algebra V K] [IsFractionRing V K]

theorem valV_irreducible {π : V} (hπ : Irreducible π) :
    valV V (algebraMap V K π) = WithZero.exp (-1 : ℤ) := by
  rw [valV, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton _ hπ.ne_zero hπ.maximalIdeal_eq

theorem valV_unit {u : V} (hu : IsUnit u) : valV V (algebraMap V K u) = 1 := by
  rw [valV, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  exact fun h => h hu

theorem vV_map_eq {V' K' : Type} [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V']
    [Field K'] [Algebra V' K'] [IsFractionRing V' K'] (f : V →+* V') (i : K →+* K')
    (hi : ∀ a, i (algebraMap V K a) = algebraMap V' K' (f a)) {π : V} (hπ : Irreducible π)
    (hπ' : Irreducible (f π)) (x : K) : vV V' (i x) = vV V x := by
  have key : ∀ a : V, valV V' (i (algebraMap V K a)) = valV V (algebraMap V K a) := by
    intro a
    by_cases ha : a = 0
    · simp [ha]
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    rw [hi]
    simp only [map_mul, map_pow]
    rw [valV_unit u.isUnit, valV_unit (u.isUnit.map f), valV_irreducible hπ, valV_irreducible hπ']
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := V) x
  simp only [vV, map_div₀, key]

end Val

theorem exists_gaussPoint (T : CDVR) (ϖ : T.V) (hϖ : Irreducible ϖ) :
    ∃ (T' : CDVR) (ev : PowerSeries T.V →+* T'.V) (i : T.Fr →+* T'.Fr), Function.Injective ev ∧
      IsUnit (ev PowerSeries.X) ∧ (∀ s, ev (PowerSeries.C ϖ) ∣ ev s → PowerSeries.C ϖ ∣ s) ∧
      (∀ a, i (algebraMap T.V T.Fr a) = algebraMap T'.V T'.Fr (ev (PowerSeries.C a))) ∧
      ∀ x, vV T'.V (i x) = vV T.V x := by
  let R := PowerSeries T.V
  let P : Ideal R := Ideal.span {(PowerSeries.C ϖ : PowerSeries T.V)}
  haveI hP : P.IsPrime := isPrime_span_C hϖ.prime
  let L := Localization.AtPrime P
  have hinj : Function.Injective (algebraMap R L) :=
    IsLocalization.injective L P.primeCompl_le_nonZeroDivisors
  have hm : maximalIdeal L = Ideal.span {algebraMap R L (PowerSeries.C ϖ)} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
  have hC0 : (PowerSeries.C ϖ : R) ≠ 0 := fun h =>
    hϖ.ne_zero (PowerSeries.C_injective (h.trans (map_zero _).symm))
  have hn : ¬ IsNilpotent (algebraMap R L (PowerSeries.C ϖ)) := by
    rw [IsNilpotent.map_iff hinj]
    exact fun h => hC0 h.eq_zero
  obtain ⟨_, hdvr, hirr⟩ := isDiscreteValuationRing_of_maximalIdeal_eq_span hm hn
  let S := AdicCompletion (maximalIdeal L) L
  let ev : R →+* S := (algebraMap L S).comp (algebraMap R L)
  have hev : Function.Injective ev :=
    (algebraMap_adicCompletion_injective_of_dvr L).comp hinj
  have hirr' : Irreducible (ev (PowerSeries.C ϖ)) :=
    irreducible_algebraMap_adicCompletion_of_dvr hirr
  have hunit : ∀ s : R, ¬ PowerSeries.C ϖ ∣ s → IsUnit (ev s) := fun s hs =>
    (IsLocalization.map_units L (⟨s, fun h => hs (Ideal.mem_span_singleton.1 h)⟩ :
      P.primeCompl)).map (algebraMap L S)
  haveI : CharZero S := charZero_of_injective_ringHom
    (f := ev.comp PowerSeries.C) (hev.comp PowerSeries.C_injective)
  let T' : CDVR := { V := S }
  let g : T.V →+* T'.Fr := (algebraMap T'.V T'.Fr).comp (ev.comp PowerSeries.C)
  have hg : Function.Injective g :=
    (IsFractionRing.injective T'.V T'.Fr).comp (hev.comp PowerSeries.C_injective)
  have hi : ∀ a, IsFractionRing.lift (K := T.Fr) hg (algebraMap T.V T.Fr a) =
      algebraMap T'.V T'.Fr (ev (PowerSeries.C a)) := fun a => IsFractionRing.lift_algebraMap hg a
  refine ⟨T', ev, IsFractionRing.lift hg, hev, hunit _ ?_, fun s hs => ?_, hi,
    vV_map_eq (ev.comp PowerSeries.C) _ hi hϖ hirr'⟩
  · rw [C_dvd_iff]
    intro h
    have h1 := h 1
    rw [PowerSeries.coeff_one_X] at h1
    exact hϖ.not_isUnit (isUnit_of_dvd_one h1)
  · by_contra h
    exact hirr'.not_isUnit (isUnit_of_dvd_unit hs (hunit s h))

end GlobalTheory.GaussPoint
end

open NumberField IsDedekindDomain Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gaussPoint' : ∀ (T : CDVR) (ϖ : T.V), Irreducible ϖ → ∃ (T' : CDVR) (ev : PowerSeries T.V →+* T'.V) (i : T.Fr →+* T'.Fr), Function.Injective ev ∧ IsUnit (ev PowerSeries.X) ∧ (∀ s, ev (PowerSeries.C ϖ) ∣ ev s → PowerSeries.C ϖ ∣ s) ∧ (∀ a, i (algebraMap T.V T.Fr a) = algebraMap T'.V T'.Fr (ev (PowerSeries.C a))) ∧ ∀ x, vV T'.V (i x) = vV T.V x := by
  atlas_forward_decl GlobalTheory.GaussPoint.exists_gaussPoint
end

section
open NumberField IsDedekindDomain Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complex_embedding_fractionField_cdvr : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (T : CDVR), T.FinRes → ∀ io : K →+* T.Fr, ∃ ι : T.Fr →+* ℂ, ι.comp io = σ := by
  first | exact @GlobalTheory.ComplexEmbedding.exists_embedding_fractionField | exact GlobalTheory.ComplexEmbedding.exists_embedding_fractionField | (intros; apply GlobalTheory.ComplexEmbedding.exists_embedding_fractionField <;> assumption)
end

section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurent_coeff_neg_eq_zero_of_bounded' : ∀ (F : ℂ⸨X⸩) (T C : ℝ), (∀ w : ℂ, T < w.im → ∃ x : ℂ, HasSum (fun m : ℤ => F.coeff m * eTwoPi w ^ m) x ∧ ‖x‖ ≤ C) → ∀ m : ℤ, m < 0 → F.coeff m = 0 := by
  first | exact @GlobalTheory.laurent_coeff_neg_eq_zero_of_bounded | exact GlobalTheory.laurent_coeff_neg_eq_zero_of_bounded | (intros; apply GlobalTheory.laurent_coeff_neg_eq_zero_of_bounded <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTransfer

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg GlobalTheory.GoodPts
open scoped LaurentSeries

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem inV_iff (T : CDVR) (x : T.Fr) : InV T x ↔ 0 ≤ vV T.V x := by
  by_cases h0 : x = 0
  · subst h0; simp [InV, vV]
  have hne := valV_ne_zero (V := T.V) h0
  constructor
  · rintro ⟨a, rfl⟩
    have h1 : valV T.V (algebraMap T.V T.Fr a) ≤ 1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a
    have h2 := (WithZero.log_le_log hne one_ne_zero).2 h1
    rw [WithZero.log_one] at h2
    unfold vV; omega
  · intro h
    have h4 : valV T.V x ≤ 1 := by
      refine (WithZero.log_le_log hne one_ne_zero).1 ?_
      rw [WithZero.log_one]
      unfold vV at h
      omega
    exact IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) h4

theorem inV_of_overLa {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {T : CDVR} {io : K →+* T.Fr}
    {e : ℕ} (ho : OverLa la T.V io e) (a : (la.valuation K).valuationSubring) : InV T (io a) := by
  rw [inV_iff, ho.2]
  refine mul_nonneg (Nat.cast_nonneg e) ?_
  by_cases h0 : (a : K) = 0
  · simp [h0, vLa]
  have hne : la.valuation K (a : K) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have h2 := (WithZero.log_le_log hne one_ne_zero).2 a.2
  rw [WithZero.log_one] at h2
  unfold vLa; omega

theorem exists_factor {A : Type} [CommRing A] (T : CDVR) (f : A →+* T.Fr) (h : ∀ a, InV T (f a)) :
    ∃ b : A →+* T.V, (algebraMap T.V T.Fr).comp b = f := by
  let j := RingEquiv.ofBijective (algebraMap T.V T.Fr).rangeRestrict
    ⟨fun a b hab => IsFractionRing.injective T.V T.Fr (congrArg Subtype.val hab),
      RingHom.rangeRestrict_surjective _⟩
  exact ⟨j.symm.toRingHom.comp (f.codRestrict _ h),
    RingHom.ext fun a => congrArg Subtype.val (j.apply_symm_apply ⟨_, h a⟩)⟩

theorem good_of_extIn {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {T : CDVR} {io : c.F →+* T.Fr}
    (y : IntFr Xo c T io) (h : letI := io.toAlgebra; ExtIn Y (abLocus Y.t.G) T io y.1.x) : Good y := by
  let _ := io.toAlgebra
  obtain ⟨y', z, h1, -, h3, h4⟩ := h
  obtain ⟨t, ⟨m⟩⟩ := (GlobalTheory.ModelPoints.model_points_charts E H Dw l Xo c O β Y).2.1 _ y'
  obtain ⟨t', m₁, -, m₂, -⟩ := GlobalTheory.TraitDataIntrinsic.exists_generic Y m h3
  have hab : abLocus t.G = Set.univ := Set.eq_univ_of_forall fun p =>
    (abLocus_pullback abLocusOne Y.t.semi m.cart.1 p).1 (h4 ⟨_, rfl⟩)
  have hp := GlobalTheory.T.isProper_semiAbelian_triple_of_abelianLocus_eq_univ E H Dw l Xo T _ t t' m₂ m₁ hab
  exact ⟨t, t', h1 ▸ m₂, m₁, hp⟩

theorem inV_of_frBor {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) {T : CDVR}
    {io : c.F →+* T.Fr} (y y' : IntFr Xo c T io) (t : Ix Dw → T.Frˣ)
    (h : letI := io.toAlgebra; FrBor t y.1 y'.1) : InV T (evI y f) ↔ InV T (evI y' f) := by
  obtain ⟨hE, hU, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have h1 := unitIndep_of hE.wt hU a n f hf T io y y' t h 1
  have key : ∀ x : T.Fr, InV T x ↔ 0 ≤ nval T.V 1 x := fun x => by
    by_cases h0 : x = 0
    · subst h0; simp [nval_zero, InV]
    · rw [nval_of_ne h0, inV_iff, EReal.coe_nonneg]; simp
  rw [key, key, h1]

theorem inV_of_extIn (la : HeightOneSpectrum (𝓞 c.F)) (Y : Model Xo c (la.valuation c.F).valuationSubring.subtype)
    (hP : PushInvertible Y.t.G Y.t.PP.L) (hop : IsOpen (abLocus Y.t.G)) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
    (hf : f ∈ sec Xo c a n) (hb : BddGood Xo c la 1 f) {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e)
    (y : IntFr Xo c T io) (h : letI := io.toAlgebra; ExtIn Y (abLocus Y.t.G) T io y.1.x) : InV T (evI y f) := by
  let _ := io.toAlgebra
  obtain ⟨hE, hU, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hev := GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hE a n f hf
  obtain ⟨J, _, P, hC⟩ := GlobalTheory.Reg.exists_finite_pchart_cover GlobalTheory.abelianSchemeLaws_all.2.secTwist E H Dw l Xo c hE.bc
    (la.valuation c.F).valuationSubring Y hP
  let W : ValuationSubring T.Fr := (valV T.V).valuationSubring
  have hW : ∀ x, x ∈ W ↔ InV T x := fun x =>
    ⟨fun h => IsDiscreteValuationRing.exists_lift_of_le_one (A := T.V) (K := T.Fr) h,
      by rintro ⟨a, rfl⟩; exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a⟩
  obtain ⟨j, e₀, he₀, ψ, z, t, hg, hz, ht⟩ := hC T.Fr W (fun a => (hW _).2 (inV_of_overLa ho a)) y.1
  obtain ⟨P', e', he', ψ', hg', hz', hall⟩ := GlobalTheory.T.exists_refined_flagChart_integral_points_in_open E H Dw l Xo c (la.valuation c.F).valuationSubring Y
    (abLocus Y.t.G) (P j) T io hop e₀ he₀ ψ z (fun g hgg => (hW _).1 (hg g hgg)) hz (ht.1 ▸ h)
  have hzI : Integral T io z := P'.int e' he' T io ψ' (inV_of_overLa ho) hg' z hz'
  rw [inV_of_frBor hf y ⟨z, hE.test _ z, hzI⟩ t ht]
  show InV T (evR Xo c f z)
  rw [(hev _).1 _ ψ' _ _ hz']
  refine GlobalTheory.T.integral_of_integral_at_algebraic_points_smooth c.F P'.Ω la P'.gens e' P'.frac (P'.es_mem e' he').1 (P'.es_mem e' he').2 (P'.sm e' he')
    (evR Xo c f (P'.y e' he')) (fun T₁ io₁ n₁ ho₁ hfin ψ₁ hk hg₁ => ?_) T io e ho ψ'.toRingHom ψ'.commutes hg'
  let _ := io₁.toAlgebra
  let φ : P'.R e' →ₐ[c.F] T₁.Fr := ⟨ψ₁, hk⟩
  obtain ⟨z₁, hz₁⟩ := hE.bc _ _ φ (P'.y e' he')
  let y₁ : IntFr Xo c T₁ io₁ := ⟨z₁, hE.test _ z₁, P'.int e' he' T₁ io₁ φ (inV_of_overLa ho₁) hg₁ z₁ hz₁⟩
  have h1 := hb T₁ io₁ n₁ ho₁ y₁ hfin (good_of_extIn Y y₁ (hall T₁ io₁ (inV_of_overLa ho₁) φ z₁ hg₁ hz₁))
  rw [map_one, one_mul] at h1
  have h2 : evI y₁ f = φ (evR Xo c f (P'.y e' he')) := (hev _).1 _ φ _ _ hz₁
  rw [h2] at h1
  exact h1

theorem exists_model (hr : 1 ≤ Dw.p + Dw.q) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ)
    (hp : p.Prime) (hpl : (p : 𝓞 c.F) ∈ la.asIdeal) (hg : l.GoodAt p) :
    ∃ Y : Model Xo c (la.valuation c.F).valuationSubring.subtype, PushInvertible Y.t.G Y.t.PP.L ∧
      IsOpen (abLocus Y.t.G) ∧ Y.SplitFibres ∧ Y.N3 ∧ Y.N4 := by
  classical
  obtain ⟨hP, hN⟩ := GlobalTheory.Moduli.jointExistence_and_moduliScheme
  let Xf : ∀ l' : Level H, Moduli Dw l' := fun l' =>
    if h : l' = l then h ▸ Xo else Classical.choice (hN E H Dw l' hr)
  have hX : Xf l = Xo := by simp [Xf]
  obtain ⟨Y, hY, -⟩ := hP.2 E H Dw hr Xf
  obtain ⟨W, hWe, hWn⟩ := exists_valuationSubring_comap_eq_nonunits c.F.val.toRingHom
    (la.valuation c.F).valuationSubring
  have hpU : (p : c.F) ∈ (la.valuation c.F).valuationSubring.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff,
      ← (Valuation.isEquiv_valuation_valuationSubring (la.valuation c.F)).lt_one_iff_lt_one]
    have := (la.valuation_lt_one_iff_mem (K := c.F) (p : 𝓞 c.F)).2 hpl
    simpa using this
  have hW : (p : ℂ) ∈ W.nonunits := by simpa using hWn _ hpU
  have h := (hY p W hp hW).1.1 ⟨l, c, hg⟩
  obtain ⟨U, hU, -⟩ := h.2.2.2.1
  have h' : ∃ Y : Model (Xf l) c (c.V W).subtype, PushInvertible Y.t.G Y.t.PP.L ∧
      IsOpen (abLocus Y.t.G) ∧ Y.SplitFibres ∧ Y.N3 ∧ Y.N4 :=
    ⟨_, h.2.2.1, hU ▸ U.isOpen, (hY p W hp hW).2 ⟨l, c, hg⟩⟩
  have he : c.V W = (la.valuation c.F).valuationSubring := hWe
  rw [he, hX] at h'
  exact h'

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := (Spec.map_comp _ _).symm

theorem mem_of_pow_mem {F : Type} [Field F] (V : ValuationSubring F) {x : F} {n : ℕ} (hn : n ≠ 0) (h : x ^ n ∈ V) :
    x ∈ V := by
  rw [← ValuationSubring.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff hn).1 h

theorem exists_values (c : Coeff l) (V : ValuationSubring c.F) :
    ∃ r z : V, ((V.subtype r : c.F) : ℂ) = H.rt0 ∧ ((V.subtype z : c.F) : ℂ) = zeta l.A := by
  let inc := (IntermediateField.inclusion c.le).toRingHom
  refine ⟨⟨inc (baseKA l).ρ, mem_of_pow_mem V two_ne_zero ?_⟩,
    ⟨inc (baseKA l).ζ, mem_of_pow_mem V l.A_pos.ne' ?_⟩, rfl, rfl⟩
  · rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
    exact neg_mem (natCast_mem V _)
  · rw [← map_pow, (baseKA l).ζ_prim.pow_eq_one, map_one]
    exact one_mem V

theorem coeff_neg_eq_zero {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r)
    (hU : ∀ σ', Formalism.L2.PjFree.GoodEmb c σ' → Formalism.L2.PjFree.IsUnf (U σ')) (σ : c.F →+* ℂ)
    (hσ : Formalism.L2.PjFree.GoodEmb c σ) {V : ValuationSubring c.F} (Y : Model Xo c V.subtype)
    (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ)
    (hP : PushInvertible Y.t.G Y.t.PP.L)
    (hover : χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype))
    (hgen : ∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j)
    (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (hth : ThNZ th)
    (htan : ∀ τ k, GtTanR (e τ k)) [Algebra c.F ℂ⸨X⸩]
    (halg : ∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x)))
    (y : FrPt Xo c ℂ⸨X⸩) (hy : IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y)
    {a' : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hd : Dom a' n) (hf : f ∈ Formalism.L2.PjFree.cusp Xo c U a' n) :
    ∀ m : ℤ, m < 0 → (evR Xo c f y).coeff m = 0 := by
  let _ : Algebra (FractionRing ℂ) ℂ := FractionRing.liftAlgebra ℂ ℂ
  have : IsScalarTower ℂ (FractionRing ℂ) ℂ := FractionRing.isScalarTower_liftAlgebra ℂ ℂ
  obtain ⟨h1, h2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨hE, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hY : Mono Y.j := GlobalTheory.ThetaShiftProofs.mono_j Y (mono_spMap_subtype _)
  obtain ⟨Uw⟩ := nonempty_unfWit_of_isUnf E H Dw l Xo c σ r (U σ) (hU σ hσ)
  have hty := (GlobalTheory.Relab.relab_good E H l c _ hσ).2.2.2 Dw Uw.g Uw.e
  obtain ⟨Ha⟩ := GlobalTheory.arcClause_closed E H Dw l Xo c _ _ Y σ a χ W Uw.g _ Uw.F hσ hty (exists_values c V) hover hgen
  obtain ⟨Θ⟩ := GlobalTheory.ArcTheta.nonempty_thetaDat h1 h2 E H Dw l Xo c σ _ _ Y a χ W _ _ Uw.F Ha hty th hth
  obtain ⟨v₁, -⟩ := GlobalTheory.ExpTan.anVec_bijective h1.globalFns E H Dw l Xo c σ _ _ Y a χ W _ _ Uw.F Ha
  choose z hz using fun τ i => (v₁ (e τ i) (htan τ i)).exists
  have hzt := GlobalTheory.ArcType.main h1 h2 E H Dw l Xo c σ r (U σ) Uw _ _ Y a χ W Ha y e th z hσ halg hY hy hz
  obtain ⟨T₁, hT₁⟩ := GlobalTheory.ArcQ.hasSum_evR_arc h1 h2 E H Dw l Xo c σ _ _ Y a χ W _ _ Uw.F Ha y e th Θ z hE halg hover
    (mono_spMap_subtype _) hP hth hy hz
  obtain ⟨T₂, C, hT₂⟩ := GlobalTheory.T.cuspForm_values_bounded_on_holomorphicArc E H Dw l Xo c r U σ Uw _ _ Y a χ W Ha th Θ z hU hσ hzt a' n f hd hf
  refine GlobalTheory.T.laurent_coeff_neg_eq_zero_of_bounded' _ (max Ha.T (max T₁ T₂)) C fun w hw => ?_
  obtain ⟨yw, hyw, -⟩ := GlobalTheory.ArcQ.AnFrEx.existsUnique_anFr h1 h2 E H Dw l Xo c σ r (U σ) Uw _ _ Y a χ W Ha th Θ z hσ hzt
    w ((le_max_left _ _).trans_lt hw)
  exact ⟨_, hT₁ w (((le_max_left _ _).trans (le_max_right _ _)).trans_lt hw) yw hyw a' n f hf.1,
    hT₂ w (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hw) yw hyw⟩

theorem exists_lift {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {S : Type} [CommRing S]
    (w : Sp S ⟶ Y.X) (k : c.F →+* S) (hw : w ≫ Y.s = spMap (k.comp β)) (hr : Set.range w ⊆ abLocus Y.t.G) :
    ∃ z : Sp S ⟶ Xo.XF c, z ≫ Y.j = w ∧ z ≫ pullback.snd _ _ = spMap k := by
  let u : Sp S ⟶ pullback Y.s (spMap β) := pullback.lift w (spMap k) (hw.trans (sp_comp _ _).symm)
  have := Y.jQ_open
  have hu : Set.range u ⊆ Set.range Y.jQ := by
    rw [← Y.ab_gen]
    rintro _ ⟨x, rfl⟩
    refine hr ⟨x, ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  refine ⟨IsOpenImmersion.lift Y.jQ u hu, ?_, ?_⟩
  · rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
  · rw [← Y.jQ_over, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_snd]

theorem snd_eq {V : ValuationSubring c.F} (Y : Model Xo c V.subtype) {S : Type} [CommRing S] (z : Sp S ⟶ Xo.XF c)
    (k : c.F →+* S) (h : z ≫ Y.j ≫ Y.s = spMap (k.comp V.subtype)) : z ≫ pullback.snd _ _ = spMap k := by
  have := mono_spMap_subtype V
  rw [← cancel_mono (spMap V.subtype), Category.assoc, ← GlobalTheory.TraitDataIntrinsic.j_s Y, h, sp_comp]

theorem flat_of_injective (T : CDVR) {S : Type} [CommRing S] [IsDomain S] (g : T.V →+* S) (hg : Function.Injective g) :
    g.Flat := by
  let _ := g.toAlgebra
  have : FaithfulSMul T.V S := (faithfulSMul_iff_algebraMap_injective T.V S).2 hg
  show Module.Flat T.V S
  infer_instance

theorem exists_value {V : ValuationSubring c.F} (Y : Model Xo c V.subtype) (T : CDVR) (io : c.F →+* T.Fr)
    (b : V →+* T.V) (a : ArcIn Dw l V.subtype T.V b) (χ : Sp (PowerSeries T.V) ⟶ Y.X) (W : Wit Y a χ) (ϖ : T.V)
    (hϖ : Irreducible ϖ) (hP : PushInvertible Y.t.G Y.t.PP.L) (hb : (algebraMap T.V T.Fr).comp b = io.comp V.subtype)
    (hover : χ ≫ Y.s = spMap (PowerSeries.C (R := T.V)) ≫ spMap b)
    (hab : ∀ x : Sp (PowerSeries T.V), χ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal)
    (ρ : (E →+* ℂ) → (𝓞 E →+* T.V)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR T.V))
    (th : a.D₀.P.L.Sec) (he : ArcBasis W ρ e) (hth : ThNZ th)
    (hρ : ∀ τ x, io (embK c τ x) = algebraMap T.V T.Fr (ρ τ x))
    {a' : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a' n) :
    ∃ (h : PowerSeries T.V) (N : ℕ), ∀ (L : Type) [CommRing L] [Algebra c.F L] (ω : PowerSeries T.V →+* L)
      (j : T.Fr →+* L), IsUnit (ω (PowerSeries.C ϖ * PowerSeries.X)) →
      (∀ x, j (algebraMap T.V T.Fr x) = ω (PowerSeries.C x)) → (∀ x, algebraMap c.F L x = j (io x)) →
      ∃ y : FrPt Xo c L, IsArcFr W e th ω y ∧ evR Xo c f y * ω ((PowerSeries.C ϖ * PowerSeries.X) ^ N) = ω h := by
  obtain ⟨h1, h2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨hE, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hY : Mono Y.j := GlobalTheory.ThetaShiftProofs.mono_j Y (mono_spMap_subtype _)
  let d : PowerSeries T.V := PowerSeries.C ϖ * PowerSeries.X
  have hd : d ≠ 0 := mul_ne_zero (fun h => hϖ.ne_zero (PowerSeries.C_injective (h.trans (map_zero _).symm)))
    PowerSeries.X_ne_zero
  have hle : Submonoid.powers d ≤ nonZeroDivisors _ := powers_le_nonZeroDivisors_of_noZeroDivisors hd
  let S := Localization.Away d
  have : IsDomain S := IsLocalization.isDomain_localization hle
  let ι : PowerSeries T.V →+* S := algebraMap _ _
  have hι : Function.Injective ι := IsLocalization.injective S hle
  have hud : IsUnit (ι d) := IsLocalization.Away.algebraMap_isUnit d
  have huϖ : IsUnit (ι (PowerSeries.C ϖ)) := by
    rw [map_mul] at hud; exact isUnit_of_mul_isUnit_left hud
  have huX : IsUnit (ι PowerSeries.X) := by
    rw [map_mul] at hud; exact isUnit_of_mul_isUnit_right hud
  have hun : ∀ x : nonZeroDivisors T.V, IsUnit ((ι.comp (PowerSeries.C (R := T.V))) x) := fun x => by
    obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero x.2) hϖ
    rw [hu, map_mul, map_pow]
    exact (u.isUnit.map _).mul (huϖ.pow m)
  let k : T.Fr →+* S := IsLocalization.lift hun
  have hk : ∀ x, k (algebraMap T.V T.Fr x) = ι (PowerSeries.C x) := IsLocalization.lift_eq hun
  let _ : Algebra c.F S := (k.comp io).toAlgebra
  obtain ⟨z, hz, hz'⟩ := exists_lift Y (spMap ι ≫ χ) (k.comp io) (by
      rw [Category.assoc, hover, sp_comp, sp_comp, RingHom.comp_assoc, ← hb]
      exact congrArg spMap (RingHom.ext fun x => (hk _).symm)) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Hom.comp_apply, hab]
      exact fun hx => x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (show ι PowerSeries.X ∈ x.asIdeal from hx) huX))
  have hflat : (ι.comp (PowerSeries.C (R := T.V))).Flat := flat_of_injective T _ (hι.comp PowerSeries.C_injective)
  obtain ⟨yS, -, hyS⟩ := GlobalTheory.ArcQ.exists_isArcFr h1 h2 E H Dw l Xo c _ _ Y T.V b a χ W ρ e th he hth (Or.inr hP) S ι z
    hflat hz (by rw [pullback.condition, ← Category.assoc, hz', sp_comp]; rfl)
    (fun τ x => (congrArg k (hρ τ x)).trans (hk _))
  obtain ⟨⟨h, s, N, rfl⟩, hs⟩ := IsLocalization.surj (Submonoid.powers d) (evR Xo c f yS)
  refine ⟨h, N, fun L _ _ ω j hω hj hc => ?_⟩
  let φ₀ : S →+* L := IsLocalization.Away.lift d hω
  have hφ₀ : ∀ s, φ₀ (ι s) = ω s := IsLocalization.Away.lift_eq d hω
  have hkj : φ₀.comp k = j := IsLocalization.ringHom_ext (nonZeroDivisors T.V)
    (RingHom.ext fun x => ((congrArg φ₀ (hk x)).trans (hφ₀ _)).trans (hj x).symm)
  let φ : S →ₐ[c.F] L := ⟨φ₀, fun x => (RingHom.congr_fun hkj (io x)).trans (hc x).symm⟩
  obtain ⟨y, hy⟩ := hE.bc _ _ φ yS
  have h₀ := (GlobalTheory.ArcQ.isArcFr_unique_baseChange h1 h2 E H Dw l Xo c _ _ Y T.V b a χ W e th hth S ι yS hyS).2 hY
    L φ y hy
  have e₀ : φ.toRingHom.comp ι = ω := RingHom.ext hφ₀
  rw [e₀] at h₀
  refine ⟨y, h₀, ?_⟩
  rw [(GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hE a' n f hf S).1 L φ yS y hy, ← hφ₀, ← hφ₀]
  exact (map_mul φ₀ _ _).symm.trans (congrArg φ₀ hs)

theorem pow_dvd_of_map {R S : Type} [CommRing R] [CommRing S] [IsDomain S] (ev : R →+* S) {p : R} (hp : ev p ≠ 0)
    (h : ∀ s, ev p ∣ ev s → p ∣ s) : ∀ (N : ℕ) (s : R), ev p ^ N ∣ ev s → p ^ N ∣ s := by
  intro N
  induction N with
  | zero => intro s _; simp
  | succ N ih =>
    intro s hs
    obtain ⟨s', rfl⟩ := h s ((dvd_pow_self _ N.succ_ne_zero).trans hs)
    rw [map_mul, pow_succ', mul_dvd_mul_iff_left hp] at hs
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih s' hs)

theorem X_pow_dvd {A : Type} [CommRing A] (κ : A →+* ℂ) (hκ : Function.Injective κ) (F : ℂ⸨X⸩)
    (hF : ∀ m : ℤ, m < 0 → F.coeff m = 0) (a : A) (h : PowerSeries A) (N : ℕ)
    (e : F * HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map κ ((PowerSeries.C a * PowerSeries.X) ^ N)) =
      HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map κ h)) : PowerSeries.X ^ N ∣ h := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  apply hκ
  have e1 : HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.map κ ((PowerSeries.C a * PowerSeries.X) ^ N)) =
      HahnSeries.single (N : ℤ) (κ a ^ N) := by
    rw [map_pow, map_mul, PowerSeries.map_C, PowerSeries.map_X, map_pow, map_mul, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_X, HahnSeries.C_apply, HahnSeries.single_mul_single, HahnSeries.single_pow]
    simp
  have e2 := congrArg (fun G : ℂ⸨X⸩ => G.coeff (((m : ℤ) - N) + N)) e
  simp only [e1, HahnSeries.coeff_mul_single_add] at e2
  rw [hF _ (by omega), zero_mul, sub_add_cancel, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map] at e2
  rw [← e2, map_zero]

theorem inV_of_arc {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (la : HeightOneSpectrum (𝓞 c.F)) (Y : Model Xo c (la.valuation c.F).valuationSubring.subtype)
    (hP : PushInvertible Y.t.G Y.t.PP.L) (hop : IsOpen (abLocus Y.t.G)) (h4 : Y.N4)
    {a' : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hd : Dom a' n) (hf : f ∈ cusp Xo c U a' n)
    (hbd : BddGood Xo c la 1 f) {T : CDVR} {io : c.F →+* T.Fr} {m : ℕ} (ho : OverLa la T.V io m) (hfin : T.FinRes)
    (b : (la.valuation c.F).valuationSubring →+* T.V)
    (hb : (algebraMap T.V T.Fr).comp b = io.comp (la.valuation c.F).valuationSubring.subtype)
    (ϖ : T.V) (hϖ : Irreducible ϖ) (a : ArcIn Dw l (la.valuation c.F).valuationSubring.subtype T.V b)
    (y' : Sp T.V ⟶ Y.X) (hy' : y' ≫ Y.s = spMap b)
    (hA : Y.HasArcData a (Ideal.span {ϖ}) (RingHom.id T.V) ϖ y') (y : IntFr Xo c T io) (z : Sp T.Fr ⟶ Xo.XF c)
    (hz₁ : letI := io.toAlgebra; z ≫ pullback.fst _ _ = y.1.x) (hz₂ : z ≫ pullback.snd _ _ = spMap io)
    (hz₃ : z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ y') : InV T (evI y f) := by
  let _ := io.toAlgebra
  obtain ⟨h1, h2, -, hL4, hL5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨hE, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hY : Mono Y.j := GlobalTheory.ThetaShiftProofs.mono_j Y (mono_spMap_subtype _)
  have hcpl : IsAdicComplete (Ideal.span {ϖ}) T.V := hϖ.maximalIdeal_eq ▸ T.cpl
  obtain ⟨χ, hχ, hsp⟩ := h4 T.V b ϖ a (Or.inr ⟨inferInstance, hϖ, hcpl⟩)
  obtain ⟨hover, hab, hopen, hW⟩ := (hχ χ).1 rfl
  obtain ⟨W⟩ := (Y.hasArcData_iff a _ _ _ χ).1 hW
  obtain ⟨-, -, ev, hevC, hevX, -⟩ := GlobalTheory.UniformiserEval.dvr_admissibleBase_and_powerSeries_evalUniformiser T.V ϖ hϖ T.cpl
  have hχy : spMap ev ≫ χ = y' := hsp hϖ y' ev hy' (by
    rintro _ ⟨x, rfl⟩
    exact ⟨z x, by rw [← Scheme.Hom.comp_apply, hz₃]⟩) hA hevC hevX
  obtain ⟨ρ, e, th, y₀, t, he, hth, htan, hρ, hy₀, ht⟩ := GlobalTheory.T.exists_constant_integral_arc_frames E H Dw l Xo c _ Y T io b a χ W ev z hP hb hover
    hevC hz₂ (by rw [hz₃, ← hχy, ← Category.assoc, sp_comp]) y.1 hz₁
  obtain ⟨h, N, hval⟩ := exists_value Y T io b a χ W ϖ hϖ hP hb hover hab ρ e th he hth hρ hf.1

  have hX : PowerSeries.X ^ N ∣ h := by
    obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_complex_embedding_fractionField_cdvr c.F c.F.val.toRingHom T hfin io
    let κ₀ : T.V →+* ℂ := κ.comp (algebraMap T.V T.Fr)
    have hκ₀ : Function.Injective κ₀ := κ.injective.comp (IsFractionRing.injective T.V T.Fr)
    have hb' : c.F.val.toRingHom.comp (la.valuation c.F).valuationSubring.subtype = κ₀.comp b := by
      rw [RingHom.comp_assoc, hb, ← RingHom.comp_assoc, hκ]
    obtain ⟨⟨a₁, p, hp⟩, hbc⟩ := GlobalTheory.ArcQBC.baseChanges h1 h2 hL4.unifBaseChange hL5 E H Dw l Xo c _ _ Y T.V ℂ b a κ₀
      hκ₀ _ hb'
    obtain ⟨hW₁, hlet, htn, hthx, hnz⟩ := hbc a₁ p hp
    obtain ⟨W₁, hW₁⟩ := hW₁ χ W
    choose e₁ he₁ using fun τ k => (hlet (e τ k)).exists
    obtain ⟨th₁, hth₁⟩ := (hthx th).exists
    let cL : ℂ →+* ℂ⸨X⸩ := (HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.C (R := ℂ))
    let _ : Algebra c.F ℂ⸨X⸩ := (cL.comp c.F.val.toRingHom).toAlgebra
    have hϖ0 : κ₀ ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hκ₀ (h0.trans (map_zero _).symm))
    obtain ⟨yC, hyC, hv⟩ := hval ℂ⸨X⸩ ((HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.map κ₀)) (cL.comp κ) (by
        rw [isUnit_iff_ne_zero, RingHom.comp_apply, map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective, map_mul,
          PowerSeries.map_C, PowerSeries.map_X]
        exact mul_ne_zero (fun h => hϖ0 (PowerSeries.C_injective (h.trans (map_zero _).symm))) PowerSeries.X_ne_zero)
      (fun x => by simp [cL, κ₀]) (fun x => congrArg cL (RingHom.congr_fun hκ x).symm)
    have hyC₁ := GlobalTheory.ArcQ.isArcFr_witBC h1 h2 E H Dw l Xo c _ _ Y T.V b a χ W ℂ _ a₁ κ₀ p W₁ hY hp hW₁ e e₁ th th₁ he₁
      hth₁ _ _ yC hyC
    refine X_pow_dvd κ₀ hκ₀ _ (coeff_neg_eq_zero (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) hU c.F.val.toRingHom rfl Y a₁ _
      W₁ hP ?_ (fun x hx => ?_) e₁ th₁ (hnz _ _ hth₁ hth) (fun τ k => htn _ _ (he₁ τ k) (htan τ k)) (fun _ => rfl) yC
      hyC₁ hd hf) ϖ h N hv
    · rw [Category.assoc, hover, sp_comp, sp_comp, sp_comp, hb']
      exact congrArg spMap (RingHom.ext fun x => PowerSeries.map_C κ₀ (b x))
    · rw [Scheme.Hom.comp_apply]
      refine hopen _ fun hm => ?_
      have hm' : PowerSeries.map κ₀ (PowerSeries.C ϖ * PowerSeries.X) ∈ x.asIdeal := hm
      rw [map_mul, PowerSeries.map_C, PowerSeries.map_X] at hm'
      exact hx ((Ideal.unit_mul_mem_iff_mem _ ((IsUnit.mk0 _ hϖ0).map _)).1 hm')
  obtain ⟨h₁, rfl⟩ := hX

  have hG : PowerSeries.C ϖ ^ N ∣ h₁ := by
    obtain ⟨T', ω, i, hω, hωX, hωd, hi, hv'⟩ := GlobalTheory.T.exists_gaussPoint' T ϖ hϖ
    have hinj := IsFractionRing.injective T'.V T'.Fr
    have hω0 : ω (PowerSeries.C ϖ) ≠ 0 := fun h0 =>
      hϖ.ne_zero (PowerSeries.C_injective ((hω (h0.trans (map_zero _).symm)).trans (map_zero _).symm))
    let _ := (i.comp io).toAlgebra
    obtain ⟨yG, hyG, hv⟩ := hval T'.Fr ((algebraMap T'.V T'.Fr).comp ω) i (by
        rw [isUnit_iff_ne_zero, RingHom.comp_apply, map_ne_zero_iff _ hinj, map_mul]
        exact mul_ne_zero hω0 hωX.ne_zero) hi (fun _ => rfl)
    have hint := GlobalTheory.ArcQ.integral_of_isArcFr h1 h2 E H Dw l Xo c _ _ Y T.V b a χ W ρ e th he hth hP T' (i.comp io) ω
      (hω.comp PowerSeries.C_injective) (fun τ x => (congrArg i (hρ τ x)).trans (hi _)) yG hyG
    obtain ⟨zG, -, -, -, -, k₁, k₂, -⟩ := id hyG
    have ho' : OverLa la T'.V (i.comp io) (1 * m) := ho.bc i one_pos fun x => by rw [hv', Nat.cast_one, one_mul]
    obtain ⟨x, hx⟩ := inV_of_extIn la Y hP hop hf.1 hbd ho' ⟨yG, hE.test _ yG, hint⟩
      ⟨spMap ω ≫ χ, zG, k₂, snd_eq Y zG _ (by
        rw [← Category.assoc, k₁, Category.assoc, hover, sp_comp, sp_comp, RingHom.comp_assoc _ io, ← hb]
        exact congrArg spMap (RingHom.ext fun x => (hi _).symm)),
       by rw [k₁, ← Category.assoc, sp_comp], by
        rintro _ ⟨x, rfl⟩
        rw [Scheme.Hom.comp_apply, hab]
        exact fun hx => x.isPrime.ne_top
          (Ideal.eq_top_of_isUnit_mem _ (show ω PowerSeries.X ∈ x.asIdeal from hx) hωX)⟩
    have hx' : algebraMap T'.V T'.Fr x = evR Xo c f yG := hx
    rw [← hx', RingHom.comp_apply, RingHom.comp_apply, ← map_mul] at hv
    have hv₁ := hinj hv
    refine pow_dvd_of_map ω hω0 hωd N h₁ ⟨x, mul_left_cancel₀ (pow_ne_zero N hωX.ne_zero) ?_⟩
    simp only [map_mul, map_pow, mul_pow] at hv₁
    rw [← hv₁]; ring
  obtain ⟨h₂, rfl⟩ := hG

  have hinj := IsFractionRing.injective T.V T.Fr
  have hne : (algebraMap T.V T.Fr).comp ev (PowerSeries.C ϖ * PowerSeries.X) ≠ 0 := by
    rw [RingHom.comp_apply, map_ne_zero_iff _ hinj, map_mul, hevC, hevX]
    exact mul_ne_zero hϖ.ne_zero hϖ.ne_zero
  obtain ⟨y₁, hy₁, hv⟩ := hval T.Fr ((algebraMap T.V T.Fr).comp ev) (RingHom.id _) (isUnit_iff_ne_zero.2 hne)
    (fun x => by rw [RingHom.comp_apply, hevC]; rfl) (fun _ => rfl)
  obtain rfl : y₁ = y₀ := (GlobalTheory.ArcQ.isArcFr_unique_baseChange h1 h2 E H Dw l Xo c _ _ Y T.V b a χ W e th hth _ _ y₀
    hy₀).1 hY y₁ hy₁
  have hint := GlobalTheory.ArcQ.integral_of_isArcFr h1 h2 E H Dw l Xo c _ _ Y T.V b a χ W ρ e th he hth hP T io ev
    (fun x x' hx => (hevC x).symm.trans (hx.trans (hevC x'))) (fun τ x => by rw [hevC]; exact hρ τ x) y₁ hy₁
  rw [← inV_of_frBor hf.1 ⟨y₁, hE.test _ y₁, hint⟩ y t ht]
  refine ⟨ev h₂, mul_right_cancel₀ (pow_ne_zero N hne) ?_⟩
  rw [← map_pow]
  refine Eq.trans ?_ hv.symm
  simp only [RingHom.comp_apply, map_mul, map_pow, mul_pow]
  ring

theorem bddAll_one {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ))
    (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ) (hp : p.Prime) (hpl : (p : 𝓞 c.F) ∈ la.asIdeal) (hg : l.GoodAt p)
    {a' : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hd : Dom a' n) (hf : f ∈ cusp Xo c U a' n)
    (hbd : BddGood Xo c la 1 f) : BddAll Xo c la 1 f := by
  intro T io m ho y hy
  by_cases hq : Dw.q = 0
  · exact hbd T io m ho y hy (GlobalTheory.T.integral_framed_point_good_reduction_definite_signature E H Dw l Xo c hq T io y)
  obtain ⟨Y, hP, hop, hS, h3, h4⟩ := exists_model (by omega) Xo c la p hp hpl hg
  let _ := io.toAlgebra
  obtain ⟨b, hb⟩ := exists_factor T (io.comp (la.valuation c.F).valuationSubring.subtype) (inV_of_overLa ho)
  let z : Sp T.Fr ⟶ Xo.XF c := pullback.lift y.1.x (spMap io) (y.1.x_over.trans (sp_comp _ _).symm)
  have hz₁ : z ≫ pullback.fst _ _ = y.1.x := pullback.lift_fst _ _ _
  have hz₂ : z ≫ pullback.snd _ _ = spMap io := pullback.lift_snd _ _ _
  obtain ⟨⟨y', ⟨hy', hz₃⟩, -⟩, -⟩ := GlobalTheory.ValuativeExtension.valuation_extension E H Dw l Xo c _ _ Y T.V T.Fr b io z hb hz₂
  by_cases hr : Set.range y' ⊆ abLocus Y.t.G
  · exact hbd T io m ho y hy (good_of_extIn Y y ⟨y', z, hz₁, hz₂, hz₃.symm, hr⟩)
  obtain ⟨T', g, ϖ, a, hg₁, hg₂, hϖ, hA⟩ := GlobalTheory.T.exists_arcData_of_badReduction_finiteExtension E H Dw l Xo c _ Y h3 hS T io b y' z hb hy' hz₂ hz₃.symm hr
  obtain ⟨i, ρ, hρ, hi, hv, -⟩ := GlobalTheory.EtaVal.finite_extension_ramification_embedding T T' g hg₁ hg₂
  have hfin : T'.FinRes := by
    let _ := g.toAlgebra
    have : Module.Finite T.V T'.V := hg₂
    exact (GlobalTheory.dvr_finite_over_complete_dvr T.V T'.V).2.2.2.2 hy
  obtain ⟨y₁, φ, hφ, hy₁⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange E H Dw l Xo c T T' io y i ρ hρ
    (fun x _ => hv x)
  let _ := (i.comp io).toAlgebra
  have e₁ : (algebraMap T'.V T'.Fr).comp g = i.comp (algebraMap T.V T.Fr) := RingHom.ext fun x => (hi x).symm
  have key := inV_of_arc U hU la Y hP hop h4 hd hf hbd (ho.bc i hρ hv) hfin (g.comp b)
    (by rw [← RingHom.comp_assoc, e₁, RingHom.comp_assoc, hb]; rfl) ϖ hϖ a (spMap g ≫ y')
    (by rw [Category.assoc, hy', sp_comp]) hA y₁ (spMap i ≫ z)
    (by rw [Category.assoc, hz₁, hy₁.1, hφ]) (by rw [Category.assoc, hz₂, sp_comp])
    (by rw [Category.assoc, ← hz₃, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp, e₁])
  obtain ⟨hE, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have e₂ : evI y₁ f = φ (evI y f) :=
    (GlobalTheory.ArcQ.evR_natural_weight_scaling E H Dw l Xo c hE a' n f hf.1 T.Fr).1 _ φ _ _ hy₁
  have e₃ : φ (evI y f) = i (evI y f) := RingHom.congr_fun hφ _
  rw [e₂, e₃, inV_iff, hv] at key
  rw [map_one, one_mul, inV_iff]
  exact nonneg_of_mul_nonneg_right key (by exact_mod_cast hρ)

theorem bddAll_of_bddGood : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) (κ : c.F), Dom a n → f ∈ cusp Xo c U a n → BddGood Xo c la κ f → BddAll Xo c la κ f := by
  intro E _ _ _ H Dw l Xo c r U hU la p hp hpl hg a n f κ hd hf hb T io m ho y hy
  have h := bddAll_one U hU la p hp hpl hg hd (Submodule.smul_mem _ κ hf)
    (fun T io m ho y hy hgood => by rw [map_one, one_mul, evI_smul]; exact hb T io m ho y hy hgood) T io m ho y hy
  rwa [map_one, one_mul, evI_smul] at h

end GlobalTheory.GoodTransfer
end
end
