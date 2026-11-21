import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointsVanishingIdealRadicalHomogeneous
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIdealOfLocally
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPointsOpenIntegralCover
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBigThetaSysWithAction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfLbIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperHomOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOnOfPowOne
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Laws3
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BasisAlongOfIndependentFibres
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LinearIndependentOfDetMemNonZeroDivisors
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardZerosOnTorsionLeOfSymmetricVeryAmple
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowerSectionOfChartFunctions
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemHasTestsOfRealPointStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormalModelThetaTupleMaximalMinors

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_points_open_integral_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (O : Type) [CommRing O] [IsNoetherianRing O] (MM : Scheme.{0}) (sM : MM ⟶ Sp O) (tM : SAB H MM) (m : ℕ), IsReduced MM → LocallyOfFiniteType sM → QuasiCompact sM → (∀ ξ ∈ genericPoints MM, ∃ (V : Scheme.{0}) (i : V ⟶ MM) (tV : SAB H V) (_ : SABMap tV tM i) (C : ZOn (i ≫ sM) tV m), IsOpenImmersion i ∧ ξ ∈ Set.range i ∧ IsIntegral V ∧ IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L (m ^ 2), A.r = r ∧ A.s = 1) → (∃ g, SmoothOfRelativeDimension g tM.G.hom) → Out.Laws → Out.Laws2 → IsProper tM.G.hom → Out.RelAmple tM.G tM.PP.L → Out.KTriv tM.G tM.PP.L → Nonempty (ZOn sM tM m) := by
  first | exact @GlobalTheory.Models.nonempty_zOn_of_components | exact GlobalTheory.Models.nonempty_zOn_of_components | (intros; apply GlobalTheory.Models.nonempty_zOn_of_components <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.FamilyModel

theorem exists_isDomain_away {R : Type} [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R] (p : Ideal R) [hp : p.IsPrime]
    (hm : ∀ q : Ideal R, q.IsPrime → q ≤ p → q = p) : ∃ f ∉ p, IsDomain (Localization.Away f) := by
  have hmin : p ∈ minimalPrimes R := ⟨⟨hp, bot_le⟩, fun q hq hle => (hm q hq.1 hle).ge⟩
  have hfin := (minimalPrimes.finite_of_isNoetherianRing R).subset (Set.diff_subset (t := {p}))
  have hnle : ¬ (hfin.toFinset.inf id ≤ p) := by
    rw [Ideal.IsPrime.inf_le' hp]
    rintro ⟨q, hq, hle⟩
    rw [Set.Finite.mem_toFinset] at hq
    exact hq.2 (hm q hq.1.1.1 hle)
  obtain ⟨f, hf, hfp⟩ := SetLike.not_le_iff_exists.1 hnle
  have hz : ∀ a ∈ p, f * a = 0 := fun a ha => by
    have : f * a ∈ sInf (minimalPrimes R) := Ideal.mem_sInf.2 fun {q} hq => by
      by_cases h : q = p
      · exact h ▸ p.mul_mem_left f ha
      · exact q.mul_mem_right a ((Finset.inf_le (f := id) (hfin.mem_toFinset.2 ⟨hq, h⟩) : _ ≤ q) hf)
    rw [minimalPrimes, Ideal.sInf_minimalPrimes] at this
    exact IsNilpotent.eq_zero (mem_nilradical.1 this)
  have hk : ∀ a, algebraMap R (Localization.Away f) a = 0 ↔ a ∈ p := fun a => by
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers f)]
    refine ⟨?_, fun ha => ⟨⟨f, Submonoid.mem_powers f⟩, hz a ha⟩⟩
    rintro ⟨⟨_, k, rfl⟩, h⟩
    exact (hp.mem_or_mem (h ▸ p.zero_mem)).resolve_left fun h => hfp (hp.mem_of_pow_mem k h)
  have : Nontrivial (Localization.Away f) := ⟨1, 0, fun h => hp.one_notMem ((hk 1).1 (by rw [map_one, h]))⟩
  have : NoZeroDivisors (Localization.Away f) := ⟨fun {x y} h => by
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers f) x
    obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers f) y
    rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_zero_iff,
      ← IsLocalization.map_eq_zero_iff (Submonoid.powers f) (Localization.Away f), hk] at h
    simp only [IsLocalization.mk'_eq_zero_iff, ← IsLocalization.map_eq_zero_iff (Submonoid.powers f) (Localization.Away f), hk]
    exact hp.mem_or_mem h⟩
  exact ⟨f, hfp, NoZeroDivisors.to_isDomain _⟩

theorem injective_of_flat {o R : Type} [CommRing o] [IsDomain o] [CommRing R] [Nontrivial R] [Algebra o R]
    (h : (algebraMap o R).Flat) : Function.Injective (algebraMap o R) :=
  have : Module.Flat o R := RingHom.flat_algebraMap_iff.1 h
  FaithfulSMul.algebraMap_injective o R

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (y : R →+* R') (φ : R' →+* R'') :
    spMap φ ≫ spMap y = spMap (φ.comp y) := (Spec.map_comp (CommRingCat.ofHom y) (CommRingCat.ofHom φ)).symm

theorem exists_integral_chart {o : Type} [CommRing o] [IsDomain o] [IsNoetherianRing o] {X : Scheme.{0}} [IsReduced X]
    (s : X ⟶ Sp o) [LocallyOfFiniteType s] [Flat s] {ξ : X} (hξ : ξ ∈ genericPoints X)
    {R₀ : Type} [CommRing R₀] (x : Sp R₀ ⟶ X) [IsOpenImmersion x] (hx : ξ ∈ Set.range x) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra o Ω) (R : Subalgebra o Ω) (φ : R₀ →+* R),
      IsOpenImmersion (spMap φ ≫ x) ∧ ξ ∈ Set.range (spMap φ ≫ x) ∧ (spMap φ ≫ x) ≫ s = spMap (algebraMap o R) ∧ R.FG ∧
      (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) ∧ Function.Injective (algebraMap o Ω) := by
  obtain ⟨β, hβ⟩ := Spec.map_surjective (x ≫ s)
  obtain ⟨p, rfl⟩ := hx
  have hft : β.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hβ]; infer_instance
  letI : Algebra o R₀ := β.hom.toAlgebra
  have : Algebra.FiniteType o R₀ := hft
  have : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing o R₀
  have : IsReduced (Sp R₀) := isReduced_of_isOpenImmersion x
  have : _root_.IsReduced R₀ := (affine_isReduced_iff (CommRingCat.of R₀)).1 this
  obtain ⟨f, hf, hd⟩ := exists_isDomain_away (show PrimeSpectrum R₀ from p).asIdeal fun q hq hle => by
    have h1 : (show Sp R₀ from (⟨q, hq⟩ : PrimeSpectrum R₀)) ⤳ p := (PrimeSpectrum.le_iff_specializes _ _).1 hle
    exact congrArg PrimeSpectrum.asIdeal
      (x.isOpenEmbedding.injective (eq_of_specializes_of_mem_genericPoints hξ (h1.map x.continuous)))
  let L := Localization.Away f
  let Ω := FractionRing L
  let j := IsScalarTower.toAlgHom o L Ω
  let e : L ≃ₐ[o] j.range := AlgEquiv.ofInjective j (IsFractionRing.injective L Ω)
  have hiso : IsIso (spMap (e : L →+* j.range)) := by
    have : IsIso (CommRingCat.ofHom (e : L →+* j.range)) := e.toRingEquiv.toCommRingCatIso.isIso_hom
    infer_instance
  have ho : IsOpenImmersion (spMap ((e : L →+* j.range).comp (algebraMap R₀ L)) ≫ x) := by
    rw [← spMap_comp]; infer_instance
  have hs : (spMap ((e : L →+* j.range).comp (algebraMap R₀ L)) ≫ x) ≫ s = spMap (algebraMap o j.range) := by
    rw [Category.assoc, ← hβ]
    refine (spMap_comp β.hom _).trans (congrArg spMap (RingHom.ext fun a => ?_))
    exact e.commutes a
  refine ⟨Ω, inferInstance, inferInstance, j.range, _, ho, ?_, hs, ?_, fun z => ?_, ?_⟩
  · obtain ⟨q, hq⟩ := (PrimeSpectrum.localization_away_comap_range L f).ge hf
    obtain ⟨q', rfl⟩ := (spMap (e : L →+* j.range)).surjective q
    refine ⟨q', ?_⟩
    rw [← spMap_comp, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact congrArg x hq
  · have : Algebra.FiniteType o L := Algebra.FiniteType.trans (S := R₀) inferInstance inferInstance
    exact (Subalgebra.fg_iff_finiteType _).2 (this.equiv e)
  · obtain ⟨a, c, -, rfl⟩ := IsFractionRing.div_surjective (A := L) z
    exact ⟨_, ⟨a, rfl⟩, _, ⟨c, rfl⟩, rfl⟩
  · have hfl : Flat (spMap (algebraMap o j.range)) := by rw [← hs]; infer_instance
    have h2 : (algebraMap o j.range).Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).1 hfl
    have h3 := injective_of_flat h2
    exact fun a b h => h3 (Subtype.ext h)

theorem eval₂_mul_eq_zero {o R σ : Type} [CommRing o] [CommRing R] {I : Ideal (MvPolynomial σ o)}
    (hI : ∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) (β : o →+* R) {v : σ → R}
    (hv : ∀ F ∈ I, MvPolynomial.eval₂ β v F = 0) (c : R) : ∀ F ∈ I, MvPolynomial.eval₂ β (fun a => c * v a) F = 0 := by
  intro F hF
  have key : ∀ (e : ℕ) (P : MvPolynomial σ o), P.IsHomogeneous e →
      MvPolynomial.eval₂ β (fun a => c * v a) P = c ^ e * MvPolynomial.eval₂ β v P := fun e P hP => by
    rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have h1 : ∑ i ∈ d.support, d i = e := by
      have := hP (MvPolynomial.mem_support_iff.1 hd)
      simpa [Finsupp.weight_apply, Finsupp.sum] using this
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h1]
    ring
  rw [← MvPolynomial.sum_homogeneousComponent F, MvPolynomial.eval₂_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [key e _ (MvPolynomial.homogeneousComponent_isHomogeneous e F), hv _ (hI F hF e), mul_zero]

theorem closure_ratios_eq_top (h₁ : Out.Laws) (h₂ : Out.Laws2) {o : Type} [CommRing o] {g n N' : ℕ} {J : Type}
    {b : TBase o (N' ^ 2)} {em : o →+* ℂ} (hem : Function.Injective em) {C : TObj g (N' ^ 2) J b (spMap em) → Prop}
    (F : ThetaFam n em C) {Ω : Type} [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (i : Sp R ⟶ F.MM) [IsOpenImmersion i]
    (hi : i ≫ F.s = spMap (algebraMap o R)) (hR : ∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c)
    (v : GlobalTheory.ZM.Ix g (N' ^ 2) → R) (hv : F.univ.HasTh i v) :
    Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i i', x = (v i : Ω) / (v i' : Ω)}) = ⊤ := by
  set K := Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i i', x = (v i : Ω) / (v i' : Ω)}) with hK
  have hI := (GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree o g N' J b em C hem).2.1
  let ρ : R →+* Ω := R.val.toRingHom
  have hx : (spMap ρ ≫ i) ≫ F.s = spMap (algebraMap o Ω) := by
    rw [Category.assoc, hi, spMap_comp]; rfl
  have hvΩ := T.hasThetaConstants_ring_baseChange h₂ o g N' J b _ _ F.univ R Ω ρ i v hv
  obtain ⟨v', hv', he, hc⟩ := F.loc Ω _ _ hx
  obtain ⟨u, hu⟩ := ThetaUniq.exists_unit_local h₁.globalFns F.univ _ hvΩ hv'
  obtain ⟨c₀, hc₀⟩ := hc ⊥ Ideal.isPrime_bot 0
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, v' a₀ ≠ 0 := ⟨_, hc₀⟩
  let w : GlobalTheory.ZM.Ix g (N' ^ 2) → K := fun a => ⟨v a / v a₀, Subfield.subset_closure (Or.inr ⟨a, a₀, rfl⟩)⟩
  have hw : ∀ a, K.subtype (w a) = (v' a₀)⁻¹ * v' a := fun a => by
    rw [hu a, hu a₀]
    have := u.ne_zero
    show (v a : Ω) / v a₀ = (u * (v a₀ : Ω))⁻¹ * (u * (v a : Ω))
    rw [mul_inv, _root_.mul_mul_mul_comm, inv_mul_cancel₀ this, _root_.one_mul, div_eq_inv_mul]
  let β : o →+* K := (algebraMap o Ω).codRestrict K fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
  have hβ : K.subtype.comp β = algebraMap o Ω := rfl
  have he' := eval₂_mul_eq_zero hI _ he (v' a₀)⁻¹
  have hc' : ∀ a, ∃ c, (v' a₀)⁻¹ * v' (a + (N' / n) • c) ≠ 0 := fun a =>
    (hc ⊥ Ideal.isPrime_bot a).imp fun c h => mul_ne_zero (inv_ne_zero ha₀) h
  have mΩ : InMM n N' (thIdeal em C) (algebraMap o Ω) (fun a => (v' a₀)⁻¹ * v' a) :=
    ⟨he', fun q hq a => by rw [Ideal.eq_bot_of_prime q]; exact hc' a⟩
  have mK : InMM n N' (thIdeal em C) β w := by
    refine ⟨fun P hP => K.subtype.injective ?_, fun q hq a => ?_⟩
    · rw [MvPolynomial.eval₂_comp_left, map_zero, hβ, show K.subtype ∘ w = _ from funext hw]
      exact he' P hP
    · rw [Ideal.eq_bot_of_prime q]
      exact (hc' a).imp fun c h h0 => h (by rw [← hw, Ideal.mem_bot.1 h0, map_zero])
  obtain ⟨y, ⟨hy, hty⟩, -⟩ := F.pts K β w mK
  have hxy : spMap K.subtype ≫ y = spMap ρ ≫ i := by
    refine (F.pts Ω _ _ mΩ).unique ⟨?_, ?_⟩ ⟨hx, ThetaClosed.hasTh_unit_mul F.univ (Units.mk0 _ (inv_ne_zero ha₀)) hv'⟩
    · rw [Category.assoc, hy, spMap_comp, hβ]
    · have := T.hasThetaConstants_ring_baseChange h₂ o g N' J b _ _ F.univ K Ω K.subtype y w hty
      simpa only [hw] using this
  have hle : Set.range y ⊆ Set.range i := by
    rintro _ ⟨p, rfl⟩
    let q : Sp Ω := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω)
    obtain rfl : p = spMap K.subtype q := Subsingleton.elim (α := PrimeSpectrum K) _ _
    exact ⟨spMap ρ q, by rw [← Scheme.Hom.comp_apply, ← hxy, Scheme.Hom.comp_apply]⟩
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (IsOpenImmersion.lift i y hle)
  have h3 : K.subtype.comp ψ.hom = ρ := by
    have h4 : spMap (K.subtype.comp ψ.hom) = spMap ρ := by
      rw [← cancel_mono i, ← hxy, ← spMap_comp, Category.assoc]
      congr 1
      exact (congrArg (· ≫ i) hψ).trans (IsOpenImmersion.lift_fac _ _ _)
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h4)
  have h5 : ∀ a ∈ R, a ∈ K := fun a ha => by
    have : a = (ψ.hom ⟨a, ha⟩ : K) := by
      have h6 := (DFunLike.congr_fun h3 (⟨a, ha⟩ : R)).symm
      exact h6
    rw [this]; exact Subtype.property _
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨a, ha, c, hc, rfl⟩ := hR z
  exact K.div_mem (h5 a ha) (h5 c hc)

theorem exists_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {o : Type} [CommRing o] {g k : ℕ}
    {J : Type} {b : TBase o k} {S S' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} (t : TObj g k J b s) (τ : SAB H S)
    (φ : τ.G ≅ t.A) [IsMonHom φ.hom] (hL : LBIso τ.PP.L (t.L.pull φ.hom.left)) (f : S' ⟶ S) (hf : f ≫ s = s') :
    ∃ (u : TObj g k J b s') (t₀ : SAB H S') (_ : SABMap t₀ τ f) (e : t₀.G ≅ u.A),
      TMap u t f ∧ IsMonHom e.hom ∧ LBIso t₀.PP.L (u.L.pull e.hom.left) := by
  obtain ⟨u, hu⟩ := tObj_pull o g k J b S S' s s' f t hf
  obtain ⟨t₀, ⟨m⟩⟩ : ∃ t₀ : SAB H S', Nonempty (SABMap t₀ τ f) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f τ
    exact ⟨_, ⟨m⟩⟩
  have hu' := hu
  obtain ⟨ψ, hψ, hLu, -⟩ := hu'
  obtain ⟨e, he, hc⟩ := grpPullback_iso ((m.cart.comp (isGrpPullback_of_iso φ)).congr (Category.comp_id _) rfl) hψ
  have hm : LBIso t₀.PP.L (τ.PP.L.pull m.φ) := m.lin.imp fun _ h => h.1
  refine ⟨u, t₀, m, e, hu, he, ?_⟩
  refine LBIso.trans t₀.PP.isLB (pull_isLB τ.PP.isLB _) (pull_isLB u.isLB _) hm ?_
  exact LBIso.trans (pull_isLB τ.PP.isLB _) (pull_isLB t.isLB _) (pull_isLB u.isLB _)
    (GenSpread.lbIso_pull_of_lbIso hL _ rfl) (GenSpread.lbIso_pull_of_lbIso hLu _ hc.symm).symm

theorem nonempty_zOn_of_components (hcomp : Out.Laws → Out.Laws2 → GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → GlobalTheory.ZH.ZHGeoSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g n : ℕ), n.Prime → Odd n → ∃ k j₀ : ℕ, ∀ j ≥ j₀, ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R : Subalgebra o Ω) (J : Type) (b : TBase o ((n ^ j) ^ 2)) (u : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap o R))) (t₀ : SAB H (Sp R)) (e : t₀.G ≅ u.A) (v : GlobalTheory.ZM.Ix g ((n ^ j) ^ 2) → R), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) → IsMonHom e.hom → LBIso t₀.PP.L (u.L.pull e.hom.left) → u.HasTh (𝟙 _) v → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i i', x = (v i : Ω) / (v i' : Ω)})) Ω → ∃ C : ZOn (spMap (algebraMap o R)) t₀ (n ^ k), IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L ((n ^ k) ^ 2), A.r = r ∧ A.s = 1) : Out.Laws → Out.Laws2 → GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → GlobalTheory.ZH.ZHGeoSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n : ℕ), 1 ≤ D.p + D.q → n.Prime → Odd n → ∃ k j₀ : ℕ, ∀ j ≥ j₀, ∀ N' : ℕ, N' = n ^ j → ∀ (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (b : TBase (RZ H n (N' ^ 2)) (N' ^ 2)) (F : ThetaFam n (RZ H n (N' ^ 2)).subtype (PELClass (b := b) D a bas (RZ.rt H n (N' ^ 2)) (RZ H n (N' ^ 2)).subtype)) (τ : SAB H F.MM), IsSympBasis D bas → Subring.closure (Set.range a) = ⊤ → (∃ w w', a w = H.w0 ∧ a w' = H.bar H.w0) → (b.ζ : RZ H n (N' ^ 2)) = RZ.ze H n (N' ^ 2) → IsPEL D a bas (RZ.rt H n (N' ^ 2)) F.univ τ → SmoothOfRelativeDimension D.dim (pullback.snd F.s (spMap (algebraMap (RZ H n (N' ^ 2)) (FractionRing (RZ H n (N' ^ 2)))))) → Nonempty (ZOn F.s τ (n ^ k)) := by
  intro h₁ h₂ h₃ h₄ h₅ h₆ E _ _ _ H D n _ hn ho
  obtain ⟨k, j₀, hz⟩ := hcomp h₁ h₂ h₃ h₄ h₅ h₆ E H (Module.finrank ℤ D.La / 2) n hn ho
  refine ⟨k, j₀, ?_⟩
  rintro j hj _ rfl g J _ a bas b F τ - - - - ⟨φ, hφ, hL, -⟩ -
  obtain rfl : g = Module.finrank ℤ D.La / 2 := by
    have := bas.finrank_eq
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
    omega
  have hded : IsDedekindDomain (RZ H n ((n ^ j) ^ 2)) :=
    BaseRing.isDedekindDomain_RZ (HostModel.level H ((n ^ j) ^ 2) (pow_pos (pow_pos hn.pos j) 2)) (e := j * 2) hn.pos
      (by rw [pow_mul]; exact dvd_rfl)
  obtain ⟨N, q, hq₀, hqc, hs⟩ := F.qproj
  have hp : IsProper (PSpace.str (RZ H n ((n ^ j) ^ 2)) N) := isProper_str _ _
  have hft : LocallyOfFiniteType F.s := by rw [← hs]; infer_instance
  have hq : QuasiCompact F.s := by rw [← hs]; infer_instance
  have hg := isGrpPullback_of_iso φ
  obtain ⟨hab, hamp, hk⟩ := pol_pull _ _ _ _ _ _ _ _ F.univ.isLB τ.PP.isLB F.univ.ab hg hL
  refine T.generic_points_open_integral_cover E H _ _ F.s τ _ F.reduced hft hq (fun ξ hξ => ?_)
    ⟨_, (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hg.1 F.univ.dim⟩ h₁ h₂ hab.proper
    (hamp F.univ.ample) (hk F.univ.ktriv)
  obtain ⟨R₀, _, x, v₀, hx, hξx, hv₀⟩ := ThetaLocal.exists_hasTh h₁ h₂ _ _ _ J b _ _ F.univ ho.pow ξ
  have := F.reduced
  have := F.flat
  obtain ⟨Ω, _, _, R, ψ, hi, hξi, his, hfg, hfr, hinj⟩ := exists_integral_chart F.s hξ x hξx
  have hv := T.hasThetaConstants_ring_baseChange h₂ _ _ _ J b _ _ F.univ R₀ R ψ x v₀ hv₀
  have : GlobalTheory.ZH.ArithBase (RZ H n ((n ^ j) ^ 2)) Ω :=
    ⟨hded, BaseRing.finiteType_RZ H _ _, charZero_of_injective_algebraMap hinj, hinj⟩
  obtain ⟨u, t₀, m, e, hu, he, hLe⟩ := exists_pull F.univ τ φ hL _ his
  have htop := closure_ratios_eq_top h₁ h₂ Subtype.val_injective F R _ his hfr _ hv
  have hC := hz j hj _ Ω R J b u t₀ e (fun a => ψ (v₀ a)) hfg hfr he hLe
    ((hasTh_iff_of_tmap _ _ _ J b _ _ F.univ _ _ u _ R (𝟙 _) _ hu).2 (by rw [Category.id_comp]; exact hv))
    (Module.Finite.of_surjective (Algebra.linearMap _ Ω) fun z => ⟨⟨z, by rw [htop]; trivial⟩, rfl⟩)
  rw [← his] at hC
  obtain ⟨C, hC⟩ := hC
  exact ⟨_, _, t₀, m, C, hi, hξi, inferInstance, hC⟩

end GlobalTheory.FamilyModel
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
open Classical

namespace GlobalTheory

theorem isOpen_setOf_TT_eq_bot : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (M : GlobalTheory.ZH.RatModel o Ω) (I : Type) (d : I → Ω) (e : ℕ), M.HasDiv S.th → (∀ z : M.Z, ∀ x₀ ∈ S.supI M z, (S.TT M z = ⊥ ↔ ∃ k, d k ≠ 0 ∧ S.th x₀ ^ e / d k ∈ M.O z)) → IsOpen {z : M.Z | S.TT M z = ⊥} := by
  intro o Ω _ _ _ S M I d e hdiv h
  haveI : NeZero (S.r * S.N) :=
    ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  refine isOpen_iff_forall_mem_open.2 fun z hz => ?_
  obtain ⟨x₀, hx₀⟩ := hdiv z
  obtain ⟨k, hk, hreg⟩ := (h z x₀ hx₀).1 hz
  refine ⟨{w | M.Div S.th x₀ w} ∩ {w | S.th x₀ ^ e / d k ∈ M.O w}, ?_,
    (M.isOpen_setOf_div S.th x₀).inter (M.isOpen_setOf_mem_O _), hx₀, hreg⟩
  rintro w ⟨hw1, hw2⟩
  exact (h w x₀ hw1).2 ⟨k, hk, hw2⟩

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
open Classical

namespace GlobalTheory.ModelOfOutput

theorem exists_openImmersion_section {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {U : Scheme.{0}} [IsIntegral U] (g : U ⟶ Sp R) [IsSeparated g] [LocallyOfFiniteType g]
    (x : Sp K ⟶ U) [IsDominant x] (hx : x ≫ g = spMap (algebraMap R K)) :
    ∃ (W : (Sp R).Opens) (j : W.toScheme ⟶ U), Dense (W : Set (Sp R)) ∧ IsOpenImmersion j ∧ IsDominant j ∧
      j ≫ g = W.ι := by
  obtain ⟨e, he⟩ := IsGenericPointHom.fractionField R K
  obtain ⟨W, hW, j, h₁, h₂⟩ := spread_out_of_isGermInjective' (𝟙 (Sp R)) g (x := genericPoint (Sp R)) (e.inv ≫ x)
    (by rw [Category.assoc, hx, Category.comp_id, Iso.inv_comp_eq]; exact he.symm)
  rw [Category.comp_id] at h₂
  have hd : IsDominant j := by
    have : IsDominant (W.fromSpecStalkOfMem _ hW ≫ j) := h₁ ▸ inferInstance
    exact IsDominant.of_comp (W.fromSpecStalkOfMem _ hW) j
  have hr : Set.range j ⊆ Set.range (g ⁻¹ᵁ W).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    show g (j w) ∈ W
    rw [← Scheme.Hom.comp_apply, h₂]
    exact w.2
  have e₁ := IsOpenImmersion.lift_fac (g ⁻¹ᵁ W).ι j hr
  set j' := IsOpenImmersion.lift (g ⁻¹ᵁ W).ι j hr
  have : IsDominant (j' ≫ (g ⁻¹ᵁ W).ι) := e₁.symm ▸ hd
  have : IsDominant j' := IsDominant.of_comp_of_isOpenImmersion _ (g ⁻¹ᵁ W).ι
  have e₂ : j' ≫ g ∣_ W = 𝟙 _ := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, e₁, h₂, Category.id_comp]
  have e₃ : g ∣_ W ≫ j = (g ⁻¹ᵁ W).ι :=
    ext_of_isDominant_of_isSeparated g (by rw [Category.assoc, h₂, morphismRestrict_ι]) j'
      (by rw [← Category.assoc, e₂, Category.id_comp, e₁])
  have : IsIso j' := ⟨g ∣_ W, e₂, by
    rw [← cancel_mono (g ⁻¹ᵁ W).ι, Category.assoc, e₁, e₃, Category.id_comp]⟩
  refine ⟨W, j, W.isOpen.dense ⟨_, hW⟩, ?_, hd, h₂⟩
  rw [← e₁]
  infer_instance

theorem flat_ratModel {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [h : GlobalTheory.ZH.ArithBase o Ω]
    (M : GlobalTheory.ZH.RatModel o Ω) : Flat M.s := by
  have := h.ded
  have := M.sep
  have : IsSchemeTheoreticallyDominant M.pt := .of_isDominant _
  have : QuasiCompact M.pt := ⟨fun U _ _ => (Set.toFinite _).isCompact⟩
  have : Flat (M.pt ≫ M.s) := by
    rw [M.pt_s]
    refine Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 ?_)
    have : FaithfulSMul o Ω := (faithfulSMul_iff_algebraMap_injective o Ω).2 h.inj
    infer_instance
  exact flat_of_schemeDominant_of_isDedekindDomain (O := CommRingCat.of o) M.pt M.s

theorem exists_zOn : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R : Subalgebra o Ω) (t₀ : SAB H (Sp R)) (S : GlobalTheory.ZH.ThetaSys o Ω) (ρ : S.Real) (h : R ≤ S.R) (φ : ρ.P.A.left ⟶ t₀.G.left) (act : OAct (𝓞 E) ρ.P.A) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Z : GlobalTheory.ZH.ZHOut ρ M U₀ EE) (m : ℕ) (r₀ : ℤ), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) → S.Over₀ M U₀ → IsOpen (abLocus Z.G) → IsGrpPullback ρ.P.A t₀.G (spMap (Subalgebra.inclusion h).toRingHom) φ → LBIso ρ.P.L (t₀.PP.L.pull φ) → (∀ a, (act.act a).left ≫ φ = φ ≫ (t₀.act.act a).left) → (letI := ρ.P.isAb.comm; ∀ a, LBIso (cubeLB ρ.P.A ![fst _ _ ≫ act.act a, snd _ _] ρ.P.L) (cubeLB ρ.P.A ![fst _ _, snd _ _ ≫ act.act (H.bar a)] ρ.P.L)) → (letI := ρ.P.isAb.comm; LBIso ρ.P.L (cubeLB ρ.P.A ![𝟙 _, act.act H.w0] ρ.P.L)) → (∀ r : ℤ, r₀ ≤ r → ∃ A : GlobalTheory.LN.AmpFrames Z.G Z.L.L (m ^ 2), A.r = r ∧ A.s = 1) → ∃ C : ZOn (spMap (algebraMap o R)) t₀ m, IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L (m ^ 2), A.r = r ∧ A.s = 1 := by
  intro _ _ E _ _ _ H o Ω _ _ _ hb R t₀ S ρ h φ act M U₀ EE Z m r₀ _ hfr hO hop hφ hL hact hadj hprim hamp
  obtain ⟨act', h₂, h₃, hact', hgood⟩ := GlobalTheory.TripleOut.exists_triple GlobalTheory.homExtension_semiAbelian_dvr o Ω S ρ M U₀ EE Z
    E H act hO hadj hprim
  let t : SAB H M.Z := SAB.mk (H := H) Z.G Z.semi act' Z.L Z.cub Z.sym h₂ h₃
  have : IsFractionRing R Ω := IsFractionRing.of_field R Ω fun y => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hfr y
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩
  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    exact (GlobalTheory.ZH.top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hO.ne)
  have ex := IsOpenImmersion.lift_fac U₀.ι M.pt hr
  set x := IsOpenImmersion.lift U₀.ι M.pt hr
  have : IsDominant (x ≫ U₀.ι) := ex.symm ▸ inferInstance
  have : IsDominant x := IsDominant.of_comp_of_isOpenImmersion _ U₀.ι
  have : Nonempty U₀.toScheme := ⟨⟨_, hO.ne.some_mem⟩⟩
  have : IsIntegral U₀.toScheme := isIntegral_of_isOpenImmersion U₀.ι
  let g : U₀.toScheme ⟶ Sp R := Z.u₀ ≫ spMap (Subalgebra.inclusion h).toRingHom
  have hx : x ≫ g = spMap (algebraMap R Ω) := by
    rw [← Category.assoc, Z.u₀_gen x ex, ← Spec.map_comp]
    rfl
  have hg : g ≫ spMap (algebraMap o R) = U₀.ι ≫ M.s := by
    refine ext_of_isDominant x ?_
    rw [← Category.assoc, hx, ← Category.assoc, ex, M.pt_s, ← Spec.map_comp]
    rfl
  have := M.sep
  have := M.lft
  have : IsSeparated (g ≫ spMap (algebraMap o R)) := hg ▸ inferInstance
  have : IsSeparated g := IsSeparated.of_comp g (spMap (algebraMap o R))
  have : LocallyOfFiniteType (g ≫ spMap (algebraMap o R)) := hg ▸ inferInstance
  have : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g (spMap (algebraMap o R))
  obtain ⟨W, j, hW, hj₁, hj₂, hj⟩ := exists_openImmersion_section g x hx
  obtain ⟨PP', cub, sym, adj, prim, m₁, -⟩ := sabPull GlobalTheory.laws3.cubePull W.ι t₀
  set tW : SAB H W.toScheme := ⟨(Over.pullback W.ι).obj t₀.G, IsSemiAbelian.pullback W.ι t₀.G t₀.semi,
    OAct.pullback W.ι t₀.G t₀.act, PP', cub, sym, adj, prim⟩
  clear_value tW
  have hP := (isGrpPullback_pullback ρ.P.A Z.u₀).comp hφ
  let ψ : tW.G.left ⟶ pullback ρ.P.A.hom Z.u₀ :=
    hP.1.lift m₁.φ (tW.G.hom ≫ j) (by rw [m₁.cart.1.w, Category.assoc, hj])
  have ψ₁ : ψ ≫ pullback.fst ρ.P.A.hom Z.u₀ ≫ φ = m₁.φ := hP.1.lift_fst _ _ _
  have ψ₂ : ψ ≫ pullback.snd ρ.P.A.hom Z.u₀ = tW.G.hom ≫ j := hP.1.lift_snd _ _ _
  have hψ : IsGrpPullback tW.G ((Over.pullback Z.u₀).obj ρ.P.A) j ψ :=
    hP.cancel (m₁.cart.congr hj.symm ψ₁.symm) ψ₂
  have hA : IsProper ρ.P.A.hom := GlobalTheory.ZH.isProper_hom_of_relAmple ρ.P.ample
  have hA' : IsProper tW.G.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) hψ.1 (inferInstanceAs (IsProper (pullback.snd ρ.P.A.hom Z.u₀)))
  have hψa : ∀ a, (tW.act.act a).left ≫ ψ = ψ ≫ ((Over.pullback Z.u₀).map (act.act a)).left := fun a => by
    have A : ((Over.pullback Z.u₀).map (act.act a)).left ≫ pullback.fst ρ.P.A.hom Z.u₀ =
      pullback.fst ρ.P.A.hom Z.u₀ ≫ (act.act a).left := pullback.lift_fst _ _ _
    have B : ((Over.pullback Z.u₀).map (act.act a)).left ≫ pullback.snd ρ.P.A.hom Z.u₀ =
      pullback.snd ρ.P.A.hom Z.u₀ := Over.w ((Over.pullback Z.u₀).map (act.act a))
    apply hP.1.hom_ext
    · calc ((tW.act.act a).left ≫ ψ) ≫ pullback.fst ρ.P.A.hom Z.u₀ ≫ φ
          = m₁.φ ≫ (t₀.act.act a).left := by rw [Category.assoc, ψ₁]; exact m₁.act a
        _ = ψ ≫ (pullback.fst ρ.P.A.hom Z.u₀ ≫ (act.act a).left) ≫ φ := by
          rw [← ψ₁]; simp only [Category.assoc, hact]
        _ = _ := by rw [← A]; simp only [Category.assoc]
    · calc ((tW.act.act a).left ≫ ψ) ≫ pullback.snd ρ.P.A.hom Z.u₀
          = tW.G.hom ≫ j := by rw [Category.assoc, ψ₂, ← Category.assoc, Over.w]
        _ = ψ ≫ ((Over.pullback Z.u₀).map (act.act a)).left ≫ pullback.snd ρ.P.A.hom Z.u₀ := by rw [B, ψ₂]
        _ = _ := (Category.assoc _ _ _).symm
  have hLW : LBIso tW.PP.L (t.PP.L.pull (ψ ≫ Z.φ)) := by
    have a₁ : LBIso tW.PP.L (t₀.PP.L.pull m₁.φ) := by
      obtain ⟨w, hw, -⟩ := m₁.lin
      exact ⟨w, hw⟩
    have a₂ : LBIso (ρ.P.L.pull (ψ ≫ pullback.fst ρ.P.A.hom Z.u₀)) (t₀.PP.L.pull m₁.φ) :=
      GenSpread.lbIso_pull_of_lbIso hL _ (by rw [Category.assoc, ψ₁])
    have a₃ : LBIso (Z.L.L.pull (ψ ≫ Z.φ)) (ρ.P.L.pull (ψ ≫ pullback.fst ρ.P.A.hom Z.u₀)) :=
      GenSpread.lbIso_pull_comp ψ rfl rfl ⟨Z.w, Z.w_gen⟩
    exact LBIso.trans tW.PP.isLB (pull_isLB t₀.PP.isLB _) (pull_isLB Z.L.isLB _) a₁
      (LBIso.trans (pull_isLB Z.L.isLB _) (pull_isLB ρ.P.isLB _) (pull_isLB t₀.PP.isLB _) a₃ a₂).symm
  obtain ⟨m₂, -⟩ := GlobalTheory.exists_sabMap_of_lbIso E H M.Z W.toScheme t tW (j ≫ U₀.ι) (ψ ≫ Z.φ)
    ⟨inferInstance, fun y _ K _ _ p _ => inferInstance⟩ (hψ.comp Z.cart)
    (fun a => by
      rw [← Category.assoc, hψa, Category.assoc, Category.assoc]
      exact congrArg (ψ ≫ ·) (hact' a)) hLW
  obtain ⟨A, hA₁, hA₂⟩ := hamp r₀ le_rfl
  have : IsDominant U₀.ι := ⟨by
    rw [DenseRange, Scheme.Opens.range_ι]
    exact U₀.isOpen.dense hO.ne⟩
  exact ⟨⟨M.Z, M.s, hO.normal, hO.proj, flat_ratModel M, t, Z.qproj,
    hgood (GlobalTheory.ZH.abOpen_of_isOpen_abLocus o Ω S ρ M U₀ EE Z hO hop), W, hW, j ≫ U₀.ι, inferInstance, inferInstance,
    by rw [Category.assoc, ← hg, ← Category.assoc, hj], tW, m₁, m₂, A⟩, M.integral, hA₂,
    fun r hr => hamp r (hA₁ ▸ hr)⟩

end GlobalTheory.ModelOfOutput
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_birationalModel_semiAbelian_ampleFrames : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R : Subalgebra o Ω) (t₀ : SAB H (Sp R)) (S : GlobalTheory.ZH.ThetaSys o Ω) (ρ : S.Real) (h : R ≤ S.R) (φ : ρ.P.A.left ⟶ t₀.G.left) (act : OAct (𝓞 E) ρ.P.A) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Z : GlobalTheory.ZH.ZHOut ρ M U₀ EE) (m : ℕ) (r₀ : ℤ), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) → S.Over₀ M U₀ → IsOpen (abLocus Z.G) → IsGrpPullback ρ.P.A t₀.G (spMap (Subalgebra.inclusion h).toRingHom) φ → LBIso ρ.P.L (t₀.PP.L.pull φ) → (∀ a, (act.act a).left ≫ φ = φ ≫ (t₀.act.act a).left) → (letI := ρ.P.isAb.comm; ∀ a, LBIso (cubeLB ρ.P.A ![fst _ _ ≫ act.act a, snd _ _] ρ.P.L) (cubeLB ρ.P.A ![fst _ _, snd _ _ ≫ act.act (H.bar a)] ρ.P.L)) → (letI := ρ.P.isAb.comm; LBIso ρ.P.L (cubeLB ρ.P.A ![𝟙 _, act.act H.w0] ρ.P.L)) → (∀ r : ℤ, r₀ ≤ r → ∃ A : GlobalTheory.LN.AmpFrames Z.G Z.L.L (m ^ 2), A.r = r ∧ A.s = 1) → ∃ C : ZOn (spMap (algebraMap o R)) t₀ m, IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L (m ^ 2), A.r = r ∧ A.s = 1 := by
  first | exact @GlobalTheory.ModelOfOutput.exists_zOn | exact GlobalTheory.ModelOfOutput.exists_zOn | (intros; apply GlobalTheory.ModelOfOutput.exists_zOn <;> assumption)
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AmpModel

section Basic

theorem exists_polAV {Z : Scheme.{0}} (G : Over Z) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (g : ℕ)
    (hd : SmoothOfRelativeDimension g G.hom) (L : RigLB G) (hs : L.IsSymmetric) (W : Z.Opens)
    (ha : RelAmple ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)))
    (hk : KTriv ((Over.pullback W.ι).obj G) (L.L.pull (pullback.fst G.hom W.ι)))
    {K : Type} [Field K] (x : Sp K ⟶ Z) (hx : Set.range x ⊆ W) :
    ∃ (A : PolAV (Sp K)) (φ : A.A.left ⟶ G.left), IsGrpPullback A.A G x φ ∧ LBIso A.L (L.L.pull φ) ∧ A.g = g := by
  obtain ⟨x', hx'⟩ : ∃ x' : Sp K ⟶ W.toScheme, x' ≫ W.ι = x :=
    ⟨IsOpenImmersion.lift W.ι x (by rwa [Scheme.Opens.range_ι]), IsOpenImmersion.lift_fac _ _ _⟩
  have h := isGrpPullback_pullback G x
  have h₀ := isGrpPullback_pullback G W.ι
  have h₂ := h.congr hx'.symm rfl
  let ψ : ((Over.pullback x).obj G).left ⟶ ((Over.pullback W.ι).obj G).left :=
    h₀.1.lift _ _ (h₂.1.w.trans (Category.assoc _ _ _).symm)
  have hψ : ψ ≫ pullback.fst G.hom W.ι = pullback.fst G.hom x := h₀.1.lift_fst _ _ _
  have h₃ : IsGrpPullback ((Over.pullback x).obj G) ((Over.pullback W.ι).obj G) x' ψ :=
    h₀.cancel (h₂.congr rfl hψ.symm) (h₀.1.lift_snd _ _ _)
  have hL := pull_isLB L.isLB (pullback.fst G.hom x)
  have hL₀ := pull_isLB L.isLB (pullback.fst G.hom W.ι)
  obtain ⟨w, hw⟩ : LBIso (L.L.pull (pullback.fst G.hom x)) ((L.L.pull (pullback.fst G.hom W.ι)).pull ψ) :=
    LBIso.chartPull (chartPullId _)
      (chartPullLinComb L.L _ (fun _ : PUnit => ψ) (fun _ => pullback.fst G.hom x) (fun _ => 1) (𝟙 _)
        fun _ => hψ.trans (Category.id_comp _).symm)
      (PolBaseChange.lbIso_refl hL)
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (X := W.toScheme) (U := ⊤)
    (x := x' (IsLocalRing.closedPoint K)) trivial
  have hamp : RelAmple ((Over.pullback x).obj G) (L.L.pull (pullback.fst G.hom x)) :=
    relAmple_pull h₃.1 hL₀ hL ((isGen_iff w).1 hw) V hV
      (fun y => by rwa [Subsingleton.elim (α := PrimeSpectrum K) y (IsLocalRing.closedPoint K)]) ha
  have hsa := IsSemiAbelian.pullback x G hG
  have hA : IsAbelianScheme ((Over.pullback x).obj G) :=
    { comm := hsa.comm, smooth := hsa.smooth, proper := projProper _ _ _ (ProjSpace.isProjOver_of_relAmple hamp)
      geomConnected := hsa.geomConnected }
  exact ⟨{ A := (Over.pullback x).obj G
           isAb := hA
           g := g
           smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 hd
           L := L.L.pull (pullback.fst G.hom x)
           isLB := hL
           rigid := PolBaseChange.rigidified_pull h ⟨L.rig, L.rigGen⟩
           sym := PolBaseChange.sym_pull h (CechPic.sym_of_isSymmetric L hs)
           ample := hamp
           ktriv := kTriv_pull h₃ hL₀ hL ((isGen_iff w).1 hw) hk },
    pullback.fst G.hom x, h, PolBaseChange.lbIso_refl hL, rfl⟩

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem isOpen_TT_eq_bot (S : ThetaSys o Ω) (M : RatModel o Ω) : IsOpen {z | S.TT M z = ⊥} := by
  haveI : NeZero (S.r * S.N) := ⟨(Nat.mul_pos S.r_pos (lt_of_lt_of_le two_pos S.N_ge)).ne'⟩
  refine isOpen_iff_forall_mem_open.2 fun z hz => ⟨⋂ x ∈ S.supI M z, {z' | M.Div S.th x z'}, fun z' hz' => ?_,
    (Set.toFinite _).isOpen_biInter fun x _ => M.isOpen_setOf_div S.th x, Set.mem_iInter₂.2 fun x hx => hx⟩
  have hle : S.HH M z ≤ S.HH M z' := AddSubgroup.closure_mono fun x hx => Set.mem_iInter₂.1 hz' x hx
  refine eq_bot_iff.2 fun a ha => ?_
  have : a ∈ S.TT M z := fun h hh => ha h (hle hh)
  rwa [show S.TT M z = ⊥ from hz] at this

theorem exists_unit (M : RatModel o Ω) {W : M.Z.Opens} (hW : (W : Set M.Z).Nonempty) {x : Ω} (h0 : x ≠ 0)
    (h : ∀ z ∈ W, x ∈ M.O z) (h' : ∀ z ∈ W, x⁻¹ ∈ M.O z) : ∃ u : Γ(M.Z, W)ˣ, M.res W hW u.val = x := by
  obtain ⟨f, hf⟩ := (RatModel.mem_ringOn_iff_exists hW).1 (RatModel.mem_ringOn.2 h)
  obtain ⟨f', hf'⟩ := (RatModel.mem_ringOn_iff_exists hW).1 (RatModel.mem_ringOn.2 h')
  rw [← M.res_apply W hW] at hf hf'
  have e : f * f' = 1 := M.res_injective W hW (by rw [map_mul, hf, hf', map_one, mul_inv_cancel₀ h0])
  exact ⟨⟨f, f', e, (mul_comm _ _).trans e⟩, hf⟩

theorem exists_GL (M : RatModel o Ω) {W : M.Z.Opens} (hW : (W : Set M.Z).Nonempty) {I : Type} [Fintype I] [DecidableEq I]
    {A A' : Matrix I I Ω} (h0 : A * A' = 1) (h : ∀ z ∈ W, ∀ i j, A i j ∈ M.O z) (h' : ∀ z ∈ W, ∀ i j, A' i j ∈ M.O z) :
    ∃ u : GL I Γ(M.Z, W), (M.res W hW).mapMatrix u.val = A := by
  choose f hf using fun i j => (RatModel.mem_ringOn_iff_exists hW).1 (RatModel.mem_ringOn.2 fun z hz => h z hz i j)
  choose f' hf' using fun i j => (RatModel.mem_ringOn_iff_exists hW).1 (RatModel.mem_ringOn.2 fun z hz => h' z hz i j)
  have e₁ : (M.res W hW).mapMatrix (Matrix.of f) = A := Matrix.ext fun i j => (M.res_apply W hW _).trans (hf i j)
  have e₂ : (M.res W hW).mapMatrix (Matrix.of f') = A' := Matrix.ext fun i j => (M.res_apply W hW _).trans (hf' i j)
  have e : Matrix.of f * Matrix.of f' = 1 := Matrix.map_injective (M.res_injective W hW)
    (show (M.res W hW).mapMatrix _ = (M.res W hW).mapMatrix _ by rw [map_mul, e₁, e₂, map_one, h0])
  exact ⟨⟨Matrix.of f, Matrix.of f', e, mul_eq_one_comm.1 e⟩, e₁⟩

theorem exists_ample (M : RatModel o Ω) {I : Type} (U : I → M.Z.Opens) (u : I → Ω) (hcov : ∀ z, ∃ i, z ∈ U i)
    (haff : ∀ i, IsAffineOpen (U i)) (hne : ∀ i, (U i : Set M.Z).Nonempty) (hu : ∀ i, u i ≠ 0)
    (hreg : ∀ i j, ∀ z ∈ U i, u j / u i ∈ M.O z) (hconv : ∀ i j, ∀ z ∈ U i, u i / u j ∈ M.O z → z ∈ U j) :
    ∃ g : ∀ i j, Γ(M.Z, U i ⊓ U j)ˣ, (LB.mk I U g).IsLB ∧
      (∀ z : M.Z, ∃ (d : ℕ) (s : H0 (LB.mk I U g) d), 1 ≤ d ∧ z ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s)) ∧
      ∀ i j, M.res _ (M.nonempty_inf (hne i) (hne j)) (g i j).val = u j / u i := by
  have n₂ : ∀ i j, ((U i ⊓ U j : M.Z.Opens) : Set M.Z).Nonempty := fun i j => M.nonempty_inf (hne i) (hne j)
  choose g hg using fun i j => exists_unit M (n₂ i j) (div_ne_zero (hu j) (hu i)) (fun z hz => hreg i j z hz.1)
    (fun z hz => by rw [inv_div]; exact hreg j i z hz.2)
  choose f hf using fun q i => (RatModel.mem_ringOn_iff_exists (hne i)).1 (RatModel.mem_ringOn.2 (hreg i q))
  refine ⟨g, ⟨top_unique fun z _ => TopologicalSpace.Opens.mem_iSup.2 (hcov z), fun i => ?_, fun i j k => ?_⟩,
    fun z => ?_, hg⟩
  · refine Units.ext (M.res_injective _ (hne i) ?_)
    refine (M.res_resG _ (hne i) _).trans ((hg i i).trans ?_)
    rw [div_self (hu i), Units.val_one, map_one]
  · have n₃ := M.nonempty_inf (n₂ i j) (hne k)
    refine Units.ext (M.res_injective _ n₃ ?_)
    refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) ((M.res_resG _ n₃ _).trans (hg i j))
      ((M.res_resG _ n₃ _).trans (hg j k))).trans (Eq.trans ?_ ((M.res_resG _ n₃ _).trans (hg i k)).symm))
    have := hu i
    have := hu j
    field_simp
  · obtain ⟨q, hq⟩ := hcov z
    let s : (LB.mk I U g).Sec := ⟨f q, fun i j => M.res_injective _ (n₂ i j) (by
      refine ((M.res_resG _ (n₂ i j) _).trans ((M.res_apply _ _ _).trans (hf q i))).trans (Eq.trans ?_
        ((map_mul _ _ _).trans (congrArg₂ (· * ·) (hg i j)
          ((M.res_resG _ (n₂ i j) _).trans ((M.res_apply _ _ _).trans (hf q j))))).symm)
      have := hu i
      have := hu j
      field_simp)⟩
    have e : nonzeroLocus s = U q := by
      have key : ∀ i, ∀ y ∈ U i, y ∈ M.Z.basicOpen (f q i) ↔ u i / u q ∈ M.O y := fun i y hy => by
        rw [← RatModel.isUnit_valF_iff hy, RatModel.isUnit_O_iff]
        simp only [hf, inv_div, ne_eq, div_ne_zero (hu q) (hu i), not_false_eq_true, true_and]
      refine le_antisymm (iSup_le fun i y hy => ?_) fun y hy => TopologicalSpace.Opens.mem_iSup.2 ⟨q, ?_⟩
      · have hy' := M.Z.basicOpen_le _ hy
        exact hconv i q y hy' ((key i y hy').1 hy)
      · exact (key q y hy).2 (hreg q q y hy)
    obtain ⟨s', e', -⟩ := exists_sec_oneTerm (LB.mk I U g) (K' := Fin 1) (e' := ((1 : ℕ) : ℤ)) rfl (TorsionZero.secOne s)
    rw [TorsionZero.nonzeroLocus_secOne, e] at e'
    exact ⟨1, s', le_rfl, by rw [e']; exact ⟨hq, haff q⟩⟩

theorem mem_span_rows_iff (A : Subalgebra o Ω) {J : Type} [Fintype J] [DecidableEq J] {b : Matrix J J Ω} (hb : b.det ≠ 0)
    (v : J → Ω) : v ∈ Submodule.span A (Set.range b) ↔ ∀ i, Matrix.vecMul v b⁻¹ i ∈ A := by
  have hb' : IsUnit b.det := hb.isUnit
  have key : ∀ c : J → A, ∑ i, c i • b i = Matrix.vecMul (fun i => (c i : Ω)) b := fun c => by
    ext j
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply, Subalgebra.smul_def]
  refine (Submodule.mem_span_range_iff_exists_fun (v := fun i => b i) A).trans ?_
  constructor
  · rintro ⟨c, rfl⟩ i
    rw [key, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hb', Matrix.vecMul_one]
    exact (c i).2
  · intro h
    refine ⟨fun i => ⟨_, h i⟩, ?_⟩
    rw [key]
    show Matrix.vecMul (Matrix.vecMul v b⁻¹) b = v
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hb', Matrix.vecMul_one]

theorem eq_span_dual (A : Subalgebra o Ω) {J : Type} [Fintype J] [DecidableEq J] {b B : Matrix J J Ω} (hb : b.det ≠ 0)
    (hB : B.det ≠ 0) (h : ∀ w, w ∈ Submodule.span A (Set.range B) ↔ ∀ v ∈ Submodule.span A (Set.range b), w ⬝ᵥ v ∈ A) :
    Submodule.span A (Set.range b) = Submodule.span A (Set.range (B⁻¹).transpose) := by
  have hB' : (B⁻¹).transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_nonsing_inv_det _ hB.isUnit).ne_zero
  have e : ((B⁻¹).transpose)⁻¹ = B.transpose := by
    rw [Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ (by rw [Matrix.det_transpose]; exact hB.isUnit)]
  ext v
  rw [mem_span_rows_iff A hB', e, Matrix.vecMul_transpose]
  refine ⟨fun hv i => (h (B i)).1 (Submodule.subset_span ⟨i, rfl⟩) v hv, fun hv => (mem_span_rows_iff A hb v).2 fun i => ?_⟩
  have h₁ : (b⁻¹).transpose i ∈ Submodule.span A (Set.range B) := (h _).2 fun v' hv' => by
    rw [dotProduct_comm]; exact (mem_span_rows_iff A hb v').1 hv' i
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1 h₁
  show v ⬝ᵥ (b⁻¹).transpose i ∈ A
  rw [← hc, dotProduct_sum]
  refine sum_mem fun k _ => ?_
  rw [dotProduct_smul, dotProduct_comm]
  exact A.mul_mem (c k).2 (hv k)

end Basic

section Sections

variable {X Y : Scheme.{0}} (L : LB X) (k : ℤ)

abbrev powAlong (F : Y ⟶ X) : LB Y := LB.LinComb L (K := Fin 1) (fun _ => F) (fun _ => k)

variable {L k} {V : X.Opens}

theorem chart_le {F : Y ⟶ X} (hF : ∀ y, F y ∈ V) (j : Fin 1 → L.ι) :
    (powAlong L k F).U j ≤ F ⁻¹ᵁ (V ⊓ (powAlong L k (𝟙 X)).U j) := fun y hy =>
  ⟨hF y, Set.mem_iInter.2 fun a => Set.mem_iInter.1 hy a⟩

theorem gs_appLE {F : Y ⟶ X} (hF : ∀ y, F y ∈ V) (j : Fin 1 → L.ι) (a : Γ(X, V ⊓ (powAlong L k (𝟙 X)).U j))
    {T : Scheme.{0}} (r : T ⟶ Y) (z : T) (hz : r z ∈ (powAlong L k F).U j) :
    gs r z _ ((F.appLE _ _ (chart_le hF j)).hom a) = gs (r ≫ F) z _ a :=
  (gs_res r z (chart_le hF j) hz ((F.app _).hom a)).trans (gs_pull r F z _ (chart_le hF j hz) a)

def pullOn {σ : ∀ j, Γ(X, V ⊓ (powAlong L k (𝟙 X)).U j)} (hσ : σ ∈ secOn (powAlong L k (𝟙 X)) V) (F : Y ⟶ X)
    (hF : ∀ y, F y ∈ V) : (powAlong L k F).Sec where
  f j := (F.appLE _ _ (chart_le hF j)).hom (σ j)
  compat j j' := fn_ext fun y hy => by
    have m := chart_le hF j hy.1
    have m' := chart_le hF j' hy.2
    refine ((gs_res (𝟙 Y) y _ hy _).trans (gs_appLE hF j _ _ y hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
        (congrArg Units.val (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2)))
        ((gs_res (𝟙 Y) y _ hy _).trans (gs_appLE hF j' _ _ y hy.2)))).symm)
    refine (ThetaUnit.gs_secOn hσ (𝟙 Y ≫ F) y m.1 m.2 m'.2).trans (congrArg (· * _) (congrArg Units.val ?_))
    refine (gm_linComb L _ _ (𝟙 Y ≫ F) y j j' m.2 m'.2).trans ?_
    simp only [Category.comp_id]

theorem valF_pullOn {σ : ∀ j, Γ(X, V ⊓ (powAlong L k (𝟙 X)).U j)} (hσ : σ ∈ secOn (powAlong L k (𝟙 X)) V) (F : Y ⟶ X)
    (hF : ∀ y, F y ∈ V) {K : Type} [Field K] (g : Sp K ⟶ Y) (j : Fin 1 → L.ι) :
    valF g _ ((pullOn hσ F hF).f j) = valF (g ≫ F) _ (σ j) := by
  by_cases h : ⊤ ≤ g ⁻¹ᵁ (powAlong L k F).U j
  · exact Points.valR_appLE g F _ h _
  · have h' : ¬ ⊤ ≤ (g ≫ F) ⁻¹ᵁ (V ⊓ (powAlong L k (𝟙 X)).U j) := fun h' =>
      h fun y hy => Set.mem_iInter.2 fun a => Set.mem_iInter.1 (h' hy).2 a
    have e : valF (g ≫ F) _ (σ j) = 0 := dif_neg h'
    rw [e]
    exact dif_neg h

end Sections

section Family

variable {Z : Scheme.{0}} (G : Over Z) {L : LB G.left} (N : ℕ)

theorem snd_mem {T : Over Z} {W : Z.Opens} (hT : ∀ t, T.hom t ∈ W) (y : (T ⊗ G).left) :
    (snd T G).left y ∈ G.hom ⁻¹ᵁ W :=
  (congrArg (fun q => q y ∈ W) (LN.Frames.snd_hom G T)).mpr (hT _)

def secOver {W : Z.Opens} {σ : ∀ j, Γ(G.left, G.hom ⁻¹ᵁ W ⊓ (powAlong L N (𝟙 _)).U j)}
    (hσ : σ ∈ secOn (powAlong L N (𝟙 _)) (G.hom ⁻¹ᵁ W)) (T : Over Z) (hT : ∀ t, T.hom t ∈ W) :
    LB.Sec (LPow G L (N : ℤ) T) :=
  pullOn hσ (snd T G).left (snd_mem G hT)

theorem lin_secOver {W W₁ W₂ : Z.Opens} {n : ℕ} {σ : ∀ j, Γ(G.left, G.hom ⁻¹ᵁ W₁ ⊓ (powAlong L N (𝟙 _)).U j)}
    (hσ : σ ∈ secOn (powAlong L N (𝟙 _)) (G.hom ⁻¹ᵁ W₁))
    {τ : Fin n → ∀ j, Γ(G.left, G.hom ⁻¹ᵁ W₂ ⊓ (powAlong L N (𝟙 _)).U j)}
    (hτ : ∀ i, τ i ∈ secOn (powAlong L N (𝟙 _)) (G.hom ⁻¹ᵁ W₂)) (h₁ : W ≤ W₁) (h₂ : W ≤ W₂) (m : Fin n → Γ(Z, W))
    (H : ∀ (Y : Scheme.{0}) (r : Y ⟶ G.left) (y : Y) (j), G.hom (r y) ∈ W → r y ∈ (powAlong L N (𝟙 _)).U j →
      gs r y _ (σ j) = ∑ i, gs (r ≫ G.hom) y W (m i) * gs r y _ (τ i j))
    (h : Over.mk W.ι ⟶ Over.mk W₂.ι) (c : Fin n → Γ(W.toScheme, ⊤)) (hc : ∀ i, c i = W.topIso.inv.hom (m i)) :
    LN.Lin G L N h (fun i => secOver G N (hτ i) (Over.mk W₂.ι) (fun t => t.2)) c
      (secOver G N hσ (Over.mk W.ι) (fun t => h₁ t.2)) := by
  obtain rfl : c = fun i => W.topIso.inv.hom (m i) := funext hc
  intro z J hJ
  have hm : ∀ t : W.toScheme, W.ι t ∈ W := fun t => t.2
  have e : W.topIso.inv = W.ι.appLE W ⊤ (fun t _ => hm t) := (Scheme.Opens.ι_appLE W W ⊤ (fun t _ => hm t)).symm
  have mz := hJ.mem (fun _ : Fin 1 => (snd (Over.mk W.ι) G).left) (𝟙 _)
  refine (gs_appLE (snd_mem G (T := Over.mk W.ι) fun t => h₁ t.2) _ _ _ z mz).trans ((H _ _ z _ (snd_mem G (T := Over.mk W.ι) hm z)
    (Set.mem_iInter.2 fun a => Set.mem_iInter.1 mz a)).trans (Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ?_ ?_))
  · show gs ((snd (Over.mk W.ι) G).left ≫ G.hom) z W (m i) = gs _ z ⊤ (W.topIso.inv.hom (m i))
    rw [LN.Frames.snd_hom, ← gs_pull _ (Over.mk W.ι).hom z _ (hm _), e]
    exact (gs_res (fst (Over.mk W.ι) G).left z (show ⊤ ≤ W.ι ⁻¹ᵁ W from fun t _ => hm t) trivial _).symm
  · refine Eq.trans ?_ (gs_appLE (snd_mem G (T := Over.mk W₂.ι) fun t => t.2) _ _ _ z
      (hJ.mem (fun _ : Fin 1 => (snd (Over.mk W₂.ι) G).left) (h ▷ G).left)).symm
    exact congrArg (fun F => gs F z _ (τ i fun _ => J F)) (LN.Frames.whisker_snd G h).symm

theorem indep_secOver {W : Z.Opens} {n : ℕ} {τ : Fin n → ∀ j, Γ(G.left, G.hom ⁻¹ᵁ W ⊓ (powAlong L N (𝟙 _)).U j)}
    (hτ : ∀ i, τ i ∈ secOn (powAlong L N (𝟙 _)) (G.hom ⁻¹ᵁ W)) {K : Type} [Field K] (x : Sp K ⟶ W.toScheme) (c : Fin n → K)
    (H : ∀ (g : Sp K ⟶ (Over.mk W.ι ⊗ G).left) j, g ≫ (fst (Over.mk W.ι) G).left = x →
      ∑ i, c i * valF g _ ((secOver G N (hτ i) (Over.mk W.ι) (fun t => t.2)).f j) = 0)
    (g : Sp K ⟶ G.left) (j) (hg : g ≫ G.hom = x ≫ W.ι) : ∑ i, c i * valF g _ (τ i j) = 0 := by
  let g' : Sp K ⟶ (Over.mk W.ι ⊗ G).left := pullback.lift x g hg.symm
  have e : g' ≫ (snd (Over.mk W.ι) G).left = g := pullback.lift_snd _ _ _
  refine Eq.trans (Finset.sum_congr rfl fun i _ => congrArg (c i * ·) ?_) (H g' j (pullback.lift_fst _ _ _))
  exact ((valF_pullOn (hτ i) _ _ g' j).trans (by rw [e])).symm

end Family

section Generic

theorem eq_of_valF_generic {X : Scheme.{0}} [IsIntegral X] {K : Type} [Field K] (ξ : Sp K ⟶ X)
    (hξ : ∀ w, ξ w = genericPoint X) {U : X.Opens} (hU : ⊤ ≤ ξ ⁻¹ᵁ U) {a b : Γ(X, U)} (h : valF ξ U a = valF ξ U b) :
    a = b := by
  rw [← sub_eq_zero]
  by_contra h0
  have hne : ((X.basicOpen (a - b) : X.Opens) : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun e => h0 ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective e))
  have hu := (Points.le_preimage_basicOpen_iff ξ hU (a - b)).1 (top_le_preimage_of_specializes
    (fun w => by rw [hξ]; exact genericPoint_specializes _) hne.some_mem)
  refine hu.ne_zero ?_
  rw [Points.valF_eq_valR, Points.valF_eq_valR, Points.valR_eq ξ U hU, Points.valR_eq ξ U hU] at h
  rw [Points.valR_eq ξ U hU, map_sub, h, sub_self]

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem exists_eq_spMap_pt (M : RatModel o Ω) {K : Type} [Field K] (x : Sp K ⟶ M.Z)
    (hx : ∀ w, x w = genericPoint M.Z) : ∃ β : Ω →+* K, x = spMap β ≫ M.pt := by
  have hs : ∀ w, x w ⤳ genericPoint M.Z := fun w => hx w ▸ specializes_rfl
  have hm : ∀ a : Ω, a ∈ M.O (genericPoint M.Z) := fun a => by rw [M.O_genericPoint]; trivial
  let β : Ω →+* K := (RatModel.valHomOf x _ hs).comp ((RingHom.id Ω).codRestrict (M.O (genericPoint M.Z)) hm)
  obtain ⟨V, hV, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := genericPoint M.Z) trivial
  have h₁ := top_le_preimage_of_specializes hs hz
  have h₂ := M.top_le_preimage_pt ⟨_, hz⟩
  refine ⟨β, Points.ext_of_valR hV h₁ (Points.le_preimage_comp _ _ h₂ (Points.le_preimage_top _)) fun f => ?_⟩
  rw [Points.valR_spMap_comp β M.pt V h₂]
  exact (RatModel.val_valF ((top_le_preimage_iff _ _).1 h₁) f).symm

variable {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (Z : ZHOut ρ M U₀ EE)

theorem rel_of_genVal (hU₀ : (U₀ : Set M.Z).Nonempty) (k : ℤ) {I : Type} [Fintype I]
    (t : I → LB.Sec (LPow ρ.P.A ρ.P.L k (baseOver (Sp S.R)))) {W W₁ W₂ : M.Z.Opens} (h₁ : W ≤ W₁) (h₂ : W ≤ W₂)
    {n : ℕ} {c : I → Ω} {d : Fin n → I → Ω} {σ} {τ : Fin n → _}
    (hσ : GenVal ρ M U₀ Z.u₀ Z.G Z.φ Z.L.L Z.w k t c (Z.G.hom ⁻¹ᵁ W₁) σ)
    (hτ : ∀ i, GenVal ρ M U₀ Z.u₀ Z.G Z.φ Z.L.L Z.w k t (d i) (Z.G.hom ⁻¹ᵁ W₂) (τ i))
    (m : Fin n → Γ(M.Z, W)) (hm : ∀ l, c l = ∑ i, valF M.pt W (m i) * d i l)
    (Y : Scheme.{0}) (r : Y ⟶ Z.G.left) (y : Y) (j) (hy : Z.G.hom (r y) ∈ W)
    (hj : r y ∈ (powAlong Z.L.L k (𝟙 _)).U j) :
    gs r y _ (σ j) = ∑ i, gs (r ≫ Z.G.hom) y W (m i) * gs r y _ (τ i j) := by
  obtain ⟨jL, rfl⟩ : ∃ jL, j = fun _ => jL := ⟨j 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  have := Z.semi
  have : IsIntegral Z.G.left := isIntegral_left_of_isSemiAbelian Z.G
  let K : Type := Z.G.left.residueField (genericPoint Z.G.left)
  let ξ : Sp K ⟶ Z.G.left := Z.G.left.fromSpecResidueField _
  have hξ : ∀ w, ξ w = genericPoint Z.G.left := fun w => Scheme.fromSpecResidueField_apply _ w
  have hξU : ∀ {U : Z.G.left.Opens} {x}, x ∈ U → ⊤ ≤ ξ ⁻¹ᵁ U := fun {U x} hx =>
    top_le_preimage_of_specializes (fun w => by rw [hξ]; exact genericPoint_specializes _) hx
  have hsurj : Function.Surjective Z.G.hom := fun z => ⟨eSec Z.G z, congrArg (fun q => q z) (Over.w η[Z.G])⟩
  have hgen : ∀ w, (ξ ≫ Z.G.hom) w = genericPoint M.Z := fun w => by
    have := (genericPoint_spec Z.G.left).image Z.G.hom.continuous
    rw [Set.image_univ, hsurj.range_eq, closure_univ, ← hξ w] at this
    exact this.eq (genericPoint_spec M.Z)
  obtain ⟨β, hβ⟩ := exists_eq_spMap_pt M _ hgen
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : Sp K ⟶ U₀.toScheme, x₀ ≫ U₀.ι = ξ ≫ Z.G.hom :=
    ⟨IsOpenImmersion.lift U₀.ι _ (by
      rintro _ ⟨w, rfl⟩
      rw [Scheme.Opens.range_ι, hgen]
      exact (genericPoint_specializes _).mem_open U₀.isOpen hU₀.some_mem), IsOpenImmersion.lift_fac _ _ _⟩
  let g : Sp K ⟶ pullback ρ.P.A.hom Z.u₀ := Z.cart.1.lift ξ x₀ hx₀.symm
  have hg₁ : g ≫ Z.φ = ξ := Z.cart.1.lift_fst _ _ _
  have hg₂ : g ≫ pullback.snd _ _ = x₀ := Z.cart.1.lift_snd _ _ _
  let p : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left :=
    pullback.lift (g ≫ pullback.fst _ _ ≫ ρ.P.A.hom) (g ≫ pullback.fst _ _) (by simp)
  have hp : p ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = g ≫ pullback.fst _ _ := pullback.lift_snd _ _ _
  obtain ⟨jP, hjP⟩ := exists_chart ρ.P.isLB ((g ≫ pullback.fst ρ.P.A.hom Z.u₀) (IsLocalRing.closedPoint K))
  have a₁ : g ≫ pullback.snd _ _ ≫ U₀.ι = spMap β ≫ M.pt := by rw [← Category.assoc, hg₂, hx₀, hβ]
  have a₂ : ⊤ ≤ (g ≫ pullback.fst ρ.P.A.hom Z.u₀) ⁻¹ᵁ ρ.P.L.U jP := (Points.le_preimage_iff _ _).2 hjP
  have a₃ : ⊤ ≤ (g ≫ Z.φ) ⁻¹ᵁ Z.L.L.U jL := by rw [hg₁]; exact hξU (Set.mem_iInter.1 hj 0)
  have e₁ := hσ K β g p jP jL a₁ hp ((top_le_preimage_iff _ _).1 a₂) ((top_le_preimage_iff _ _).1 a₃)
    ((top_le_preimage_iff _ _).1 (by rw [hg₁]; exact hξU (x := r y) (h₁ hy)))
  have e₂ := fun i => hτ i K β g p jP jL a₁ hp ((top_le_preimage_iff _ _).1 a₂) ((top_le_preimage_iff _ _).1 a₃)
    ((top_le_preimage_iff _ _).1 (by rw [hg₁]; exact hξU (x := r y) (h₂ hy)))
  rw [hg₁] at e₁ e₂
  have hw : valF g _ (Z.w.s (fun _ => jP, fun _ => jL)).val ≠ 0 := by
    have hle : ⊤ ≤ g ⁻¹ᵁ (LB.div (ρ.P.L.pull (pullback.fst ρ.P.A.hom Z.u₀)) (Z.L.L.pull Z.φ)).U (fun _ => jP, fun _ => jL) :=
      fun w hw => ⟨mem_pull.2 (a₂ hw), mem_pull.2 (a₃ hw)⟩
    rw [Points.valF_eq_valR, Points.valR_eq g _ hle]
    exact ((Units.isUnit _).map _).ne_zero
  have e₃ : valF ξ _ (σ fun _ => jL) = ∑ i, β (valF M.pt W (m i)) * valF ξ _ (τ i fun _ => jL) := by
    refine mul_left_cancel₀ (zpow_ne_zero k hw) ?_
    rw [← e₁, Finset.mul_sum]
    refine Eq.trans ?_ (Finset.sum_congr rfl fun i _ => (congrArg (β (valF M.pt W (m i)) * ·) (e₂ i)).trans
      (mul_left_comm _ _ _))
    simp only [hm, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, _root_.mul_assoc]
    rw [Finset.sum_comm]
  let O : Z.G.left.Opens := Z.G.hom ⁻¹ᵁ W ⊓ (powAlong Z.L.L k (𝟙 _)).U fun _ => jL
  have hO : r y ∈ O := ⟨hy, hj⟩
  have l₁ : O ≤ Z.G.hom ⁻¹ᵁ W₁ ⊓ (powAlong Z.L.L k (𝟙 _)).U fun _ => jL := fun x hx => ⟨h₁ hx.1, hx.2⟩
  have l₂ : O ≤ Z.G.hom ⁻¹ᵁ W₂ ⊓ (powAlong Z.L.L k (𝟙 _)).U fun _ => jL := fun x hx => ⟨h₂ hx.1, hx.2⟩
  have e₄ : resG _ l₁ (σ fun _ => jL) =
      ∑ i, resG _ (inf_le_left : O ≤ _) ((Z.G.hom.app W).hom (m i)) * resG _ l₂ (τ i fun _ => jL) := by
    refine eq_of_valF_generic ξ hξ (hξU hO) (((Points.valR_res ξ l₁ (hξU hO) _).trans e₃).trans (Eq.symm ?_))
    rw [Points.valF_eq_valR, Points.valR_eq ξ O (hξU hO), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← Points.valR_eq, ← Points.valR_eq]
    refine congrArg₂ (· * ·) ((Points.valR_res ξ _ (hξU hO) _).trans ((Points.valR_comp ξ Z.G.hom W _).symm.trans ?_))
      (Points.valR_res ξ l₂ (hξU hO) _)
    rw [hβ]
    exact Points.valR_spMap_comp β M.pt W (M.top_le_preimage_pt ⟨_, hy⟩) _
  refine (gs_res r y l₁ hO _).symm.trans ((congrArg (gs r y O) e₄).trans ?_)
  rw [gs_eq r y O hO, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← gs_eq r y O hO, gs_mul r y O hO]
  exact congrArg₂ (· * ·) ((gs_res r y _ hO _).trans (gs_pull r Z.G.hom y W hy _)) (gs_res r y l₂ hO _)

end Generic

end GlobalTheory.AmpModel
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AmpModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem exists_ampFrames_of_cover (laws : Laws) {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens}
    {EE : M.Lat S.J} (Z : ZHOut ρ M U₀ EE) (hU₀ : (U₀ : Set M.Z).Nonempty) {I : Type} (U : I → M.Z.Opens) (x : I → S.Gam)
    (b : I → Matrix S.J S.J Ω) (r : ℤ) (u : I → Ω) (hu : ∀ i, u i = S.th (x i) ^ (r + Fintype.card S.J) / (b i).det)
    (hcov : ∀ z, ∃ i, z ∈ U i) (haff : ∀ i, IsAffineOpen (U i)) (hne : ∀ i, (U i : Set M.Z).Nonempty)
    (hb : ∀ i, (b i).det ≠ 0)
    (hx : ∀ i, ∀ z ∈ U i, x i ∈ S.supI M z ∧ EE.E z = Submodule.span (M.O z) (Set.range (b i)))
    (hreg : ∀ i j, ∀ z ∈ U i, u j / u i ∈ M.O z) (hconv : ∀ i j, ∀ z ∈ U i, u i / u j ∈ M.O z → z ∈ U j) :
    ∃ A : LN.AmpFrames Z.G Z.L.L S.N, A.r = r ∧ A.s = 1 := by
  have h0 : ∀ i, S.th (x i) ≠ 0 := fun i => (hx i _ (hne i).some_mem).1.1
  obtain ⟨g, hLB, hamp, hg⟩ := exists_ample M U u hcov haff hne
    (fun i => by rw [hu]; exact div_ne_zero (zpow_ne_zero _ (h0 i)) (hb i)) hreg hconv
  choose σ hσ gσ nσ using fun i => Z.theta (U i) (x i) fun z hz => (hx i z hz).1
  choose τ hτ nτ using fun i => Z.sections (U i) (x i) (b i) (hx i)
  let e : Fin (Fintype.card S.J) ≃ S.J := (Fintype.equivFin S.J).symm
  refine ⟨⟨LB.mk I U g, hLB, hamp, Fintype.card S.J, fun i => secOver Z.G 1 (hσ i) _ (fun t => t.2),
    fun i k => secOver Z.G S.N (hτ i (e k)).1 _ (fun t => t.2), r, 1, fun i j => ?_, fun i V _ _ _ hV χ hχ => ?_⟩, rfl, rfl⟩
  · have n₂ : ((U i ⊓ U j : M.Z.Opens) : Set M.Z).Nonempty := M.nonempty_inf (hne i) (hne j)
    obtain ⟨c, hc⟩ := exists_unit M n₂ (div_ne_zero (h0 j) (h0 i)) (fun z hz => (hx i z hz.1).1.2 _)
      (fun z hz => by rw [inv_div]; exact (hx j z hz.2).1.2 _)
    have reg : ∀ i j, ∀ z ∈ U i, z ∈ U j → ∀ k k',
        (((S.th (x j) / S.th (x i)) • (b i * (b j)⁻¹)).submatrix e e) k k' ∈ M.O z := fun i j z hi hj k k' =>
      (M.O z).mul_mem ((hx i z hi).1.2 _) ((mem_span_rows_iff (M.O z) (hb j) (b i (e k))).1
        ((hx j z hj).2 ▸ (hx i z hi).2 ▸ Submodule.subset_span ⟨e k, rfl⟩) (e k'))
    obtain ⟨m, hm⟩ := exists_GL M n₂ (A := ((S.th (x j) / S.th (x i)) • (b i * (b j)⁻¹)).submatrix e e)
      (A' := ((S.th (x i) / S.th (x j)) • (b j * (b i)⁻¹)).submatrix e e) (by
        rw [Matrix.submatrix_mul_equiv, smul_mul_smul_comm, div_mul_div_cancel₀ (h0 i), div_self (h0 j), one_smul,
          Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (hb j).isUnit, Matrix.mul_nonsing_inv _ (hb i).isUnit,
          Matrix.submatrix_one_equiv])
      (fun z hz => reg i j z hz.1 hz.2) (fun z hz => reg j i z hz.2 hz.1)
    have one : valF M.pt (U i ⊓ U j) 1 = 1 := (M.res_apply _ n₂ 1).symm.trans (map_one _)
    refine ⟨Units.map (U i ⊓ U j).topIso.inv.hom.toMonoidHom c, Matrix.GeneralLinearGroup.map (U i ⊓ U j).topIso.inv.hom m,
      ⟨_, lin_secOver Z.G 1 (hσ i) (fun _ : Fin 1 => hσ i) inf_le_left inf_le_left (fun _ => 1)
          (rel_of_genVal Z hU₀ _ _ inf_le_left inf_le_left (gσ i) (fun _ => gσ i) _ fun _ => by
            rw [Fin.sum_univ_one, one, _root_.one_mul]) _ _ (fun _ => (map_one _).symm),
        lin_secOver Z.G 1 (hσ i) (fun _ : Fin 1 => hσ j) inf_le_left inf_le_right (fun _ => c.val)
          (rel_of_genVal Z hU₀ _ _ inf_le_left inf_le_right (gσ i) (fun _ => gσ j) _ fun _ => by
            rw [Fin.sum_univ_one, ← M.res_apply _ n₂, hc, div_mul_eq_mul_div, mul_inv_cancel₀ (h0 j), one_div])
          _ _ (fun _ => rfl)⟩,
      fun k => ⟨_, lin_secOver Z.G S.N (hτ i (e k)).1 (fun _ : Fin 1 => (hτ i (e k)).1) inf_le_left inf_le_left (fun _ => 1)
          (rel_of_genVal Z hU₀ _ _ inf_le_left inf_le_left (hτ i (e k)).2 (fun _ => (hτ i (e k)).2) _ fun _ => by
            rw [Fin.sum_univ_one, one, _root_.one_mul]) _ _ (fun _ => (map_one _).symm),
        lin_secOver Z.G S.N (hτ i (e k)).1 (fun k' => (hτ j (e k')).1) inf_le_left inf_le_right (fun k' => m.val k k')
          (rel_of_genVal Z hU₀ _ _ inf_le_left inf_le_right (hτ i (e k)).2 (fun k' => (hτ j (e k')).2) _ fun l => ?_)
          _ _ (fun _ => rfl)⟩, ?_⟩
    · have v : ∀ k', valF M.pt (U i ⊓ U j) (m.val k k') = S.th (x j) / S.th (x i) * (b i * (b j)⁻¹) (e k) (e k') :=
        fun k' => (M.res_apply _ n₂ _).symm.trans (congrFun (congrFun hm k) k')
      have w : b i (e k) l = ∑ k', (b i * (b j)⁻¹) (e k) (e k') * b j (e k') l := by
        rw [e.sum_comp (fun a => (b i * (b j)⁻¹) (e k) a * b j a l), ← Matrix.mul_apply,
          Matrix.nonsing_inv_mul_cancel_right _ _ (hb j).isUnit]
      rw [w, Finset.sum_div]
      refine Finset.sum_congr rfl fun k' _ => ?_
      rw [v]
      have := h0 i
      have := h0 j
      field_simp
    · have key : g i j = c ^ r * Matrix.GeneralLinearGroup.det m := by
        refine Units.ext (M.res_injective _ n₂ ((hg i j).trans (Eq.symm ?_)))
        have e₁ : M.res _ n₂ (c ^ r).val = (S.th (x j) / S.th (x i)) ^ r := by
          rw [← hc]
          exact (congrArg Units.val (map_zpow (Units.map (M.res _ n₂).toMonoidHom) c r)).trans (Units.val_zpow_eq_zpow_val _ _)
        rw [Units.val_mul, map_mul, e₁, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det, hm,
          Matrix.det_submatrix_equiv_self, Matrix.det_smul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
          hu, hu, zpow_add₀ (h0 i), zpow_add₀ (h0 j), div_zpow, div_pow, zpow_natCast, zpow_natCast]
        have := h0 i
        have := h0 j
        have := hb i
        have := hb j
        field_simp
      show (U i ⊓ U j).topIso.inv.hom (g i j).val = _
      rw [key, zpow_one, Matrix.GeneralLinearGroup.map_det, ← map_zpow]
      exact map_mul _ _ _
  · let W₀ : M.Z.Opens := ⟨abLocus Z.G, by rw [Z.ab]; exact isOpen_TT_eq_bot S M⟩
    obtain ⟨ha, hk⟩ := Z.pol W₀ subset_rfl
    obtain ⟨A, φ, h₁, h₂, h₃⟩ := exists_polAV Z.G Z.semi S.g Z.dim Z.L Z.sym W₀ ha hk _ hχ
    have hr : ∀ {K : Type} [Field K] (y : Sp K ⟶ (U i).toScheme), Set.range (y ≫ (U i).ι) ⊆ U i := by
      rintro K _ y _ ⟨w, rfl⟩
      exact (y w).2
    refine ⟨GlobalTheory.basisAlong_of_independent_fibres laws M.Z Z.G Z.L.L 1 1 (Over.mk (U i).ι) _ Z.L.isLB Z.semi le_rfl (fun K _ _ y c H => ?_) V hV χ A φ
        h₁ h₂ (one_pow _).symm,
      GlobalTheory.basisAlong_of_independent_fibres laws M.Z Z.G Z.L.L S.N _ (Over.mk (U i).ι) _ Z.L.isLB Z.semi (one_le_two.trans S.N_ge)
        (fun K _ _ y c H => ?_) V hV χ A φ h₁ h₂ (ρ.card.trans (by rw [h₃]))⟩
    · obtain ⟨p, j, hp, hne⟩ := nσ i K _ (hr y)
      have := indep_secOver Z.G 1 (fun _ : Fin 1 => hσ i) y c H p j hp
      rw [Fin.sum_univ_one] at this
      exact funext fun a => by rw [Subsingleton.elim a 0]; exact (mul_eq_zero.1 this).resolve_right hne
    · have := (nτ i K _ (hr y)).2 (c ∘ e.symm) fun p j hp => by
        rw [← e.sum_comp]
        simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
          indep_secOver Z.G S.N (fun k => (hτ i (e k)).1) y c H p j hp
      exact funext fun a => by simpa using congrFun this (e a)

end GlobalTheory.AmpModel

namespace GlobalTheory

open AmpModel

theorem exists_ampFrames_exponents : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (n a : ℕ) (GG : Fin n → S.J → Ω) (Z : ZHOut ρ M U₀ EE), M.IsNm (fun q : S.Gam × (S.J → Fin n) => S.th q.1 * Matrix.det (Matrix.of fun i j => GG (q.2 i) j)) → S.Over₀ M U₀ → (∀ z : M.Z, ∀ x₀ ∈ S.supI M z, ∀ w : S.J → Ω, w ∈ Submodule.span (M.O z) (Set.range fun k j => GG k j / S.th x₀ ^ a) ↔ ∀ v ∈ EE.E z, w ⬝ᵥ v ∈ M.O z) → ∃ r₀ : ℤ, ∀ r : ℤ, r₀ ≤ r → ∃ A : GlobalTheory.LN.AmpFrames Z.G Z.L.L S.N, A.r = r ∧ A.s = 1 := by
  intro laws o Ω _ _ _ _ S ρ M U₀ EE n a GG Z hN hO hdual
  let d : (S.J → Fin n) → Ω := fun k => Matrix.det (Matrix.of fun i j => GG (k i) j)
  let t : S.Gam × (S.J → Fin n) → Ω := fun q => S.th q.1 * d q.2
  refine ⟨1 + ((a : ℤ) - 1) * Fintype.card S.J, fun r hr => ?_⟩
  obtain ⟨e, rfl⟩ := Int.le.dest hr
  choose U haff hU _ using fun i : {q // t q ≠ 0} => hN.2 i.1 i.2
  have mem : ∀ i z, z ∈ U i ↔ M.Div t i.1 z := fun i z => Set.ext_iff.1 (hU i) z
  have h0 : ∀ i : {q // t q ≠ 0}, S.th i.1.1 ≠ 0 := fun i => left_ne_zero_of_mul i.2
  have hd : ∀ i : {q // t q ≠ 0}, d i.1.2 ≠ 0 := fun i => right_ne_zero_of_mul i.2
  have hth : ∀ i, ∀ z ∈ U i, i.1.1 ∈ S.supI M z := fun i z hz => ⟨h0 i, fun y => by
    have := ((mem i z).1 hz).2 (y, i.1.2)
    rwa [mul_div_mul_right _ _ (hd i)] at this⟩
  have hmin : ∀ i, ∀ z ∈ U i, ∀ k, d k / d i.1.2 ∈ M.O z := fun i z hz k => by
    have := ((mem i z).1 hz).2 (i.1.1, k)
    rwa [mul_div_mul_left _ _ (h0 i)] at this
  let B : {q // t q ≠ 0} → (S.J → Fin n) → Matrix S.J S.J Ω := fun i k => Matrix.of fun l j => GG (k l) j / S.th i.1.1 ^ a
  have hB : ∀ i k, (B i k).det = d k / (S.th i.1.1 ^ a) ^ Fintype.card S.J := fun i k => by
    have : B i k = (S.th i.1.1 ^ a)⁻¹ • Matrix.of fun l j => GG (k l) j := by
      ext l j
      simp [B, div_eq_inv_mul]
    rw [this, Matrix.det_smul, inv_pow, div_eq_inv_mul]
  have hB0 : ∀ i, (B i i.1.2).det ≠ 0 := fun i => by
    rw [hB]; exact div_ne_zero (hd i) (pow_ne_zero _ (pow_ne_zero _ (h0 i)))
  have hdet : ∀ i, ((B i i.1.2)⁻¹).transpose.det = (S.th i.1.1 ^ a) ^ Fintype.card S.J / d i.1.2 := fun i => by
    rw [Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hB, inv_div]
  have ratio : ∀ i j : {q // t q ≠ 0}, t j.1 * S.th j.1.1 ^ e / (t i.1 * S.th i.1.1 ^ e) =
      t j.1 / t i.1 * (S.th j.1.1 / S.th i.1.1) ^ e := fun i j => by rw [div_pow, div_mul_div_comm]
  refine exists_ampFrames_of_cover laws Z hO.ne U (fun i => i.1.1) (fun i => ((B i i.1.2)⁻¹).transpose) _
    (fun i => t i.1 * S.th i.1.1 ^ e) (fun i => ?_) (fun z => ?_) haff
    (fun i => ⟨_, (mem i _).2 (RatModel.div_genericPoint i.2)⟩) (fun i => ?_) (fun i z hz => ⟨hth i z hz, ?_⟩)
    (fun i j z hz => ?_) (fun i j z hz h => ?_)
  · have : 1 + ((a : ℤ) - 1) * Fintype.card S.J + e + Fintype.card S.J = ((1 + e + a * Fintype.card S.J : ℕ) : ℤ) := by
      push_cast; ring
    rw [hdet, this, zpow_natCast]
    have := h0 i
    have := hd i
    simp only [t]
    field_simp
    ring
  · obtain ⟨q, hq⟩ := hN.1 z
    exact ⟨⟨q, hq.1⟩, (mem _ z).2 hq⟩
  · rw [hdet]; exact div_ne_zero (pow_ne_zero _ (pow_ne_zero _ (h0 i))) (hd i)
  · obtain ⟨V, b, hzV, hb, hE⟩ := EE.loc z
    rw [hE z hzV]
    refine eq_span_dual (M.O z) hb (hB0 i) fun w => ?_
    rw [← hE z hzV, ← hdual z _ (hth i z hz) w]
    have dd : ∀ k, (Pi.basisFun Ω S.J).det ((fun k j => GG k j / S.th i.1.1 ^ a) ∘ k) = (B i k).det := fun k => by
      rw [Module.Basis.det_apply, ← Matrix.det_transpose]
      congr 1
    have := MaximalMinor.span_range_comp_eq (A := M.O z) (Pi.basisFun Ω S.J) (fun k j => GG k j / S.th i.1.1 ^ a)
      (σ := i.1.2) (mem_nonZeroDivisors_of_ne_zero (by rw [dd]; exact hB0 i)) fun k => by
        rw [dd, dd, hB, hB]
        refine Submodule.mem_span_singleton.2 ⟨⟨_, hmin i z hz k⟩, ?_⟩
        have := hd i
        show d k / d i.1.2 * _ = _
        field_simp
    exact SetLike.ext_iff.1 this w
  · rw [ratio]
    exact (M.O z).mul_mem (((mem i z).1 hz).2 _) (pow_mem ((hth i z hz).2 _) _)
  · rw [ratio] at h
    refine (mem j z).2 ⟨j.2, fun q => ?_⟩
    have := (M.O z).mul_mem ((M.O z).mul_mem (((mem i z).1 hz).2 q) h) (pow_mem ((hth i z hz).2 j.1.1) e)
    convert this using 1
    have := h0 i
    have := h0 j
    have := i.2
    have := j.2
    rw [div_pow, div_pow]
    field_simp

end GlobalTheory
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory

theorem exists_zon_ampFrames_component :
    Out.Laws → Out.Laws2 → GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → GlobalTheory.ZH.ZHGeoSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g n : ℕ), n.Prime → Odd n → ∃ k j₀ : ℕ, ∀ j ≥ j₀, ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R : Subalgebra o Ω) (J : Type) (b : TBase o ((n ^ j) ^ 2)) (u : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap o R))) (t₀ : SAB H (Sp R)) (e : t₀.G ≅ u.A) (v : GlobalTheory.ZM.Ix g ((n ^ j) ^ 2) → R), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) → IsMonHom e.hom → LBIso t₀.PP.L (u.L.pull e.hom.left) → u.HasTh (𝟙 _) v → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i i', x = (v i : Ω) / (v i' : Ω)})) Ω → ∃ C : ZOn (spMap (algebraMap o R)) t₀ (n ^ k), IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L ((n ^ k) ^ 2), A.r = r ∧ A.s = 1 := by
  intro h1 h2 hss hU hT hG E _ _ _ H g n hn ho
  obtain ⟨k, j₀, hk⟩ := GlobalTheory.exists_big_thetaSys_with_action h1 h2 E H g n hn ho
  refine ⟨k, j₀, ?_⟩
  intro j hj o Ω _ _ _ _ R J b u t₀ e v hR hfr he hL hth hfin
  obtain ⟨S, ρ, h, φ, act, hbig, hN, hfin', hcart, hLφ, hact, hadj, hprim⟩ :=
    hk j hj o Ω R J b u t₀ e v hR hfr he hL hth hfin
  have htests : S.HasTests := (GlobalTheory.T.thetaSystem_hasTests_of_real_point hss hU h1 h2 hT o Ω S ρ).1
  obtain ⟨m, a, GG, X, Z, U₀, EE, f, Xab, -, -, hNm, hO, hEE, -, -, -, hgen, hlast⟩ :=
    GlobalTheory.ZH.exists_minor_model o Ω S htests hfin'
  obtain ⟨Y⟩ := hG o Ω S ρ hbig Z U₀ EE hO hEE ⟨m, a, GG, hgen⟩
  have hopen : IsOpen (abLocus Y.G) := by
    rw [Y.ab]
    exact GlobalTheory.isOpen_setOf_TT_eq_bot o Ω S Z _ _ _ hO.div (fun z x₀ hx => (hlast z x₀ hx).2)
  obtain ⟨r₀, hr⟩ := GlobalTheory.exists_ampFrames_exponents h1 o Ω S ρ Z U₀ EE m a GG Y hNm hO hgen
  rw [hN] at hr
  exact GlobalTheory.T.exists_birationalModel_semiAbelian_ampleFrames h1 h2 E H o Ω R t₀ S ρ h φ act Z U₀ EE Y (n ^ k) r₀ hR hfr hO hopen hcart hLφ
    hact hadj hprim hr

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_model_triple_ampleFrames_component : Out.Laws → Out.Laws2 → GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → GlobalTheory.ZH.ZHGeoSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g n : ℕ), n.Prime → Odd n → ∃ k j₀ : ℕ, ∀ j ≥ j₀, ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R : Subalgebra o Ω) (J : Type) (b : TBase o ((n ^ j) ^ 2)) (u : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap o R))) (t₀ : SAB H (Sp R)) (e : t₀.G ≅ u.A) (v : GlobalTheory.ZM.Ix g ((n ^ j) ^ 2) → R), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) → IsMonHom e.hom → LBIso t₀.PP.L (u.L.pull e.hom.left) → u.HasTh (𝟙 _) v → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i i', x = (v i : Ω) / (v i' : Ω)})) Ω → ∃ C : ZOn (spMap (algebraMap o R)) t₀ (n ^ k), IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L ((n ^ k) ^ 2), A.r = r ∧ A.s = 1 := by
  atlas_forward_decl GlobalTheory.exists_zon_ampFrames_component
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem GlobalTheory.nonempty_zOn_thetaFam : Out.Laws → Out.Laws2 → GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → GlobalTheory.ZH.ZHGeoSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n : ℕ), 1 ≤ D.p + D.q → n.Prime → Odd n → ∃ k j₀ : ℕ, ∀ j ≥ j₀, ∀ N' : ℕ, N' = n ^ j → ∀ (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (b : TBase (RZ H n (N' ^ 2)) (N' ^ 2)) (F : ThetaFam n (RZ H n (N' ^ 2)).subtype (PELClass (b := b) D a bas (RZ.rt H n (N' ^ 2)) (RZ H n (N' ^ 2)).subtype)) (τ : SAB H F.MM), IsSympBasis D bas → Subring.closure (Set.range a) = ⊤ → (∃ w w', a w = H.w0 ∧ a w' = H.bar H.w0) → (b.ζ : RZ H n (N' ^ 2)) = RZ.ze H n (N' ^ 2) → IsPEL D a bas (RZ.rt H n (N' ^ 2)) F.univ τ → SmoothOfRelativeDimension D.dim (pullback.snd F.s (spMap (algebraMap (RZ H n (N' ^ 2)) (FractionRing (RZ H n (N' ^ 2)))))) → Nonempty (ZOn F.s τ (n ^ k)) := by
  intro h1 h2 h3 h4 h5 h6 E _ _ _ H D n hpq hn hodd
  exact FamilyModel.nonempty_zOn_of_components GlobalTheory.T.exists_model_triple_ampleFrames_component h1 h2 h3 h4 h5 h6 E H D n hpq hn hodd
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_ampleFramedModel_PELThetaFamily : Out.Laws → Out.Laws2 → GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → GlobalTheory.ZH.ZHGeoSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n : ℕ), 1 ≤ D.p + D.q → n.Prime → Odd n → ∃ k j₀ : ℕ, ∀ j ≥ j₀, ∀ N' : ℕ, N' = n ^ j → ∀ (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (b : TBase (RZ H n (N' ^ 2)) (N' ^ 2)) (F : ThetaFam n (RZ H n (N' ^ 2)).subtype (PELClass (b := b) D a bas (RZ.rt H n (N' ^ 2)) (RZ H n (N' ^ 2)).subtype)) (τ : SAB H F.MM), IsSympBasis D bas → Subring.closure (Set.range a) = ⊤ → (∃ w w', a w = H.w0 ∧ a w' = H.bar H.w0) → (b.ζ : RZ H n (N' ^ 2)) = RZ.ze H n (N' ^ 2) → IsPEL D a bas (RZ.rt H n (N' ^ 2)) F.univ τ → SmoothOfRelativeDimension D.dim (pullback.snd F.s (spMap (algebraMap (RZ H n (N' ^ 2)) (FractionRing (RZ H n (N' ^ 2)))))) → Nonempty (ZOn F.s τ (n ^ k)) := by
  atlas_forward_decl GlobalTheory.nonempty_zOn_thetaFam
end
