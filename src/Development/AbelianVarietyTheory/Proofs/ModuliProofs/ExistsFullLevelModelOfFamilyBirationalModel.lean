import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueLiftOfDensePart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapIdOfCommonGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelObjectDescendsFgSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LocallyQuasiFiniteOfTrivialOnFibres
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusOpenFamilyOverLevelStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliFiniteSurjectiveOverGenericFamily
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOnTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullLevelChangeActsOnUnitaryFamily
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoprimeLevel

section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.FrameCmp

def ev {Y : Scheme.{0}} {R : Type} [CommRing R] (τ : Y ⟶ Sp R) (y : Y) : R →+* Y.presheaf.stalk y :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ τ.appTop ≫ Y.presheaf.germ ⊤ y trivial).hom

theorem ev_eq_gs {Y : Scheme.{0}} {R : Type} [CommRing R] (τ : Y ⟶ Sp R) (y : Y) (a : R) :
    ev τ y a = gs τ y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) := (gs_eq τ y ⊤ trivial _).symm

theorem ev_comp {Y : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (τ : Y ⟶ Sp R') (y : Y) (φ : R →+* R') (a : R) :
    ev (τ ≫ spMap φ) y a = ev τ y (φ a) := by
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [ev, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [e]

structure Probes (Z : Scheme.{0}) where

  I : Type 1

  Y : I → Scheme.{0}

  y : ∀ p, Y p

  β : ∀ p, Y p ⟶ Z

variable {Z : Scheme.{0}} (P : Probes Z)

abbrev Probes.F : Type 1 := ∀ p : P.I, (P.Y p).presheaf.stalk (P.y p)

variable {P} {R R' : Type} [CommRing R] [CommRing R'] {l m n : ℕ}

def Rel (x : Sp R ⟶ Z) (b' : Fin m → P.F) (M : Matrix (Fin m) (Fin n) R) (b : Fin n → P.F) : Prop :=
  ∀ (p : P.I) (τ : P.Y p ⟶ Sp R), τ ≫ x = P.β p → ∀ a, b' a p = ∑ c, ev τ (P.y p) (M a c) * b c p

def Ind (x : Sp R ⟶ Z) (b : Fin n → P.F) : Prop :=
  ∀ c : Fin n → R, (∀ (p : P.I) (τ : P.Y p ⟶ Sp R), τ ≫ x = P.β p → ∑ i, ev τ (P.y p) (c i) * b i p = 0) → c = 0

def Cmp (x : Sp R ⟶ Z) (b : Fin n → P.F) (b' : Fin m → P.F) : Prop :=
  Ind x b ∧ Ind x b' ∧ (∃ M, Rel x b' M b) ∧ ∃ M', Rel x b M' b'

variable {x : Sp R ⟶ Z} {b : Fin n → P.F} {b' : Fin m → P.F} {b'' : Fin l → P.F}

theorem Cmp.symm (h : Cmp x b b') : Cmp x b' b := ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

theorem Rel.map {M} (h : Rel x b' M b) (φ : R →+* R') : Rel (spMap φ ≫ x) b' (M.map φ) b := fun p τ e a => by
  rw [h p (τ ≫ spMap φ) (by rw [Category.assoc, e]) a]
  simp only [ev_comp, Matrix.map_apply]

theorem Rel.mul {M M'} (h' : Rel x b'' M' b') (h : Rel x b' M b) : Rel x b'' (M' * M) b := fun p τ e a => by
  rw [h' p τ e a]
  simp only [h p τ e, Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem Rel.one : Rel x b 1 b := fun p τ _ a => by
  simp [Matrix.one_apply, apply_ite]

theorem Ind.unique (hb : Ind x b) {M M'} (h : Rel x b' M b) (h' : Rel x b' M' b) : M = M' := by
  ext a c
  have := hb (fun c => M a c - M' a c) fun p τ e => by
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib, ← h p τ e a, ← h' p τ e a, sub_self]
  exact sub_eq_zero.1 (congrFun this c)

theorem Ind.of_injective (φ : R →+* R') (hφ : Function.Injective φ) (h : Ind (spMap φ ≫ x) b) : Ind x b := by
  intro c hc
  have := h (fun i => φ (c i)) fun p τ e => by
    rw [← hc p (τ ≫ spMap φ) (by rw [Category.assoc, e])]
    simp only [ev_comp]
  exact funext fun i => hφ ((congrFun this i).trans (map_zero φ).symm)

theorem spMap_comp {R'' : Type} [CommRing R''] (φ : R →+* R') (ψ : R' →+* R'') :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  rw [← Spec.map_comp]; rfl

theorem Cmp.card_eq [Nontrivial R] (h : Cmp x b b') : n = m := by
  obtain ⟨h₁, h₂, ⟨M, hM⟩, M', hM'⟩ := h
  have e := Matrix.indexEquivOfInv (h₂.unique (hM.mul hM') Rel.one) (h₁.unique (hM'.mul hM) Rel.one)
  simpa using (Fintype.card_congr e).symm

theorem cDvr_powerSeries (K : Type) [Field K] [CharZero K] : GlobalTheory.LN.CDvr (PowerSeries K) := by
  refine ⟨inferInstance, ?_, algebraRat.charZero _⟩
  rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance

theorem Cmp.of_powerSeries {K : Type} [Field K] {x : Sp K ⟶ Z} (h : Cmp (spMap (PowerSeries.C (R := K)) ≫ x) b b') :
    Cmp x b b' := by
  have e : spMap (PowerSeries.constantCoeff (R := K)) ≫ spMap (PowerSeries.C (R := K)) ≫ x = x := by
    rw [← Category.assoc, spMap_comp, PowerSeries.constantCoeff_comp_C]
    exact (congrArg (· ≫ x) (Spec.map_id _)).trans (Category.id_comp x)
  obtain ⟨h₁, h₂, ⟨M, hM⟩, M', hM'⟩ := h
  exact ⟨h₁.of_injective _ PowerSeries.C_injective, h₂.of_injective _ PowerSeries.C_injective,
    ⟨_, e ▸ hM.map _⟩, ⟨_, e ▸ hM'.map _⟩⟩

def TraitCmp (x : Sp R ⟶ Z) (b : Fin n → P.F) (b' : Fin m → P.F) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ φ : R →+* W, Function.Injective φ →
    Cmp (spMap φ ≫ x) b b'

theorem TraitCmp.symm (h : TraitCmp x b b') : TraitCmp x b' b := fun W _ _ _ hW φ hφ => (h W hW φ hφ).symm

theorem TraitCmp.field [CharZero R] (h : TraitCmp x b b') {K : Type} [Field K] (ψ : R →+* K) (hψ : Function.Injective ψ) :
    Cmp (spMap ψ ≫ x) b b' := by
  have : CharZero K := charZero_of_injective_ringHom hψ
  refine Cmp.of_powerSeries ?_
  rw [← Category.assoc, spMap_comp]
  exact h _ (cDvr_powerSeries K) _ (PowerSeries.C_injective.comp hψ)

theorem mem_of_completion {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] {W : Type} [CommRing W] [IsDomain W] (ι : V →+* W) (hι : ∀ v, IsUnit (ι v) → IsUnit v)
    (γ : K →+* FractionRing W) (hγ : ∀ v, γ (algebraMap V K v) = algebraMap W _ (ι v)) (d : K) (w : W)
    (h : γ d = algebraMap W _ w) : ∃ v, algebraMap V K v = d := by
  rcases eq_or_ne d 0 with rfl | hd
  · exact ⟨0, map_zero _⟩
  rcases ValuationRing.isInteger_or_isInteger V d with h₁ | ⟨v, hv⟩
  · exact h₁
  have e : ι v * w = 1 := by
    apply IsFractionRing.injective W (FractionRing W)
    rw [map_mul, ← hγ, ← h, ← map_mul, hv, inv_mul_cancel₀ hd, map_one, map_one]
  obtain ⟨u, rfl⟩ := hι v (IsUnit.of_mul_eq_one _ e)
  refine ⟨u⁻¹.val, ?_⟩
  rw [← inv_inv d, ← hv]
  simp

theorem TraitCmp.det_mem [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] {b' : Fin n → P.F}
    (h : TraitCmp x b b') {M} (hM : Rel (spMap (algebraMap R (FractionRing R)) ≫ x) b' M b) :
    ∃ a, algebraMap R (FractionRing R) a = M.det := by
  refine (mem_range_algebraMap_iff_forall_height_eq_one (A := R) (K := FractionRing R) M.det).2 fun p _ hp => ?_
  set V := primeLocalSubalgebra (FractionRing R) p
  have : IsDiscreteValuationRing V := isDiscreteValuationRing_of_height_eq_one p hp V
  let W := AdicCompletion (IsLocalRing.maximalIdeal V) V
  have hVW : Function.Injective (algebraMap V W) := algebraMap_adicCompletion_injective_of_dvr V
  have hRV : Function.Injective (algebraMap R V) := fun a c e =>
    IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val e)
  let φ : R →+* W := (algebraMap V W).comp (algebraMap R V)
  have hφ : Function.Injective φ := hVW.comp hRV
  have hW : GlobalTheory.LN.CDvr W := ⟨inferInstance, inferInstance, charZero_of_injective_ringHom hφ⟩
  have hi : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap V W)) :=
    (IsFractionRing.injective W (FractionRing W)).comp hVW
  let γ : FractionRing R →+* FractionRing W := IsFractionRing.lift (A := V) hi
  have hγ : ∀ v : V, γ (algebraMap V _ v) = algebraMap W _ (algebraMap V W v) := fun v =>
    IsFractionRing.lift_algebraMap hi v
  have e : γ.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ :=
    RingHom.ext fun r => hγ (algebraMap R V r)
  obtain ⟨-, -, ⟨N, hN⟩, -⟩ := h W hW φ hφ
  have h₁ := hM.map γ
  have h₂ := hN.map (algebraMap W (FractionRing W))
  rw [← Category.assoc, spMap_comp] at h₁ h₂
  rw [e] at h₁
  have hMN := (h.field _ ((IsFractionRing.injective W (FractionRing W)).comp hφ)).1.unique h₁ h₂
  obtain ⟨v, hv⟩ := mem_of_completion (K := FractionRing R) (algebraMap V W) (fun v hv => by
      by_contra hn
      have : algebraMap V W v ∈ IsLocalRing.maximalIdeal W := by
        rw [AdicCompletion.maximalIdeal_eq_map]; exact Ideal.mem_map_of_mem _ hn
      exact this hv) γ hγ M.det N.det (by
    rw [RingHom.map_det, RingHom.map_det]; exact congrArg Matrix.det hMN)
  rw [← hv]; exact v.2

theorem TraitCmp.exists_unit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] {b' : Fin n → P.F}
    (h : TraitCmp x b b') : ∃ u : Rˣ, ∀ (K : Type) [Field K] (ψ : R →+* K), Function.Injective ψ →
      ∃ M, Rel (spMap ψ ≫ x) b' M b ∧ M.det = ψ u := by
  have hi := IsFractionRing.injective R (FractionRing R)
  obtain ⟨h₁, -, ⟨M, hM⟩, M', hM'⟩ := h.field _ hi
  obtain ⟨a, ha⟩ := h.det_mem hM
  obtain ⟨a', ha'⟩ := h.symm.det_mem hM'
  have e : a' * a = 1 := hi (by
    rw [map_mul, ha, ha', ← Matrix.det_mul, h₁.unique (hM'.mul hM) Rel.one, Matrix.det_one, map_one])
  refine ⟨⟨a, a', (mul_comm _ _).trans e, e⟩, fun K _ ψ hψ => ⟨M.map (IsFractionRing.lift hψ), ?_, ?_⟩⟩
  · have := hM.map (IsFractionRing.lift hψ)
    rwa [← Category.assoc, spMap_comp, show (IsFractionRing.lift hψ).comp (algebraMap R (FractionRing R)) = ψ from
      RingHom.ext (IsFractionRing.lift_algebraMap hψ)] at this
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, ← ha]
    exact IsFractionRing.lift_algebraMap hψ a

section Base

variable {Z : Scheme.{0}} {P : Probes Z} {n m : ℕ}

def GenPt (η : Z) : Prop := ∀ q : Z, q ⤳ η → q = η

theorem GenPt.mem_genericPoints {η : Z} (h : GenPt η) : η ∈ genericPoints Z := by
  have hC := irreducibleComponent_mem_irreducibleComponents η
  have hg := (isIrreducible_irreducibleComponent (x := η)).isGenericPoint_genericPoint isClosed_irreducibleComponent
  have e := h _ (hg.specializes mem_irreducibleComponent)
  rw [e] at hg
  show closure {η} ∈ irreducibleComponents Z
  rw [hg.def]; exact hC

theorem genPt_iff {R K : Type} [CommRing R] [IsDomain R] [Field K] (x₀ : Sp R ⟶ Z) [IsOpenImmersion x₀] (ψ : R →+* K)
    (pt : Sp K) : GenPt ((spMap ψ ≫ x₀) pt) ↔ Function.Injective ψ := by
  have hk : (spMap ψ pt : PrimeSpectrum R).asIdeal = RingHom.ker ψ := by
    have : (pt : PrimeSpectrum K).asIdeal = ⊥ := congrArg PrimeSpectrum.asIdeal
      (Subsingleton.elim (α := PrimeSpectrum K) pt ⟨⊥, Ideal.isPrime_bot⟩)
    exact congrArg (Ideal.comap ψ) this
  let o : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
  rw [RingHom.injective_iff_ker_eq_bot, ← hk, Scheme.Hom.comp_apply]
  constructor
  · intro h
    have s : o ⤳ spMap ψ pt := (PrimeSpectrum.le_iff_specializes (R := R) o (spMap ψ pt)).1 (show (⊥ : Ideal R) ≤ _ from bot_le)
    have := x₀.isOpenEmbedding.injective (h _ (s.map x₀.continuous))
    exact (congrArg PrimeSpectrum.asIdeal this).symm
  · intro h q hq
    obtain ⟨q', rfl⟩ : q ∈ Set.range x₀ := hq.mem_open x₀.isOpenEmbedding.isOpen_range ⟨_, rfl⟩
    have s := (PrimeSpectrum.le_iff_specializes (R := R) q' (spMap ψ pt)).2 (x₀.isOpenEmbedding.isInducing.specializes_iff.1 hq)
    refine congrArg _ (PrimeSpectrum.ext (R := R) ?_)
    have s' : (q' : PrimeSpectrum R).asIdeal ≤ (spMap ψ pt : PrimeSpectrum R).asIdeal := s
    rw [h] at s' ⊢
    exact le_bot_iff.1 s'

theorem fromSpec_mem {W : Z.Opens} (hW : IsAffineOpen W) (q) : hW.fromSpec q ∈ W :=
  show hW.fromSpec q ∈ (W : Set Z) from hW.range_fromSpec ▸ ⟨q, rfl⟩

theorem gs_fromSpec {W : Z.Opens} (hW : IsAffineOpen W) {Y : Scheme.{0}} (τ : Y ⟶ Sp Γ(Z, W)) (y : Y) (a : Γ(Z, W)) :
    gs (τ ≫ hW.fromSpec) y W a = ev τ y a := by
  rw [← gs_pull τ hW.fromSpec y W (fromSpec_mem hW _), hW.fromSpec_app_self, ev_eq_gs]
  exact gs_res τ y (U := ⊤) (V := hW.fromSpec ⁻¹ᵁ W) le_top (fromSpec_mem hW _) _

theorem exists_spMap {W : Z.Opens} (hW : IsAffineOpen W) {K : Type} [Field K] (x : Sp K ⟶ Z) (pt : Sp K) (h : x pt ∈ W) :
    ∃ ψ : Γ(Z, W) →+* K, spMap ψ ≫ hW.fromSpec = x := by
  have hr : Set.range x ⊆ Set.range hW.fromSpec := by
    rw [hW.range_fromSpec]
    rintro _ ⟨q, rfl⟩
    rwa [Subsingleton.elim (α := PrimeSpectrum K) q pt]
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hW.fromSpec x hr)
  exact ⟨φ.hom, (congrArg (· ≫ hW.fromSpec) hφ).trans (IsOpenImmersion.lift_fac _ _ _)⟩

theorem ev_field_injective {K : Type} [Field K] (pt : Sp K) : Function.Injective (ev (𝟙 (Sp K)) pt) := RingHom.injective _

theorem ev_spMap {R K : Type} [CommRing R] [CommRing K] (ψ : R →+* K) (pt : Sp K) (a : R) :
    ev (spMap ψ) pt a = ev (𝟙 _) pt (ψ a) := by rw [← ev_comp (𝟙 _) pt ψ a, Category.id_comp]

variable [IsLocallyNoetherian Z] (hZ : Geo.Tor.IsNormalScheme Z) (z : Z ⟶ Sp ℤ) [Flat z]
include hZ

theorem exists_domain_chart {V : Z.Opens} {p : Z} (hp : p ∈ V) : ∃ W : Z.Opens, IsAffineOpen W ∧ p ∈ W ∧ W ≤ V ∧
    IsDomain Γ(Z, W) ∧ IsIntegrallyClosed Γ(Z, W) := by
  have := GlobalTheory.IsNormalScheme.of_pred hZ
  have hC := GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents p)
  obtain ⟨W, hW, hpW, hle⟩ := exists_isAffineOpen_mem_and_subset (U := V ⊓ ⟨_, hC⟩) (x := p) ⟨hp, mem_irreducibleComponent⟩
  refine ⟨W, hW, hpW, fun q hq => (hle hq).1, GlobalTheory.IsNormalScheme.isDomain_and_isIntegrallyClosed_of_isIrreducible
    ⟨⟨p, hpW⟩, (isIrreducible_irreducibleComponent (x := p)).2.open_subset W.isOpen fun q hq => (hle hq).2⟩⟩

theorem ext_genPt {V : Z.Opens} {a b : Γ(Z, V)}
    (h : ∀ (K : Type) [Field K] (x : Sp K ⟶ Z) (pt : Sp K), x pt ∈ V → GenPt (x pt) → gs x pt V a = gs x pt V b) : a = b := by
  refine fn_ext fun p hp => ?_
  obtain ⟨W, hW, hpW, hle, _, -⟩ := exists_domain_chart hZ hp
  have hi := IsFractionRing.injective Γ(Z, W) (FractionRing Γ(Z, W))
  let pt : Sp (FractionRing Γ(Z, W)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum _)
  have hm : (spMap (algebraMap Γ(Z, W) (FractionRing Γ(Z, W))) ≫ hW.fromSpec) pt ∈ W := fromSpec_mem hW _
  have v : ∀ c : Γ(Z, V), gs (spMap (algebraMap Γ(Z, W) (FractionRing Γ(Z, W))) ≫ hW.fromSpec) pt V c =
      ev (𝟙 _) pt (algebraMap Γ(Z, W) (FractionRing Γ(Z, W)) ((Z.presheaf.map (homOfLE hle).op).hom c)) := fun c => by
    rw [← gs_res _ pt hle hm, gs_fromSpec, ev_spMap]
  have e := h _ _ pt (hle hm) ((genPt_iff (R := Γ(Z, W)) hW.fromSpec _ pt).2 hi)
  rw [v, v] at e
  rw [← gs_res _ p hle hpW, ← gs_res _ p hle hpW, hi (ev_field_injective pt e)]

theorem unit_ext_genPt {V : Z.Opens} {a b : Γ(Z, V)ˣ}
    (h : ∀ (K : Type) [Field K] (x : Sp K ⟶ Z) (pt : Sp K), x pt ∈ V → GenPt (x pt) → gm x pt V a = gm x pt V b) : a = b :=
  Units.ext (ext_genPt hZ fun K _ x pt hx hg => by rw [gs_unit _ _ _ hx, gs_unit _ _ _ hx, h K x pt hx hg])

omit hZ [IsLocallyNoetherian Z] in
include z in
theorem charZero_chart {W : Z.Opens} (hW : IsAffineOpen W) [Nontrivial Γ(Z, W)] : CharZero Γ(Z, W) := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hW.fromSpec ≫ z)
  have h₁ : φ.hom.Flat := by rw [← Flat.SpecMap_iff, hφ]; infer_instance
  have h₂ : φ.hom = algebraMap ℤ Γ(Z, W) := RingHom.ext_int _ _
  have : Module.Flat ℤ Γ(Z, W) := RingHom.flat_algebraMap_iff.1 (h₂ ▸ h₁)
  refine charZero_of_inj_zero fun k hk => by_contra fun h0 => ?_
  have := (Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(Z, W)) (r := (k : ℤ))
    (mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast h0))).right_eq_zero_of_smul (x := 1) (by simpa using hk)
  exact one_ne_zero this

def GeoCmp (V : Z.Opens) (b : Fin n → P.F) (b' : Fin m → P.F) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ χ : Sp W ⟶ Z, (∀ q, χ q ∈ V) →
    (∀ q, GenPt ((Out.jK W ≫ χ) q)) → Cmp χ b b'

omit hZ [IsLocallyNoetherian Z] in
theorem GeoCmp.traitCmp {V W : Z.Opens} {b : Fin n → P.F} {b' : Fin m → P.F} (h : GeoCmp V b b') (hW : IsAffineOpen W)
    (hle : W ≤ V) [IsDomain Γ(Z, W)] : TraitCmp (R := Γ(Z, W)) hW.fromSpec b b' := fun T _ _ _ hT φ hφ =>
  h T hT _ (fun _ => hle (fromSpec_mem hW _)) fun q => by
    have := (genPt_iff (R := Γ(Z, W)) hW.fromSpec ((algebraMap T (FractionRing T)).comp φ) q).2
      ((IsFractionRing.injective T _).comp hφ)
    rwa [← spMap_comp, Category.assoc] at this

include z

theorem GeoCmp.field {V : Z.Opens} {b : Fin n → P.F} {b' : Fin m → P.F} (h : GeoCmp V b b') {K : Type} [Field K]
    (x : Sp K ⟶ Z) (pt : Sp K) (hx : x pt ∈ V) (hg : GenPt (x pt)) : Cmp x b b' := by
  obtain ⟨W, hW, hpW, hle, _, -⟩ := exists_domain_chart hZ hx
  have := charZero_chart z hW
  obtain ⟨ψ, rfl⟩ := exists_spMap hW x pt hpW
  exact (h.traitCmp hW hle).field ψ ((genPt_iff (R := Γ(Z, W)) hW.fromSpec ψ pt).1 hg)

theorem GeoCmp.card_eq {V : Z.Opens} {b : Fin n → P.F} {b' : Fin m → P.F} (h : GeoCmp V b b') {p : Z} (hp : p ∈ V) :
    n = m := by
  obtain ⟨W, hW, hpW, hle, _, -⟩ := exists_domain_chart hZ hp
  have := charZero_chart z hW
  exact ((h.traitCmp hW hle).field _ (IsFractionRing.injective Γ(Z, W) (FractionRing Γ(Z, W)))).card_eq

theorem GeoCmp.exists_unit {V : Z.Opens} {b b' : Fin n → P.F} (h : GeoCmp V b b') : ∃ u : Γ(Z, V)ˣ,
    ∀ (K : Type) [Field K] (x : Sp K ⟶ Z) (pt : Sp K), x pt ∈ V → GenPt (x pt) →
      ∃ M, Rel x b' M b ∧ ev (𝟙 _) pt M.det = (gm x pt V u).val := by
  have loc : ∀ p : V, ∃ (W : Z.Opens) (u : Γ(Z, W)ˣ), p.1 ∈ W ∧ W ≤ V ∧
      ∀ (K : Type) [Field K] (x : Sp K ⟶ Z) (pt : Sp K), x pt ∈ W → GenPt (x pt) →
        ∃ M, Rel x b' M b ∧ ev (𝟙 _) pt M.det = (gm x pt W u).val := by
    intro p
    obtain ⟨W, hW, hpW, hle, _, _⟩ := exists_domain_chart hZ p.2
    have := charZero_chart z hW
    have : IsNoetherianRing Γ(Z, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
    obtain ⟨u, hu⟩ := (h.traitCmp hW hle).exists_unit
    refine ⟨W, u, hpW, hle, fun K _ x pt hx hg => ?_⟩
    obtain ⟨ψ, rfl⟩ := exists_spMap hW x pt hx
    obtain ⟨M, hM, hd⟩ := hu K ψ ((genPt_iff (R := Γ(Z, W)) hW.fromSpec ψ pt).1 hg)
    refine ⟨M, hM, ?_⟩
    rw [hd, ← gs_unit _ _ _ hx, gs_fromSpec, ev_spMap]
  choose W u hp hle hu using loc
  obtain ⟨s, hs⟩ := glue_unit V W hle (fun p hp' => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨p, hp'⟩, hp _⟩) u
    (fun i j y hy => by
      have e : res (inf_le_left : W i ⊓ W j ≤ W i) (u i) = res inf_le_right (u j) :=
        unit_ext_genPt hZ fun K _ x pt hx hg => by
          obtain ⟨M, hM, hd⟩ := hu i K x pt hx.1 hg
          obtain ⟨M', hM', hd'⟩ := hu j K x pt hx.2 hg
          rw [gm_res _ _ _ hx, gm_res _ _ _ hx]
          refine Units.ext ?_
          rw [← hd, ← hd', (h.field hZ z x pt (hle i hx.1) hg).1.unique hM hM']
      exact (gm_res _ y inf_le_left hy _).symm.trans ((congrArg (gm _ y _) e).trans (gm_res _ y inf_le_right hy _)))
  refine ⟨s, fun K _ x pt hx hg => ?_⟩
  obtain ⟨M, hM, hd⟩ := hu ⟨_, hx⟩ K x pt (hp _) hg
  exact ⟨M, hM, by rw [hd, ← hs, gm_res _ _ _ (hp ⟨_, hx⟩)]⟩

omit [IsLocallyNoetherian Z] hZ z [Flat z] in
theorem det_square {K : Type} [Field K] {x : Sp K ⟶ Z} (pt : Sp K) {b₁ b₁' b₂ b₂' : Fin n → P.F} {N N' M₁ M₂}
    (hN : Rel x b₂ N b₁) (hN' : Rel x b₂' N' b₁') (h₁ : Rel x b₁ M₁ b₁') (h₂ : Rel x b₂ M₂ b₂') (hi : Ind x b₁')
    {u u' m₁ m₂ : ((Sp K).presheaf.stalk pt)ˣ} (e : ev (𝟙 _) pt N.det = u.val) (e' : ev (𝟙 _) pt N'.det = u'.val)
    (e₁ : ev (𝟙 _) pt M₁.det = m₁.val) (e₂ : ev (𝟙 _) pt M₂.det = m₂.val) : u = m₂ * m₁⁻¹ * u' := by
  have h := congrArg (fun M => ev (𝟙 _) pt (Matrix.det M)) (hi.unique (hN.mul h₁) (h₂.mul hN'))
  simp only [Matrix.det_mul, map_mul, e, e', e₁, e₂, ← Units.val_mul, Units.val_inj] at h
  rw [mul_right_comm, ← h, mul_inv_cancel_right]

def Tr {Z₁ : Scheme.{0}} (A : LB Z₁) (f : Z ⟶ Z₁) (r s : ℤ) (θ : A.ι → Fin 1 → P.F) (v : A.ι → Fin n → P.F) : Prop :=
  ∀ (i j : A.ι) (K : Type) [Field K] (x : Sp K ⟶ Z) (pt : Sp K), f (x pt) ∈ A.U i → f (x pt) ∈ A.U j →
    ∃ (C : Matrix (Fin 1) (Fin 1) K) (M : Matrix (Fin n) (Fin n) K) (c d : ((Sp K).presheaf.stalk pt)ˣ),
      Rel x (θ i) C (θ j) ∧ Rel x (v i) M (v j) ∧
      ev (𝟙 _) pt C.det = c.val ∧ ev (𝟙 _) pt M.det = d.val ∧ gm (x ≫ f) pt _ (A.g i j) = c ^ r * d ^ s

theorem lbIso_of_cmp {Z₁ Z₂ : Scheme.{0}} {A₁ : LB Z₁} {A₂ : LB Z₂} (h₁ : A₁.IsLB) (h₂ : A₂.IsLB) (f₁ : Z ⟶ Z₁) (f₂ : Z ⟶ Z₂)
    (r s : ℤ) (θ₁ : A₁.ι → Fin 1 → P.F) (v₁ : A₁.ι → Fin n → P.F) (θ₂ : A₂.ι → Fin 1 → P.F) (v₂ : A₂.ι → Fin m → P.F)
    (hc : ∀ i j (V : Z.Opens), (∀ q ∈ V, f₁ q ∈ A₁.U i) → (∀ q ∈ V, f₂ q ∈ A₂.U j) →
      GeoCmp V (θ₁ i) (θ₂ j) ∧ GeoCmp V (v₁ i) (v₂ j))
    (t₁ : Tr A₁ f₁ r s θ₁ v₁) (t₂ : Tr A₂ f₂ r s θ₂ v₂) : LBIso (A₁.pull f₁) (A₂.pull f₂) := by
  rcases isEmpty_or_nonempty Z with hE | ⟨⟨p₀⟩⟩
  · exact ⟨⟨fun _ => 1⟩, fun i j => unit_ext fun x _ => isEmptyElim x⟩
  obtain rfl : n = m := by
    obtain ⟨i, hi⟩ := exists_chart h₁ (f₁ p₀)
    obtain ⟨j, hj⟩ := exists_chart h₂ (f₂ p₀)
    exact (hc i j (f₁ ⁻¹ᵁ A₁.U i ⊓ f₂ ⁻¹ᵁ A₂.U j) (fun _ h => h.1) (fun _ h => h.2)).2.card_eq hZ z (p := p₀) ⟨hi, hj⟩
  have hc' := fun p : (PUnit → A₂.ι) × (PUnit → A₁.ι) => hc (p.2 PUnit.unit) (p.1 PUnit.unit)
    ((A₂.pull f₂).U p.1 ⊓ (A₁.pull f₁).U p.2) (fun _ h => mem_pull.1 h.2) (fun _ h => mem_pull.1 h.1)
  choose u hu using fun p => (hc' p).1.exists_unit hZ z
  choose d hd using fun p => (hc' p).2.exists_unit hZ z
  refine ⟨⟨fun p => u p ^ r * d p ^ s⟩, fun p q => unit_ext_genPt hZ fun K _ x pt hx hg => ?_⟩
  obtain ⟨C, hC, eC⟩ := hu p K x pt hx.1 hg
  obtain ⟨C', hC', eC'⟩ := hu q K x pt hx.2 hg
  obtain ⟨M, hM, eM⟩ := hd p K x pt hx.1 hg
  obtain ⟨M', hM', eM'⟩ := hd q K x pt hx.2 hg
  obtain ⟨C₁, M₁, c₁, d₁, a₁, a₂, a₃, a₄, a₅⟩ := t₁ _ _ K x pt (mem_pull.1 hx.1.2) (mem_pull.1 hx.2.2)
  obtain ⟨C₂, M₂, c₂, d₂, b₁, b₂, b₃, b₄, b₅⟩ := t₂ _ _ K x pt (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1)
  have e₁ := det_square pt hC hC' a₁ b₁ ((hc' q).1.field hZ z x pt hx.2 hg).1 eC eC' a₃ b₃
  have e₂ := det_square pt hM hM' a₂ b₂ ((hc' q).2.field hZ z x pt hx.2 hg).1 eM eM' a₄ b₄
  refine (gm_res x pt _ hx _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((gm_div (A₁.pull f₁) (A₂.pull f₂) x pt p q hx).trans (congrArg₂ (fun a b => a * b⁻¹)
      ((gm_pull_g A₂ f₂ x pt _ _ hx.1.1 hx.2.1).trans b₅) ((gm_pull_g A₁ f₁ x pt _ _ hx.1.2 hx.2.2).trans a₅)))
    (gm_res x pt _ hx _))).symm)
  have v : ∀ p : (PUnit → A₂.ι) × (PUnit → A₁.ι), gm x pt ((A₂.pull f₂).U p.1 ⊓ (A₁.pull f₁).U p.2) (u p ^ r * d p ^ s) =
      gm x pt _ (u p) ^ r * gm x pt _ (d p) ^ s := fun p => by rw [map_mul, map_zpow, map_zpow]
  refine (v p).trans (Eq.trans ?_ (congrArg _ (v q)).symm)
  rw [e₁, e₂]
  simp only [mul_zpow, mul_inv, inv_zpow]
  ac_rfl

end Base

section Values

open MonoidalCategory CartesianMonoidalCategory ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.LN TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_up_sec {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y ⟶ X')} {φ : K → (Y ⟶ X)}
    (e : ∀ k, φ' k ≫ F = φ k) {ε : K → ℤ} (a : LB.Sec (LB.LinComb L' φ' ε)) : ∃ t : LB.Sec (LB.LinComb L φ ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι), r z ∈ LB.wchart L φ p →
        r z ∈ LB.wchart L' φ' q → gs r z (LB.wchart L φ p) (t.f p) =
          (pw w φ' ε r z p q).val * gs r z (LB.wchart L' φ' q) (a.f q) := by
  obtain rfl : (fun k => φ' k ≫ F) = φ := funext e
  choose u hu using fun p q => exists_pw w φ' ε p q
  have glue : ∀ p : K → L.ι, ∃ s : Γ(Y, LB.wchart L (fun k => φ' k ≫ F) p), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gs r z _ s = (pw w φ' ε r z p q).val * gs r z (LB.wchart L' φ' q) (a.f q) := by
    intro p
    let W : (K → L'.ι) → Y.Opens := fun q => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q
    obtain ⟨v, hv⟩ : ∃ v : ∀ q, Γ(Y, W q), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q, r z ∈ W q →
        gs r z (W q) (v q) = (pw w φ' ε r z p q).val * gs r z (LB.wchart L' φ' q) (a.f q) :=
      ⟨fun q => (u p q).val * (Y.presheaf.map (homOfLE (inf_le_right : W q ≤ LB.wchart L' φ' q)).op).hom (a.f q),
        fun Z r z q hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
          ((gs_unit r z _ hz _).trans (congrArg Units.val (hu p q Z r z hz))) (gs_res r z _ hz _))⟩
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' W (LB.wchart L (fun k => φ' k ≫ F) p)
      (fun q => homOfLE inf_le_left) (fun y hy => by
        choose q hq using fun k => exists_chart hL' (φ' k y)
        exact Opens.mem_iSup.2 ⟨q, hy, Set.mem_iInter.2 hq⟩) v
      (fun q q' => fn_ext (V := W q ⊓ W q') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hv _ _ y q hy.1, hv _ _ y q' hy.2, pw_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.1.1 hy.1.2 hy.2.2,
          trF_self hL _ ε (𝟙 Y) y hy.1.1, sec_trans a (𝟙 Y) y hy.1.2 hy.2.2, one_mul, ← mul_assoc, ← Units.val_mul,
          mul_right_comm, inv_mul_cancel, one_mul])
    refine ⟨s, fun Z r z q h₁ h₂ => ?_⟩
    have hz : r z ∈ W q := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz s).symm.trans ((congrArg (gs r z (W q)) (hs q)).trans (hv Z r z q hz))
  choose s hs using glue
  refine ⟨⟨s, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z p q => hs p Z r z q⟩
  choose q hq using fun k => exists_chart hL' (φ' k y)
  have m : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L' φ' q := Set.mem_iInter.2 hq
  refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
    ((gs_unit (𝟙 Y) y _ hy _).trans (congrArg Units.val (gm_linComb L _ ε (𝟙 Y) y j j' hy.1 hy.2)))
    (gs_res (𝟙 Y) y _ hy _))).symm)
  refine (hs j _ (𝟙 Y) y q hy.1 m).trans (Eq.trans ?_ (congrArg _ (hs j' _ (𝟙 Y) y q hy.2 m)).symm)
  rw [pw_trans hw φ' ε (𝟙 Y) y hy.1 hy.2 m m, trF_self hL' _ ε (𝟙 Y) y m, inv_one, mul_one, Units.val_mul, mul_assoc]
  rfl

theorem gs_comp {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (q : Y ⟶ X) (z : Z) (U : X.Opens) (h : q (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ q) z U a = (r.stalkMap z).hom (gs q (r z) U a) := by
  rw [← gs_pull r q z U h, gs_stalkMap r z _ h, gs_pull (𝟙 _) q (r z) U h, Category.id_comp]

def cv {T : Scheme.{0}} {R : Type} [CommRing R] (x : Sp R ⟶ T) : Γ(T, ⊤) →+* R :=
  (x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom

theorem ev_cv {T Y : Scheme.{0}} {R : Type} [CommRing R] (x : Sp R ⟶ T) (τ : Y ⟶ Sp R) (y : Y) (a : Γ(T, ⊤)) :
    ev τ y (cv x a) = gs (τ ≫ x) y ⊤ a := by
  rw [ev_eq_gs, ← gs_pull τ x y ⊤ trivial]
  exact congrArg (gs τ y ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply _)

variable {Z Z₁ : Scheme.{0}}

structure Pt (G : Over Z) (L : LB G.left) where

  Y : Scheme.{0}

  g : Y ⟶ G.left

  y : Y

  k : L.ι

  hk : g y ∈ L.U k

abbrev probes (G : Over Z) (L : LB G.left) : Probes Z := ⟨Pt G L, Pt.Y, Pt.y, fun p => p.g ≫ G.hom⟩

def sg {G : Over Z} {L : LB G.left} {N : ℕ} {T : Over Z} (s : LB.Sec (LPow G L (N : ℤ) T)) {Y : Scheme.{0}}
    (r : Y ⟶ (T ⊗ G).left) (y : Y) (j : L.ι) : Y.presheaf.stalk y :=
  gs r y (LB.wchart L (fun _ : Fin 1 => (snd T G).left) (fun _ => j)) (s.f (fun _ => j))

theorem exists_lift (G T : Over Z) {Y : Scheme.{0}} (a : Y ⟶ T.left) (c : Y ⟶ G.left) (h : a ≫ T.hom = c ≫ G.hom) :
    ∃ r : Y ⟶ (T ⊗ G).left, r ≫ (fst T G).left = a ∧ r ≫ (snd T G).left = c :=
  ⟨pullback.lift a c h, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem whisker_snd' (G : Over Z) {T T' : Over Z} (h : T' ⟶ T) : (h ▷ G).left ≫ (snd T G).left = (snd T' G).left := by
  rw [← Over.comp_left, whiskerRight_snd]

theorem lin_univ {G : Over Z} {L : LB G.left} (hL : L.IsLB) {N n : ℕ} {T T' : Over Z} {h : T' ⟶ T}
    {b : Fin n → LB.Sec (LPow G L (N : ℤ) T)} {c s} (H : Lin G L N h b c s) {Y : Scheme.{0}} (r : Y ⟶ (T' ⊗ G).left) (y : Y)
    (j : L.ι) (hj : (snd T' G).left (r y) ∈ L.U j) :
    sg s r y j = ∑ i, gs (r ≫ (fst T' G).left) y ⊤ (c i) * sg (b i) (r ≫ (h ▷ G).left) y j := by
  obtain ⟨J, hJ, e⟩ := exists_good L hL (r y) (fun _ : PUnit => (snd T' G).left) (fun _ => j) (fun _ _ _ => rfl) (fun _ => hj)
  have e₁ := H (r y) J hJ
  have m : (h ▷ G).left (r y) ∈ LB.wchart L (fun _ : Fin 1 => (snd T G).left) (fun _ => j) :=
    Set.mem_iInter.2 fun _ => (congrArg (fun q => q (r y) ∈ L.U j) (whisker_snd' G h)).mpr hj
  have m' : r y ∈ LB.wchart L (fun _ : Fin 1 => (snd T' G).left) (fun _ => j) := Set.mem_iInter.2 fun _ => hj
  have e₂ := (sval_of (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) s (𝟙 _) (r y) J (fun _ => j)
    (fun _ => by rw [Category.id_comp]; exact e PUnit.unit)).symm.trans (e₁.trans (Finset.sum_congr rfl fun i _ =>
      congrArg _ (sval_of (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) (b i) (h ▷ G).left (r y) J
        (fun _ => j) (fun _ => by rw [whisker_snd']; exact e PUnit.unit))))
  refine (gs_stalkMap r y _ m' _).trans ((congrArg (r.stalkMap y).hom e₂).trans ((map_sum _ _ _).trans
    (Finset.sum_congr rfl fun i _ => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gs_comp r _ y ⊤ trivial _).symm
      (gs_comp r _ y _ m _).symm))))

def Comes {G : Over Z} {L : LB G.left} (N : ℕ) {W : Type} [CommRing W] (χ : Sp W ⟶ Z) (v : (probes G L).F) : Prop :=
  ∀ (Y' : Scheme.{0}) (ψ : Y' ⟶ G.left) (σ : Y' ⟶ Sp W), σ ≫ χ = ψ ≫ G.hom →
    ∃ a : LB.Sec (LB.LinComb L (fun _ : Fin 1 => ψ) (fun _ => (N : ℤ))), ∀ (p : Pt G L) (r : p.Y ⟶ Y'), r ≫ ψ = p.g →
      gs r p.y (LB.wchart L (fun _ : Fin 1 => ψ) (fun _ => p.k)) (a.f (fun _ => p.k)) = v p

def Bas {G : Over Z} {L : LB G.left} (N : ℕ) {W : Type} [CommRing W] (χ : Sp W ⟶ Z) {n : ℕ} (v : Fin n → (probes G L).F) :
    Prop :=
  Ind χ v ∧ (∀ i, Comes N χ (v i)) ∧ ∀ v', Comes N χ v' → ∃ c : Fin n → W, ∀ (p : Pt G L) (τ : p.Y ⟶ Sp W),
    τ ≫ χ = p.g ≫ G.hom → v' p = ∑ i, ev τ p.y (c i) * v i p

theorem Bas.cmp {G : Over Z} {L : LB G.left} {N : ℕ} {W : Type} [CommRing W] {χ : Sp W ⟶ Z} {n m : ℕ}
    {v : Fin n → (probes G L).F} {v' : Fin m → (probes G L).F} (h : Bas N χ v) (h' : Bas N χ v') : Cmp χ v v' := by
  choose M hM using fun i => h.2.2 _ (h'.2.1 i)
  choose M' hM' using fun i => h'.2.2 _ (h.2.1 i)
  exact ⟨h.1, h'.1, ⟨Matrix.of M, fun p τ e a => hM a p τ e⟩, ⟨Matrix.of M', fun p τ e a => hM' a p τ e⟩⟩

variable {G : Over Z} {G₁ : Over Z₁} {L : LB G.left} {L₁ : LB G₁.left} {f : Z ⟶ Z₁} {φ : G.left ⟶ G₁.left}
  (w : LB.Iso L (L₁.pull φ)) {N n : ℕ}

def IsVal {T : Over Z₁} (s : LB.Sec (LPow G₁ L₁ (N : ℤ) T)) (v : (probes G L).F) : Prop :=
  ∀ (p : Pt G L) (r : p.Y ⟶ (T ⊗ G₁).left) (j : L₁.ι), r ≫ (snd T G₁).left = p.g ≫ φ → φ (p.g p.y) ∈ L₁.U j →
    sg s r p.y j = (gw w p.g p.y j p.k ^ (N : ℤ)).val * v p

variable {w} (hφ : IsPullback φ G.hom G₁.hom f) (hw : PGen w) (hL : L.IsLB) (hL₁ : L₁.IsLB)

include hw hL hL₁ in
theorem exists_isVal {T : Over Z₁} [Mono T.hom] (s : LB.Sec (LPow G₁ L₁ (N : ℤ) T)) : ∃ v, IsVal w s v := by
  classical
  have : Mono (snd T G₁).left := inferInstanceAs (Mono (pullback.snd T.hom G₁.hom))
  choose j₀ hj₀ using fun p : Pt G L => exists_chart hL₁ (φ (p.g p.y))
  have ex : ∀ p : Pt G L, ∃ a : p.Y.presheaf.stalk p.y, ∀ r : p.Y ⟶ (T ⊗ G₁).left, r ≫ (snd T G₁).left = p.g ≫ φ →
      a = (gw w p.g p.y (j₀ p) p.k ^ (N : ℤ))⁻¹.val * sg s r p.y (j₀ p) := fun p => by
    by_cases h : ∃ r : p.Y ⟶ (T ⊗ G₁).left, r ≫ (snd T G₁).left = p.g ≫ φ
    · obtain ⟨r₀, h₀⟩ := h
      exact ⟨(gw w p.g p.y (j₀ p) p.k ^ (N : ℤ))⁻¹.val * sg s r₀ p.y (j₀ p), fun r hr => by
        rw [(cancel_mono _).1 (hr.trans h₀.symm)]⟩
    · exact ⟨0, fun r hr => absurd ⟨r, hr⟩ h⟩
  choose v hv using ex
  refine ⟨v, fun p r j hr hj => ?_⟩
  have m : ∀ i, φ (p.g p.y) ∈ L₁.U i → r p.y ∈ LB.wchart L₁ (fun _ : Fin 1 => (snd T G₁).left) (fun _ => i) := fun i hi =>
    Set.mem_iInter.2 fun _ => (congrArg (fun q => q p.y ∈ L₁.U i) hr).mpr hi
  have t := sec_trans (L := L₁) (φ := fun _ : Fin 1 => (snd T G₁).left) (ε := fun _ => (N : ℤ)) s r p.y (m j hj) (m _ (hj₀ p))
  have g := hw _ p.g p.y j (j₀ p) p.k p.k hj (hj₀ p) p.hk p.hk
  rw [gm_self hL p.g p.y p.hk, inv_one, mul_one] at g
  refine t.trans ?_
  rw [hv p r hr, g, Geo.Tor.trF, Fin.prod_univ_one, hr, mul_zpow, Units.val_mul, mul_assoc, Units.mul_inv_cancel_left]
  rfl

include hφ hL₁ in
theorem rel_of_lin {T₁ T₂ T' : Over Z₁} {h₁ : T' ⟶ T₁} {h₂ : T' ⟶ T₂} {m : ℕ}
    {b₁ : Fin m → LB.Sec (LPow G₁ L₁ (N : ℤ) T₁)} {b₂ : Fin n → LB.Sec (LPow G₁ L₁ (N : ℤ) T₂)}
    (M : Matrix (Fin m) (Fin n) Γ(T'.left, ⊤))
    (H : ∀ k, ∃ t, Lin G₁ L₁ N h₁ (fun _ : Fin 1 => b₁ k) (fun _ => 1) t ∧ Lin G₁ L₁ N h₂ b₂ (fun k' => M k k') t)
    {v₁ : Fin m → (probes G L).F} {v₂ : Fin n → (probes G L).F} (hv₁ : ∀ k, IsVal w (b₁ k) (v₁ k))
    (hv₂ : ∀ k, IsVal w (b₂ k) (v₂ k)) {R : Type} [CommRing R] (x : Sp R ⟶ Z) (x' : Sp R ⟶ T'.left)
    (hx : x' ≫ T'.hom = x ≫ f) : Rel x v₁ (M.map (cv x')) v₂ := by
  intro (p : Pt G L) (τ : p.Y ⟶ Sp R) (e : τ ≫ x = p.g ≫ G.hom) k
  obtain ⟨r, r₁, r₂⟩ := exists_lift G₁ T' (τ ≫ x') (p.g ≫ φ) (by
    rw [Category.assoc, hx, ← Category.assoc, e, Category.assoc, Category.assoc, hφ.w])
  obtain ⟨j, hj⟩ := exists_chart hL₁ (φ (p.g p.y))
  have hj' : (snd T' G₁).left (r p.y) ∈ L₁.U j := (congrArg (fun q => q p.y ∈ L₁.U j) r₂).mpr hj
  obtain ⟨t, t₁, t₂⟩ := H k
  have E := (lin_univ hL₁ t₁ r p.y j hj').symm.trans (lin_univ hL₁ t₂ r p.y j hj')
  rw [Fin.sum_univ_one, gs_eq _ _ ⊤ trivial, map_one, map_one, one_mul,
    hv₁ k p _ j (by rw [Category.assoc, whisker_snd', r₂]) hj] at E
  refine (Units.mul_right_inj (gw w p.g p.y j p.k ^ (N : ℤ))).1 (E.trans ((Finset.sum_congr rfl fun i _ => ?_).trans
    (Finset.mul_sum _ _ _).symm))
  rw [hv₂ i p _ j (by rw [Category.assoc, whisker_snd', r₂]) hj, r₁, ← ev_cv, mul_left_comm]
  rfl

include hφ hw hL hL₁ in
theorem comes_of_isVal {T : Over Z₁} {s : LB.Sec (LPow G₁ L₁ (N : ℤ) T)} {v : (probes G L).F} (hv : IsVal w s v)
    {W : Type} [CommRing W] (χ : Sp W ⟶ Z) (χ₁ : Sp W ⟶ T.left) (hχ : χ₁ ≫ T.hom = χ ≫ f) : Comes N χ v := by
  intro Y' ψ σ e
  obtain ⟨h, -, h₂⟩ := exists_lift G₁ T (σ ≫ χ₁) (ψ ≫ φ) (by
    rw [Category.assoc, hχ, ← Category.assoc, e, Category.assoc, Category.assoc, hφ.w])
  obtain ⟨a, ha⟩ := GlobalTheory.SecPull.exists_down_sec hw hL₁ hL (fun _ : Fin 1 => ψ) (fun _ => (snd T G₁).left)
    (fun _ => (N : ℤ)) h (fun _ => h₂.symm) s
  refine ⟨a, fun p r hr => ?_⟩
  obtain ⟨j, hj⟩ := exists_chart hL₁ (φ (p.g p.y))
  have e₁ := hv p (r ≫ h) j (by rw [Category.assoc, h₂, ← Category.assoc, hr]) hj
  rw [ha _ r p.y (fun _ => j) (fun _ => p.k)
    (Set.mem_iInter.2 fun _ => (congrArg (fun q => φ (q p.y) ∈ L₁.U j) hr).mpr hj)
    (Set.mem_iInter.2 fun _ => (congrArg (fun q => q p.y ∈ L.U p.k) hr).mpr p.hk), pw, Fin.prod_univ_one, hr]
  exact (congrArg _ e₁).trans (Units.inv_mul_cancel_left _ _)

include hφ hw hL hL₁ in
theorem bas_of_basisAlong {T : Over Z₁} {b : Fin n → LB.Sec (LPow G₁ L₁ (N : ℤ) T)} {v : Fin n → (probes G L).F}
    (hv : ∀ i, IsVal w (b i) (v i)) {W : Type} [CommRing W] (χ : Sp W ⟶ Z) {χ' : Sp W ⟶ Z₁} (hχ : χ' = χ ≫ f)
    (h : Over.mk χ' ⟶ T) (hb : BasisAlong G₁ L₁ N h b) : Bas N χ v := by
  have hs : (snd (Over.mk χ') G₁).left ≫ G₁.hom = ((fst (Over.mk χ') G₁).left ≫ χ) ≫ f := by
    rw [Category.assoc, ← hχ]; exact Frames.snd_hom G₁ (Over.mk χ')
  obtain ⟨ψ, ψ₁, ψ₂⟩ : ∃ ψ : (Over.mk χ' ⊗ G₁).left ⟶ G.left, ψ ≫ φ = (snd (Over.mk χ') G₁).left ∧
      ψ ≫ G.hom = (fst (Over.mk χ') G₁).left ≫ χ := ⟨hφ.lift _ _ hs, hφ.lift_fst _ _ _, hφ.lift_snd _ _ _⟩
  refine ⟨fun c hc => ?_, fun i => comes_of_isVal hφ hw hL hL₁ (hv i) χ h.left ((Over.w h).trans hχ), fun v' hv' => ?_⟩
  · let o : LB.Sec (LPow G₁ L₁ (N : ℤ) (Over.mk χ')) := ⟨fun _ => 0, fun _ _ => by rw [map_zero, map_zero, mul_zero]⟩
    have ho : ∀ z J, Good L₁ z J → sval (L := L₁) (φ := fun _ : Fin 1 => (snd (Over.mk χ') G₁).left)
        (ε := fun _ => (N : ℤ)) o (𝟙 _) z J = 0 := fun z J hJ =>
      (gs_eq _ _ _ (hJ.mem (fun _ : Fin 1 => (snd (Over.mk χ') G₁).left) (𝟙 _)) _).trans
        ((congrArg _ (map_zero _)).trans (map_zero _))
    have H₀ : Lin G₁ L₁ N h b 0 o := fun z J hJ => (ho z J hJ).trans (Finset.sum_eq_zero fun i _ => by
      rw [Pi.zero_apply, gs_eq _ _ ⊤ trivial, map_zero, map_zero, zero_mul]).symm
    have H₁ : Lin G₁ L₁ N h b (fun i => (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom (c i)) o := fun z J hJ => by
      obtain ⟨k, hk⟩ := exists_chart hL (ψ z)
      have e : (h ▷ G₁).left ≫ (snd T G₁).left = ψ ≫ φ := (whisker_snd' G₁ h).trans ψ₁.symm
      have hj : φ (ψ z) ∈ L₁.U (J ((h ▷ G₁).left ≫ (snd T G₁).left)) :=
        (congrArg (fun q => q z ∈ L₁.U (J ((h ▷ G₁).left ≫ (snd T G₁).left))) e).mp (hJ _)
      have E := congrArg ((gw w ψ z (J ((h ▷ G₁).left ≫ (snd T G₁).left)) k ^ (N : ℤ)).val * ·)
        (hc (⟨_, ψ, z, k, hk⟩ : Pt G L) (fst (Over.mk χ') G₁).left ψ₂.symm)
      refine (ho z J hJ).trans ((mul_zero _).symm.trans (E.symm.trans ((Finset.mul_sum _ _ _).trans
        (Finset.sum_congr rfl fun i _ => (mul_left_comm _ _ _).trans (congrArg₂ (· * ·) (ev_eq_gs _ _ _)
          (hv i (⟨_, ψ, z, k, hk⟩ : Pt G L) (h ▷ G₁).left _ e hj).symm)))))
    have E := (hb o).unique H₁ H₀
    exact funext fun i => (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).inv).1
      ((congrFun E i).trans (map_zero _).symm)
  · obtain ⟨a, ha⟩ := hv' _ ψ (fst (Over.mk χ') G₁).left ψ₂.symm
    obtain ⟨t, ht⟩ := exists_up_sec hw hL₁ hL (φ := fun _ : Fin 1 => (snd (Over.mk χ') G₁).left) (fun _ => ψ₁) a
    obtain ⟨c, hc, -⟩ := hb t
    refine ⟨fun i => cv (R := W) (𝟙 (Sp W)) (c i), fun p τ e => ?_⟩
    obtain ⟨r, r₁, r₂⟩ := exists_lift G₁ (Over.mk χ') τ (p.g ≫ φ) (by
      show τ ≫ χ' = _
      rw [hχ, ← Category.assoc, e, Category.assoc, Category.assoc, hφ.w])
    have hr : r ≫ ψ = p.g := hφ.hom_ext (by rw [Category.assoc, ψ₁, r₂])
      (by rw [Category.assoc, ψ₂, ← Category.assoc, r₁, e])
    obtain ⟨j, hj⟩ := exists_chart hL₁ (φ (p.g p.y))
    have hj' : (snd (Over.mk χ') G₁).left (r p.y) ∈ L₁.U j := (congrArg (fun q => q p.y ∈ L₁.U j) r₂).mpr hj
    have E := ht _ r p.y (fun _ => j) (fun _ => p.k) (Set.mem_iInter.2 fun _ => hj')
      (Set.mem_iInter.2 fun _ => (congrArg (fun q => q p.y ∈ L.U p.k) hr).mpr p.hk)
    rw [ha p r hr, pw, Fin.prod_univ_one, hr] at E
    refine (Units.mul_right_inj (gw w p.g p.y j p.k ^ (N : ℤ))).1 (E.symm.trans ((lin_univ hL₁ hc r p.y j hj').trans
      ((Finset.sum_congr rfl fun i _ => ?_).trans (Finset.mul_sum _ _ _).symm)))
    rw [hv i p _ j (by rw [Category.assoc, whisker_snd', r₂]) hj, r₁, ev_cv, Category.comp_id, mul_left_comm]

theorem exists_lift_open {Y X : Scheme.{0}} (x : Y ⟶ X) (U : X.Opens) (h : ∀ q, x q ∈ U) : ∃ x' : Y ⟶ U.toScheme, x' ≫ U.ι = x :=
  ⟨IsOpenImmersion.lift U.ι x (by rintro _ ⟨q, rfl⟩; exact ⟨⟨_, h q⟩, rfl⟩), IsOpenImmersion.lift_fac _ _ _⟩

theorem gs_topIso {Y X : Scheme.{0}} (U : X.Opens) (x : Y ⟶ U.toScheme) (y : Y) (a : Γ(X, U)) :
    gs x y ⊤ (U.topIso.inv.hom a) = gs (x ≫ U.ι) y U a := by
  have hm : ∀ t : U.toScheme, U.ι t ∈ U := fun t => t.2
  rw [← gs_pull x U.ι y U (hm _)]
  refine Eq.trans ?_ (gs_res x y (show ⊤ ≤ U.ι ⁻¹ᵁ U from fun t _ => hm t) trivial _)
  refine congrArg (gs _ y ⊤) ?_
  have e : U.topIso.inv = U.ι.appLE U ⊤ (fun t _ => hm t) := (Scheme.Opens.ι_appLE U U ⊤ (fun t _ => hm t)).symm
  rw [e]; rfl

include hφ hw hL hL₁ in
theorem exists_values (A : AmpFrames G₁ L₁ N) (hab : ∀ η : Z, GenPt η → f η ∈ abLocus G₁) :
    ∃ (θ : A.A.ι → Fin 1 → (probes G L).F) (v : A.A.ι → Fin A.n → (probes G L).F),
      (∀ (i : A.A.ι) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ χ : Sp W ⟶ Z,
        (∀ q, f (χ q) ∈ A.A.U i) → (∀ q, GenPt ((jK W ≫ χ) q)) → Bas 1 χ (θ i) ∧ Bas N χ (v i)) ∧
      Tr A.A f A.r A.s θ v := by
  have mo : ∀ i, Mono (Over.mk (A.A.U i).ι).hom := fun i => inferInstanceAs (Mono (A.A.U i).ι)
  choose θ hθ using fun i => exists_isVal hw hL hL₁ (A.th i)
  choose v hv using fun i k => exists_isVal hw hL hL₁ (A.b i k)
  refine ⟨fun i _ => θ i, v, fun i W _ _ _ hW χ hχ hg => ?_, fun i j K _ x pt hi hj => ?_⟩
  · obtain ⟨χ₁, e⟩ := exists_lift_open (χ ≫ f) (A.A.U i) hχ
    obtain ⟨t₁, t₂⟩ := A.trait i W hW χ₁ (by
      rw [e]
      rintro _ ⟨q, rfl⟩
      exact hab _ (hg q))
    exact ⟨bas_of_basisAlong hφ hw hL hL₁ (fun _ => hθ i) χ e _ t₁, bas_of_basisAlong hφ hw hL hL₁ (hv i) χ e _ t₂⟩
  · obtain ⟨x', e⟩ := exists_lift_open (x ≫ f) (A.A.U i ⊓ A.A.U j) fun q => by
      rw [Subsingleton.elim (α := PrimeSpectrum K) q pt]; exact ⟨hi, hj⟩
    obtain ⟨c, M, t₁, t₂, t₃⟩ := A.trans i j
    let ρ : Γ((A.A.U i ⊓ A.A.U j).toScheme, ⊤) →+* (Sp K).presheaf.stalk pt := (ev (𝟙 (Sp K)) pt).comp (cv x')
    have R₁ := rel_of_lin (T' := Over.mk (A.A.U i ⊓ A.A.U j).ι) hφ hL₁ (b₁ := fun _ : Fin 1 => A.th i)
      (b₂ := fun _ : Fin 1 => A.th j) (Matrix.of fun _ _ => c.val) (fun _ => t₁) (fun _ => hθ i) (fun _ => hθ j) x x' e
    have R₂ := rel_of_lin (T' := Over.mk (A.A.U i ⊓ A.A.U j).ι) hφ hL₁ M.val t₂ (hv i) (hv j) x x' e
    refine ⟨_, _, Units.map ρ.toMonoidHom c, Units.map ρ.toMonoidHom (Matrix.GeneralLinearGroup.det M), R₁, R₂,
      congrArg (ev (𝟙 (Sp K)) pt) (Matrix.det_fin_one _), congrArg (ev (𝟙 (Sp K)) pt) ((cv x').map_det M.val).symm,
      Units.ext ?_⟩
    rw [← map_zpow, ← map_zpow, ← map_mul, ← gs_unit (x ≫ f) pt (A.A.U i ⊓ A.A.U j) ⟨hi, hj⟩, ← e, ← gs_topIso, t₃]
    exact ((ev_cv x' (𝟙 _) pt _).trans (by rw [Category.id_comp])).symm

end Values

section Main

open MonoidalCategory CartesianMonoidalCategory MonObj NumberField

theorem lbIso_of_ampFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z Z₁ Z₂ : Scheme.{0}) [IsLocallyNoetherian Z] (z : Z ⟶ Sp ℤ) (t : SAB H Z) (t₁ : SAB H Z₁) (t₂ : SAB H Z₂) (f₁ : Z ⟶ Z₁) (f₂ : Z ⟶ Z₂) (_ : SABMap t t₁ f₁) (_ : SABMap t t₂ f₂) (N : ℕ) (A₁ : GlobalTheory.LN.AmpFrames t₁.G t₁.PP.L N) (A₂ : GlobalTheory.LN.AmpFrames t₂.G t₂.PP.L N), Geo.Tor.IsNormalScheme Z → Flat z → genericPoints Z ⊆ abLocus t.G → A₁.r = A₂.r → A₁.s = A₂.s → LBIso (A₁.A.pull f₁) (A₂.A.pull f₂) := by
  intro E _ _ _ H Z Z₁ Z₂ _ z t t₁ t₂ f₁ f₂ m₁ m₂ N A₁ A₂ hZ hz hab hr hs
  obtain ⟨w₁, hw₁, -⟩ := (isPullCubical_iff m₁.cm t₁.cub t.cub).1 m₁.lin
  obtain ⟨w₂, hw₂, -⟩ := (isPullCubical_iff m₂.cm t₂.cub t.cub).1 m₂.lin
  obtain ⟨θ₁, v₁, b₁, r₁⟩ := exists_values m₁.cart.1 hw₁ t.PP.isLB t₁.PP.isLB A₁ fun q hq =>
    (abLocus_pullback abLocusOne t₁.semi m₁.cart.1 q).2 (hab hq.mem_genericPoints)
  obtain ⟨θ₂, v₂, b₂, r₂⟩ := exists_values m₂.cart.1 hw₂ t.PP.isLB t₂.PP.isLB A₂ fun q hq =>
    (abLocus_pullback abLocusOne t₂.semi m₂.cart.1 q).2 (hab hq.mem_genericPoints)
  rw [← hr, ← hs] at r₂
  refine lbIso_of_cmp hZ z A₁.isLB A₂.isLB f₁ f₂ A₁.r A₁.s θ₁ v₁ θ₂ v₂ (fun i j V h₁ h₂ => ?_) r₁ r₂
  exact ⟨fun W _ _ _ hW χ hχ hg => (b₁ i W hW χ (fun q => h₁ _ (hχ q)) hg).1.cmp (b₂ j W hW χ (fun q => h₂ _ (hχ q)) hg).1,
    fun W _ _ _ hW χ hχ hg => (b₁ i W hW χ (fun q => h₁ _ (hχ q)) hg).2.cmp (b₂ j W hW χ (fun q => h₂ _ (hχ q)) hg).2⟩

end Main

end GlobalTheory.FrameCmp
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_of_ampleDeterminantFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z Z₁ Z₂ : Scheme.{0}) [IsLocallyNoetherian Z] (z : Z ⟶ Sp ℤ) (t : SAB H Z) (t₁ : SAB H Z₁) (t₂ : SAB H Z₂) (f₁ : Z ⟶ Z₁) (f₂ : Z ⟶ Z₂) (_ : SABMap t t₁ f₁) (_ : SABMap t t₂ f₂) (N : ℕ) (A₁ : GlobalTheory.LN.AmpFrames t₁.G t₁.PP.L N) (A₂ : GlobalTheory.LN.AmpFrames t₂.G t₂.PP.L N), IsNormalScheme Z → Flat z → genericPoints Z ⊆ abLocus t.G → A₁.r = A₂.r → A₁.s = A₂.s → LBIso (A₁.A.pull f₁) (A₂.A.pull f₂) := by
  first | exact @GlobalTheory.FrameCmp.lbIso_of_ampFrames | exact GlobalTheory.FrameCmp.lbIso_of_ampFrames | (intros; apply GlobalTheory.FrameCmp.lbIso_of_ampFrames <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.AmpUniq

theorem isNoetherianRing_of_isInducing {A B : Type*} [CommRing A] [CommRing B] [IsNoetherianRing A]
    (f : A →+* B) (hi : Topology.IsInducing (PrimeSpectrum.comap f)) (hf : f.SurjectiveOnStalks) :
    IsNoetherianRing B := by
  refine (isNoetherianRing_iff_ideal_fg B).2 fun J => ?_
  have e : (J.comap f).map f = J := by
    refine le_antisymm Ideal.map_comap_le fun b hb => ?_
    by_contra hn
    have hne : ((J.comap f).map f).colon {b} ≠ ⊤ := fun h => hn (by
      have h1 : (1 : B) ∈ ((J.comap f).map f).colon {b} := h ▸ Submodule.mem_top
      simpa using Submodule.mem_colon_singleton.1 h1)
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨x, r, c, hc, hr, hx⟩ := RingHom.surjectiveOnStalks_iff_forall_maximal'.1 hf P hP b
    let p : PrimeSpectrum B := ⟨P, hP.isPrime⟩
    obtain ⟨U, hU, hUc⟩ := hi.isOpen_iff.1 (PrimeSpectrum.basicOpen c).isOpen
    have hpU : PrimeSpectrum.comap f p ∈ U := by
      have : p ∈ PrimeSpectrum.comap f ⁻¹' U := hUc ▸ hc
      exact this
    obtain ⟨_, ⟨a, rfl⟩, ha, haU⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpU hU
    have hac : PrimeSpectrum.basicOpen (f a) ≤ PrimeSpectrum.basicOpen c := fun q hq => by
      have : q ∈ PrimeSpectrum.comap f ⁻¹' U := haU hq
      exact hUc.subset this
    obtain ⟨n, hn⟩ := (PrimeSpectrum.basicOpen_le_basicOpen_iff _ _).1 hac
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hn
    have key : f (a ^ n * r) * b = f (a ^ n * x) := by
      rw [map_mul, map_mul, map_pow, ← hd]
      linear_combination d * hx
    have hmem : f (a ^ n * r) ∈ P := hle (Submodule.mem_colon_singleton.2 (by
      rw [smul_eq_mul, key]
      exact Ideal.mem_map_of_mem f (Ideal.mem_comap.2 (key ▸ J.mul_mem_left _ hb))))
    rw [map_mul, map_pow] at hmem
    rcases hP.isPrime.mem_or_mem hmem with h | h
    · exact ha (hP.isPrime.mem_of_pow_mem n h)
    · exact hr h
  rw [← e]
  exact Ideal.FG.map (IsNoetherian.noetherian _) f

theorem isLocallyNoetherian_of_isPreimmersion {W Z : Scheme.{0}} (j : W ⟶ Z) [IsPreimmersion j]
    [IsLocallyNoetherian Z] : IsLocallyNoetherian W := by
  have H (w : W) : ∃ V : W.affineOpens, w ∈ V.1 ∧ IsNoetherianRing Γ(W, V) := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hw, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (j w)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hwV, hVU⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
      (show w ∈ (j ⁻¹ᵁ U : Set W) from hw) (j ⁻¹ᵁ U).isOpen
    have hU' : IsAffineOpen U := hU
    have hV' : IsAffineOpen V := hV
    have e := IsAffineOpen.SpecMap_appLE_fromSpec j hU' hV' hVU
    have : IsPreimmersion (Spec.map (j.appLE U V hVU) ≫ hU'.fromSpec) := by
      rw [e]; infer_instance
    have h := (IsPreimmersion.SpecMap_iff _).1 (IsPreimmersion.of_comp (Spec.map (j.appLE U V hVU)) hU'.fromSpec)
    have : IsNoetherianRing Γ(Z, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    exact ⟨⟨V, hV⟩, hwV, isNoetherianRing_of_isInducing _ h.1.isInducing h.2⟩
  choose V hV hN using H
  exact isLocallyNoetherian_of_affine_cover (S := V)
    (top_le_iff.1 fun w _ => TopologicalSpace.Opens.mem_iSup.2 ⟨w, hV w⟩) hN

theorem isPreimmersion_of_comp {W Z Y : Scheme.{0}} (u : W ⟶ Z) (p : Z ⟶ Y) [IsPreimmersion (u ≫ p)] :
    IsPreimmersion u where
  toSurjectiveOnStalks := SurjectiveOnStalks.of_comp u p
  isEmbedding := Topology.IsEmbedding.of_comp u.continuous p.continuous (u ≫ p).isEmbedding

theorem flat_of_isPreimmersion {W Z : Scheme.{0}} (u : W ⟶ Z) [IsPreimmersion u] [QuasiCompact u]
    [IsSchemeTheoreticallyDominant u] : Flat u := by
  refine Flat.of_stalkMap u fun w => RingHom.Flat.of_bijective ⟨?_, u.stalkMap_surjective w⟩
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  obtain ⟨V, hV, s, rfl⟩ := Z.presheaf.exists_germ_eq a
  rw [Scheme.Hom.germ_stalkMap_apply] at ha
  obtain ⟨T, hT, iT, iT', hs⟩ := W.presheaf.germ_eq (U := u ⁻¹ᵁ V) (V := u ⁻¹ᵁ V) w hV hV (u.app V s) 0
    (by rw [ha, map_zero])
  obtain ⟨T', hT', hTT'⟩ := u.isEmbedding.isInducing.isOpen_iff.1 T.isOpen
  let V' : Z.Opens := V ⊓ ⟨T', hT'⟩
  have hw : u w ∈ V' := ⟨hV, by
    have : w ∈ u ⁻¹' T' := hTT' ▸ hT
    exact this⟩
  have hle : u ⁻¹ᵁ V' ≤ T := fun x hx => by
    have : x ∈ u ⁻¹' T' := hx.2
    exact hTT'.subset this
  have h0 : Z.presheaf.map (homOfLE (inf_le_left : V' ≤ V)).op s = 0 := by
    apply u.app_injective V'
    rw [map_zero, ← CommRingCat.comp_apply, u.naturality, CommRingCat.comp_apply]
    have := congrArg (W.presheaf.map (homOfLE hle).op) hs
    rw [map_zero, map_zero, ← CommRingCat.comp_apply, ← Functor.map_comp] at this
    exact this
  rw [← Z.presheaf.germ_res_apply (homOfLE (inf_le_left : V' ≤ V)) (u w) hw, h0, map_zero]

def chartPullPowSingle {X : Scheme.{0}} (L : LB X) (n : ℕ) :
    ChartPull (lbPow L n) (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (n : ℤ))) (𝟙 X) where
  idx J := fun _ => J PUnit.unit
  le _ _ hy := Set.mem_iInter.2 fun _ => mem_powChart.1 hy
  g y J J' hJ hJ' := by
    have h₁ := mem_powChart.1 hJ
    have h₂ := mem_powChart.1 hJ'
    refine (gm_lbPow_g n (𝟙 X) y J J' hJ hJ').trans (Eq.trans ?_ (gm_linComb L (fun _ : Fin 1 => 𝟙 X)
      (fun _ => (n : ℤ)) (𝟙 X) y _ _ (Set.mem_iInter.2 fun _ => h₁) (Set.mem_iInter.2 fun _ => h₂)).symm)
    simp

theorem exists_affine_locus_pull {X Y : Scheme.{0}} {A : LB Y} (hA : A.IsLB)
    (ha : ∀ y : Y, ∃ (d : ℕ) (s : Out.H0 A d), 1 ≤ d ∧ y ∈ Out.nonzeroLocus s ∧ IsAffineOpen (Out.nonzeroLocus s))
    (q : X ⟶ Y) [IsAffineHom q] (x : X) :
    ∃ (d : ℕ) (s : LB.Sec (LB.LinComb (A.pull q) (K := Fin d) (fun _ => 𝟙 X) (fun _ => 1))),
      x ∈ Out.nonzeroLocus s ∧ IsAffineOpen (Out.nonzeroLocus s) := by
  obtain ⟨d, s, -, hx, hs⟩ := ha (q x)
  have hq := pull_isLB hA q
  have e₁ := nonzeroLocus_chartSec_id (chartPullPowSingle A d) s fun y J hJ =>
    ⟨fun _ => J 0, mem_powChart.2 (Set.mem_iInter.1 hJ 0)⟩
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_linComb hq _ _)
    (isLB_lbPow (pull_isLB hq _) d) (lbIso_lbPow_finPow hq (𝟙 X) d).symm
    (secPowPull (secPowPull (chartSec (chartPullPowSingle A d) s) q) (𝟙 X))
  rw [nonzeroLocus_secPowPull, nonzeroLocus_secPowPull, e₁] at ht
  refine ⟨d, t, ?_, ?_⟩
  · rw [ht]; exact hx
  · rw [ht]; exact hs.preimage q

set_option backward.isDefEq.respectTransparency false in

theorem isFinite_fst {Z Z₁ Z₂ S : Scheme.{0}} [IsAffine S] (s₁ : Z₁ ⟶ S) (s₂ : Z₂ ⟶ S) [IsProper s₂]
    (ν : Z ⟶ pullback s₁ s₂) [IsFinite ν] {A₁ : LB Z₁} {A₂ : LB Z₂} (h₁ : A₁.IsLB) (h₂ : A₂.IsLB)
    (ha : ∀ y : Z₂, ∃ (d : ℕ) (s : Out.H0 A₂ d), 1 ≤ d ∧ y ∈ Out.nonzeroLocus s ∧
      IsAffineOpen (Out.nonzeroLocus s))
    (H : LBIso (A₁.pull (ν ≫ pullback.fst s₁ s₂)) (A₂.pull (ν ≫ pullback.snd s₁ s₂))) :
    IsFinite (ν ≫ pullback.fst s₁ s₂) := by
  have : LocallyQuasiFinite (ν ≫ pullback.fst s₁ s₂) := by
    refine (IsZariskiLocalAtTarget.iff_of_openCover (P := @LocallyQuasiFinite) Z₁.affineCover).2 fun i => ?_
    let g := Z₁.affineCover.f i
    let p := ν ≫ pullback.fst s₁ s₂
    let q := pullback.fst p g ≫ ν ≫ pullback.snd s₁ s₂
    change LocallyQuasiFinite (pullback.snd p g)
    have hq : IsAffineHom q := by
      let m : pullback (g ≫ s₁) s₂ ⟶ pullback s₁ s₂ := pullback.map _ _ _ _ g (𝟙 _) (𝟙 _) (by simp) (by simp)
      have hm : IsPullback m (pullback.fst _ _) (pullback.fst s₁ s₂) g := by
        refine IsPullback.of_right (h₁₂ := pullback.snd s₁ s₂) (v₁₃ := s₂) (h₂₂ := s₁) ?_ (by simp [m])
          (IsPullback.of_hasPullback s₁ s₂).flip
        have : m ≫ pullback.snd s₁ s₂ = pullback.snd _ _ := by simp [m]
        rw [this]
        exact (IsPullback.of_hasPullback (g ≫ s₁) s₂).flip
      let l : pullback p g ⟶ pullback (g ≫ s₁) s₂ :=
        hm.lift (pullback.fst p g ≫ ν) (pullback.snd p g) (by simpa [p] using pullback.condition (f := p) (g := g))
      have hl : IsPullback (pullback.fst p g) l ν m := by
        refine IsPullback.of_bot ?_ (by simp [l]) hm
        have : l ≫ pullback.fst (g ≫ s₁) s₂ = pullback.snd p g := by simp [l]
        rw [this]
        exact IsPullback.of_hasPullback p g
      have : IsFinite l := MorphismProperty.of_isPullback hl inferInstance
      have : IsAffineHom (pullback.snd (g ≫ s₁) s₂) :=
        MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ (inferInstance : IsAffineHom (g ≫ s₁))
      have e : q = l ≫ pullback.snd (g ≫ s₁) s₂ := by
        have : pullback.snd (g ≫ s₁) s₂ = m ≫ pullback.snd s₁ s₂ := by simp [m]
        rw [this, ← hl.w_assoc]
      rw [e]
      infer_instance
    refine GlobalTheory.AmpleFibre.locallyQuasiFinite_of_trivial_on_fibres _ _ (pullback.snd p g) (A₂.pull q) inferInstance (pull_isLB h₂ q)
      (exists_affine_locus_pull h₂ ha q) fun k _ _ y C _ c _ => ?_
    let a := c ≫ pullback.fst (pullback.snd p g) y
    have e : a ≫ pullback.fst p g ≫ p = (c ≫ pullback.snd (pullback.snd p g) y) ≫ y ≫ g := by
      simp only [a, Category.assoc, pullback.condition, pullback.condition_assoc]
    obtain ⟨t, ht⟩ := DVR.exists_gen_of_local (V := k) A₁ h₁ (K := PUnit) (fun _ => y ≫ g) (fun _ => 1)
    have g₁ : ∃ t : (A₁.pull ((c ≫ pullback.snd (pullback.snd p g) y) ≫ y ≫ g)).Gen, t.IsGen :=
      ⟨_, DVR.pullGen_isGen _ _ _ t ht _⟩
    have i₁ : LBIso (A₁.pull ((c ≫ pullback.snd (pullback.snd p g) y) ≫ y ≫ g)) (A₂.pull (a ≫ q)) :=
      GenSpread.lbIso_pull_comp (a ≫ pullback.fst p g) (e.symm.trans (Category.assoc _ _ _).symm) (by simp [q]) H
    exact GlobalTheory.SiegelDescent.exists_gen_of_lbIso (pull_isLB h₂ _) (pull_isLB (pull_isLB h₂ _) _) (GenSpread.lbIso_pull_pull h₂ a rfl)
      (GlobalTheory.SiegelDescent.exists_gen_of_lbIso (pull_isLB h₁ _) (pull_isLB h₂ _) i₁ g₁)
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

theorem isFinite_fromNormalization_graph {R : Type} [CommRing R] [IsDedekindDomain R] [CharZero R]
    {W Y : Scheme.{0}} (f : W ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [SurjectiveOnStalks f]
    (g : Y ⟶ Sp R) [LocallyOfFiniteType g] [Flat (f ≫ g)] [IsReduced W] [IsLocallyNoetherian W] :
    IsFinite f.fromNormalization := by
  refine isFinite_fromNormalization_of_genericPoints (o := CommRingCat.of R) f g (fun x hx => ?_) fun x _ => ?_
  · have hsp : genericPoint (Sp R) ⤳ (f ≫ g) x := (genericPoint_spec (Sp R)).specializes trivial
    obtain ⟨x', hx', e⟩ := Flat.generalizingMap (f ≫ g) hsp
    obtain rfl := eq_of_specializes_of_mem_genericPoints hx hx'
    have : CharZero ((Sp R).residueField ((f ≫ g) x')) := by
      rw [e]
      have : Nonempty (⊤ : (Sp R).Opens) := ⟨⟨genericPoint (Sp R), trivial⟩⟩
      have : CharZero (Sp R).functionField :=
        charZero_of_injective_ringHom (R := R)
          (f := ((Scheme.ΓSpecIso (.of R)).inv ≫ (Sp R).germToFunctionField ⊤).hom)
          (((Sp R).germToFunctionField_injective ⊤).comp
            (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).1)
      exact charZero_of_injective_ringHom (R := (Sp R).functionField)
        ((Sp R).residue (genericPoint (Sp R))).hom.injective
    exact charZero_of_injective_ringHom ((f ≫ g).residueFieldMap x').hom.injective
  · exact (RingHom.FiniteType.of_surjective _ (f.stalkMap_surjective x)).essFiniteType.residueFieldMap

theorem genericPoints_subset_abLocus {W Z : Scheme.{0}} (u : W ⟶ Z) [IsPreimmersion u] [Flat u] [IsDominant u]
    [QuasiCompact u] {G : Over Z} {G' : Over W} {φ : G'.left ⟶ G.left} (h : IsPullback φ G'.hom G.hom u)
    [IsProper G'.hom] : genericPoints Z ⊆ abLocus G := by
  intro z hz K _ _ t ht
  obtain ⟨w, rfl⟩ := genericPoints_subset_range_of_isDominant u hz
  obtain ⟨y, rfl⟩ := HomExt.exists_lift_of_range_subset u t (by
    rintro _ ⟨p, rfl⟩
    obtain ⟨p', hp'⟩ := ht
    exact ⟨w, hp'.symm.trans (congrArg t (Subsingleton.elim _ _))⟩)
  have P := (IsPullback.of_hasPullback G'.hom y).paste_horiz h
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper P.isoPullback.hom _).1
    (by rw [P.isoPullback_hom_snd]; infer_instance)

theorem exists_hom_of_ampFrames : GlobalTheory.LN.HomExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (Z₁ Z₂ W : Scheme.{0}) (s₁ : Z₁ ⟶ Sp R) (s₂ : Z₂ ⟶ Sp R) (t₁ : SAB H Z₁) (t₂ : SAB H Z₂) (tW : SAB H W) (j : W ⟶ Z₁) (j' : W ⟶ Z₂) (_ : SABMap tW t₁ j) (_ : SABMap tW t₂ j') (N : ℕ) (A₁ : GlobalTheory.LN.AmpFrames t₁.G t₁.PP.L N) (A₂ : GlobalTheory.LN.AmpFrames t₂.G t₂.PP.L N), IsDedekindDomain R → CharZero R → Algebra.FiniteType ℤ R → Geo.Tor.IsNormalScheme Z₁ → IsProjOver s₁ → IsProjOver s₂ → Flat s₁ → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → IsPreimmersion j' → Flat j' → IsDominant j' → QuasiCompact j' → IsProper tW.G.hom → j ≫ s₁ = j' ≫ s₂ → A₁.r = A₂.r → A₁.s = A₂.s → ∃ ρ : Z₁ ⟶ Z₂, j ≫ ρ = j' := by
  intro hE E _ _ _ H R _ Z₁ Z₂ W s₁ s₂ t₁ t₂ tW j j' m₁ m₂ N A₁ A₂ _ _ _ hn hp₁ hp₂ _ _ _ _ _ _ _ _ _ _ w hr hs
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver hp₁
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver hp₂
  have : IsLocallyNoetherian Z₁ := LocallyOfFiniteType.isLocallyNoetherian s₁
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks j
  have : GlobalTheory.IsNormalScheme W := GlobalTheory.IsNormalScheme.of_isIso_stalkMap j
  have : IsLocallyNoetherian W := isLocallyNoetherian_of_isPreimmersion j
  let f : W ⟶ pullback s₁ s₂ := pullback.lift j j' w
  have hf₁ : f ≫ pullback.fst s₁ s₂ = j := pullback.lift_fst _ _ _
  have hf₂ : f ≫ pullback.snd s₁ s₂ = j' := pullback.lift_snd _ _ _
  have : IsPreimmersion (f ≫ pullback.fst s₁ s₂) := hf₁ ▸ inferInstance
  have : QuasiCompact (f ≫ pullback.fst s₁ s₂) := hf₁ ▸ inferInstance
  have : IsPreimmersion f := isPreimmersion_of_comp f (pullback.fst s₁ s₂)
  have : QuasiCompact f := .of_comp f (pullback.fst s₁ s₂)
  have : Flat (f ≫ pullback.fst s₁ s₂ ≫ s₁) := by
    rw [reassoc_of% hf₁]; infer_instance
  have : IsFinite f.fromNormalization := isFinite_fromNormalization_graph f (pullback.fst s₁ s₂ ≫ s₁)
  let u := f.toNormalization
  let p₁ := f.fromNormalization ≫ pullback.fst s₁ s₂
  let p₂ := f.fromNormalization ≫ pullback.snd s₁ s₂
  have hu₁ : u ≫ p₁ = j := by simp [u, p₁, hf₁]
  have hu₂ : u ≫ p₂ = j' := by simp [u, p₂, hf₂]
  have : IsPreimmersion (u ≫ p₁) := hu₁ ▸ inferInstance
  have : IsPreimmersion u := isPreimmersion_of_comp u p₁
  have : Flat u := flat_of_isPreimmersion u
  have hZ := GlobalTheory.IsNormalScheme.pred f.normalization
  have : IsLocallyNoetherian f.normalization := LocallyOfFiniteType.isLocallyNoetherian p₁
  let z₀ : Sp R ⟶ Sp ℤ := spMap (algebraMap ℤ R)
  have : LocallyOfFiniteType z₀ :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 ‹_›)
  have : Flat z₀ := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Flat (f.toNormalization ≫ p₁ ≫ s₁) := by
    rw [reassoc_of% hu₁]; infer_instance
  have : Flat (p₁ ≫ s₁) := flat_normalization f (p₁ ≫ s₁)
  obtain ⟨_, _, _, _, _, n₁, -⟩ := sabPull Out.CubePf.cubePull p₁ t₁
  obtain ⟨_, _, _, _, _, n₂, -⟩ := sabPull Out.CubePf.cubePull p₂ t₂
  obtain ⟨a₁, -⟩ := ObjMaps.exists_sab_cancel n₁ (hu₁ ▸ m₁ : SABMap tW t₁ (u ≫ p₁))
  obtain ⟨a₂, -⟩ := ObjMaps.exists_sab_cancel n₂ (hu₂ ▸ m₂ : SABMap tW t₂ (u ≫ p₂))
  obtain ⟨b, -⟩ := GlobalTheory.exists_sabMap_id_of_common_generic hE E H _ W u
    ⟨hZ, (p₁ ≫ s₁) ≫ z₀, inferInstance, inferInstance⟩ inferInstance inferInstance inferInstance inferInstance
    tW _ _ a₁ a₂ inferInstance
  obtain ⟨n₂', -⟩ := ObjMaps.exists_sab_comp n₂ b
  rw [Category.id_comp] at n₂'
  have hA := GlobalTheory.T.lineBundleIso_of_ampleDeterminantFrames E H _ Z₁ Z₂ ((p₁ ≫ s₁) ≫ z₀) _ t₁ t₂ p₁ p₂ n₁ n₂' N A₁ A₂ hZ inferInstance
    (genericPoints_subset_abLocus u a₁.cart.1) hr hs
  have : IsFinite p₁ := isFinite_fst s₁ s₂ f.fromNormalization A₁.isLB A₂.isLB A₂.ample hA
  obtain ⟨h, ⟨h₁, -⟩, -⟩ := existsUnique_lift_of_densePart Z₁ W Z₁ f.normalization j hn inferInstance inferInstance
    inferInstance inferInstance p₁ (𝟙 _) u inferInstance (by rw [hu₁, Category.comp_id])
  exact ⟨h ≫ p₂, by rw [reassoc_of% h₁, hu₂]⟩

end GlobalTheory.AmpUniq
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_birational_models_ampleFrames : GlobalTheory.LN.HomExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (Z₁ Z₂ W : Scheme.{0}) (s₁ : Z₁ ⟶ Sp R) (s₂ : Z₂ ⟶ Sp R) (t₁ : SAB H Z₁) (t₂ : SAB H Z₂) (tW : SAB H W) (j : W ⟶ Z₁) (j' : W ⟶ Z₂) (_ : SABMap tW t₁ j) (_ : SABMap tW t₂ j') (N : ℕ) (A₁ : GlobalTheory.LN.AmpFrames t₁.G t₁.PP.L N) (A₂ : GlobalTheory.LN.AmpFrames t₂.G t₂.PP.L N), IsDedekindDomain R → CharZero R → Algebra.FiniteType ℤ R → IsNormalScheme Z₁ → IsProjOver s₁ → IsProjOver s₂ → Flat s₁ → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → IsPreimmersion j' → Flat j' → IsDominant j' → QuasiCompact j' → IsProper tW.G.hom → j ≫ s₁ = j' ≫ s₂ → A₁.r = A₂.r → A₁.s = A₂.s → ∃ ρ : Z₁ ⟶ Z₂, j ≫ ρ = j' := by
  first | exact @GlobalTheory.AmpUniq.exists_hom_of_ampFrames | exact GlobalTheory.AmpUniq.exists_hom_of_ampFrames | (intros; apply GlobalTheory.AmpUniq.exists_hom_of_ampFrames <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduli_finite_surjective_over_generic_family : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)) (l : Level H) (Xo : Moduli D l) (β : RZ H n N →+* KA l), l.A = N → n.Prime → Odd n → (∃ j, 1 ≤ j ∧ N = n ^ j) → N.Coprime l.M → IsInc (RZ H n N).subtype (KA l).val.toRingHom β → FamCore D sM tM lev → ∃ (a : Xo.X ⟶ MM) (ν : SABMap Xo.univ.t tM a) (h : a ≫ sM = Xo.s ≫ spMap β), (∀ x, (Xo.univ.etaA x).left ≫ ν.φ = a ≫ (lev x).left) ∧ IsFinite (pullback.lift a _ h) ∧ Surjective (pullback.lift a _ h) := by
  first | exact @GlobalTheory.moduli_finite_surjective_over_family | exact GlobalTheory.moduli_finite_surjective_over_family | (intros; apply GlobalTheory.moduli_finite_surjective_over_family <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullLevelChange_acts_on_unitaryFamily : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)) (l : Level H) (Xo : Moduli D l) (β : RZ H n N →+* KA l) (a : Xo.X ⟶ MM) (ν₀ : SABMap Xo.univ.t tM a) (h : a ≫ sM = Xo.s ≫ spMap β) (r : Xo.X ≅ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t r.hom) (g : D.La →ₗ[𝓞 E] D.La) (σ : KA l ≃+* KA l), 1 ≤ D.p + D.q → l.A = N → n.Prime → Odd n → (∃ j, 1 ≤ j ∧ N = n ^ j) → IsInc (RZ H n N).subtype (KA l).val.toRingHom β → FamCore D sM tM lev → Surjective (pullback.lift a _ h) → (∀ x, (Xo.univ.etaA x).left ≫ ν₀.φ = a ≫ (lev x).left) → σ (baseKA l).ρ = (baseKA l).ρ → r.hom ≫ Xo.s = Xo.s ≫ spMap σ.toRingHom → (∀ x, (Xo.univ.etaA (g x)).left ≫ ν.φ = r.hom ≫ (Xo.univ.etaA x).left) → ∃ (ρ : MM ≅ MM) (_ : SABMap tM tM ρ.hom) (σ₀ : RZ H n N ≃+* RZ H n N), a ≫ ρ.hom = r.hom ≫ a ∧ ρ.hom ≫ sM = sM ≫ spMap σ₀.toRingHom ∧ σ₀ (RZ.rt H n N) = RZ.rt H n N := by
  first | exact @GlobalTheory.famCore_exists_aut | exact GlobalTheory.famCore_exists_aut | (intros; apply GlobalTheory.famCore_exists_aut <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.TopOfFamily

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc pullback.lift_snd_assoc

theorem exists_section {U M : Scheme.{0}} (u : U ⟶ M) (W : M.Opens) [IsIso (u ∣_ W)] :
    ∃ i : W.toScheme ⟶ U, IsOpenImmersion i ∧ i ≫ u = W.ι ∧
      ∀ (T : Scheme.{0}) (g : T ⟶ U) (b : T ⟶ W.toScheme), g ≫ u = b ≫ W.ι → g = b ≫ i := by
  have hp := isPullback_morphismRestrict u W
  refine ⟨inv (u ∣_ W) ≫ (u ⁻¹ᵁ W).ι, inferInstance, ?_, fun T g b h => ?_⟩
  · rw [Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  · have h1 := hp.lift_fst b g h.symm
    have h2 := hp.lift_snd b g h.symm
    rw [← h1, Category.assoc, IsIso.hom_inv_id_assoc, h2]

theorem isProjOver_comp_iso {R : Type} [CommRing R] {Z : Scheme.{0}} {s : Z ⟶ Sp R} (h : IsProjOver s) (σ : R ≃+* R) :
    IsProjOver (s ≫ spMap σ.toRingHom) := by
  obtain ⟨L, hL⟩ := GlobalTheory.exists_isAmpleLB_of_isProjOver h
  have := projProper _ _ _ h
  have : IsIso (CommRingCat.ofHom σ.toRingHom) := σ.toCommRingCatIso.isIso_hom
  exact hL.isProjOver _

theorem isReduced_of_normal {Z : Scheme.{0}} (h : Geo.Tor.IsNormalScheme Z) : IsReduced Z := by
  have : ∀ x : Z, _root_.IsReduced (Z.presheaf.stalk x) := fun x ↦
    have := (h x).1
    inferInstance
  exact isReduced_of_isReduced_stalk Z

theorem charZero_residueField {k : Type} [Field k] [CharZero k] {S : Scheme.{0}} (s : S ⟶ Sp k) (p : S) :
    CharZero (S.residueField p) := by
  obtain ⟨φ, -⟩ := Spec.map_surjective (S.fromSpecResidueField p ≫ s)
  exact charZero_of_injective_ringHom (R := k) φ.hom.injective

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  rw [spMap, spMap, ← Spec.map_comp]; rfl

theorem asIdeal_spMap {A k : Type} [CommRing A] [Field k] (β : A →+* k) (hβ : Function.Injective β) (x : Sp k) :
    (spMap β x).asIdeal = ⊥ := by
  have h : x.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ x.isPrime
  change Ideal.comap β x.asIdeal = ⊥
  rw [h]
  exact (RingHom.injective_iff_ker_eq_bot _).1 hβ

theorem isDominant_snd {X U Y : Scheme.{0}} (j : U ⟶ X) [IsDominant j] (p : Y ⟶ X) [IsOpenImmersion p] :
    IsDominant (pullback.snd j p) := by
  have := isDominant_pullback_fst_of_isOpenMap j p p.isOpenEmbedding.isOpenMap
  rw [← pullbackSymmetry_hom_comp_fst]
  infer_instance

theorem comp_eq_of_dense {Z U M W W₀ W' X : Scheme.{0}} [IsReduced Z] [Z.IsSeparated] (v : U ⟶ Z) [IsOpenImmersion v]
    (u : U ⟶ M) (w₀ : W₀ ⟶ M) [IsOpenImmersion w₀] (i : W₀ ⟶ U) [IsOpenImmersion i] (hi : i ≫ u = w₀)
    (hu : ∀ (T : Scheme.{0}) (g : T ⟶ U) (b : T ⟶ W₀), g ≫ u = b ≫ w₀ → g = b ≫ i)
    (j : W ⟶ U) (e₁ e₂ : W' ⟶ W) [IsDominant (e₁ ≫ j ≫ v)] (ρ : M ≅ M) (he : e₁ ≫ j ≫ u ≫ ρ.hom = e₂ ≫ j ≫ u)
    (τ : Z ⟶ Z) (hτ : (e₁ ≫ j ≫ v) ≫ τ = e₂ ≫ j ≫ v) (b b' : X ⟶ W₀) (hb : b ≫ w₀ ≫ ρ.hom = b' ≫ w₀) :
    (b ≫ i ≫ v) ≫ τ = b' ≫ i ≫ v := by
  let d₁ := pullback.fst (w₀ ≫ ρ.hom) w₀
  let d₂ := pullback.snd (w₀ ≫ ρ.hom) w₀
  have hd : d₁ ≫ w₀ ≫ ρ.hom = d₂ ≫ w₀ := pullback.condition
  have key : (d₁ ≫ i ≫ v) ≫ τ = d₂ ≫ i ≫ v := by
    have := isReduced_of_isOpenImmersion (d₁ ≫ i ≫ v)
    have := isDominant_snd (e₁ ≫ j ≫ v) (d₁ ≫ i ≫ v)
    have hq := pullback.condition (f := e₁ ≫ j ≫ v) (g := d₁ ≫ i ≫ v)
    set q₁ := pullback.fst (e₁ ≫ j ≫ v) (d₁ ≫ i ≫ v)
    set q₂ := pullback.snd (e₁ ≫ j ≫ v) (d₁ ≫ i ≫ v)
    refine ext_of_isDominant q₂ ?_
    have h1 : q₁ ≫ e₁ ≫ j = q₂ ≫ d₁ ≫ i := by
      rw [← cancel_mono v]; simpa using hq
    have h2 : q₁ ≫ e₂ ≫ j = (q₂ ≫ d₂) ≫ i := by
      refine hu _ _ _ ?_
      simp only [Category.assoc]
      rw [← he, reassoc_of% h1, reassoc_of% hi, hd]
    rw [← Category.assoc q₂, ← hq, Category.assoc, hτ, reassoc_of% h2]
  have h1 := pullback.lift_fst b b' (f := w₀ ≫ ρ.hom) (g := w₀) hb
  have h2 := pullback.lift_snd b b' (f := w₀ ≫ ρ.hom) (g := w₀) hb
  rw [← h1]
  conv_rhs => rw [← h2]
  simp only [Category.assoc] at key ⊢
  rw [key]

theorem exists_finite_lift {Z M W₀ X B B' : Scheme.{0}} (U : Z.Opens) (s : Z ⟶ B) (sM : M ⟶ B) (β : B' ⟶ B)
    (u : U.toScheme ⟶ M) (hs : u ≫ sM = U.ι ≫ s) (w₀ : W₀ ⟶ M) [IsOpenImmersion w₀] (i : W₀ ⟶ U.toScheme)
    (hi : i ≫ u = w₀) (hu : ∀ (T : Scheme.{0}) (g : T ⟶ U) (b : T ⟶ W₀), g ≫ u = b ≫ w₀ → g = b ≫ i)
    (hr : Set.range (pullback.fst sM β) ⊆ Set.range w₀) (b : X ⟶ W₀) (c : X ⟶ B') (h : (b ≫ w₀) ≫ sM = c ≫ β)
    (hf : IsFinite (pullback.lift _ _ h)) (hsu : Surjective (pullback.lift _ _ h)) :
    ∃ f : X ⟶ (pullback.fst s β ⁻¹ᵁ U).toScheme, IsFinite f ∧ Surjective f ∧
      f ≫ (pullback.fst s β ⁻¹ᵁ U).ι ≫ pullback.fst _ _ = b ≫ i ≫ U.ι ∧
      f ≫ (pullback.fst s β ⁻¹ᵁ U).ι ≫ pullback.snd _ _ = c := by
  have hp := isPullback_morphismRestrict (pullback.fst s β) U
  obtain ⟨p, hp₀⟩ : ∃ p, p ≫ w₀ = pullback.fst sM β := ⟨_, IsOpenImmersion.lift_fac w₀ _ hr⟩
  have c₁ : (p ≫ i ≫ U.ι) ≫ s = pullback.snd sM β ≫ β := by
    simp only [Category.assoc]
    rw [← hs, reassoc_of% hi, reassoc_of% hp₀, pullback.condition]
  have c₂ : (p ≫ i) ≫ U.ι = pullback.lift _ _ c₁ ≫ pullback.fst s β := by simp
  have c₃ : (pullback.fst s β ∣_ U ≫ u) ≫ sM = ((pullback.fst s β ⁻¹ᵁ U).ι ≫ pullback.snd s β) ≫ β := by
    simp only [Category.assoc]
    rw [hs, morphismRestrict_ι_assoc, pullback.condition]
  have g₁ := hp.lift_fst _ _ c₂
  have g₂ := hp.lift_snd _ _ c₂
  set g := hp.lift _ _ c₂
  have hk : pullback.fst s β ∣_ U = (pullback.lift _ _ c₃ ≫ p) ≫ i := hu _ _ _ (by simp [hp₀])
  have : IsIso g := by
    refine ⟨pullback.lift _ _ c₃, ?_, ?_⟩
    · apply pullback.hom_ext
      · simp [reassoc_of% g₁, hi, hp₀]
      · simp [reassoc_of% g₂]
    · apply hp.hom_ext
      · rw [Category.assoc, g₁, Category.id_comp, ← Category.assoc, ← hk]
      · rw [Category.assoc, g₂, Category.id_comp]
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst]
          rw [← morphismRestrict_ι]
          conv_rhs => rw [hk]
          simp
        · simp
  refine ⟨pullback.lift _ _ h ≫ g, inferInstance, inferInstance, ?_, ?_⟩
  · have : pullback.lift _ _ h ≫ p = b := by
      rw [← cancel_mono w₀]; simp [hp₀]
    simp [reassoc_of% g₂, reassoc_of% this]
  · simp [reassoc_of% g₂]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem comp_of_eq {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {h : S'' ⟶ S} (m : SABMap t' t f) (m' : SABMap t'' t' g) (e : g ≫ f = h) :
    ∃ n : SABMap t'' t h, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabComp pullCubComp E H _ _ _ t t' t'' f g m m'

theorem cancel_of_eq {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S}
    {g : S'' ⟶ S'} {h : S'' ⟶ S} (m : SABMap t' t f) (n : SABMap t'' t h) (e : g ≫ f = h) :
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ := by
  subst e
  exact sabCancel pullCubCancel E H _ _ _ t t' t'' f g m n

section Model

variable {R : Type} [CommRing R] {MM : Scheme.{0}} {sM : MM ⟶ Sp R} {tM : SAB H MM} {m : ℕ} (C : ZOn sM tM m)

theorem isLocallyNoetherian [IsNoetherianRing R] : IsLocallyNoetherian C.Z := by
  have := projProper _ _ _ C.proj
  exact LocallyOfFiniteType.isLocallyNoetherian C.s

theorem isSeparated : C.Z.IsSeparated := by
  have := projProper _ _ _ C.proj
  refine ⟨?_⟩
  rw [← terminal.comp_from C.s]
  infer_instance

theorem genericPoints_subset [IsNoetherianRing R] [IsProper tM.G.hom] : genericPoints C.Z ⊆ abLocus C.t.G := by
  have := isLocallyNoetherian C
  have := C.j_open
  have := C.j_dom
  refine (genericPoints_subset_range_of_isDominant C.j).trans ?_
  rintro _ ⟨x, rfl⟩
  rw [abLocus_pullback abLocusOne C.t.semi C.m₂.cart.1, ← abLocus_pullback abLocusOne tM.semi C.m₁.cart.1]
  intro K _ _ t _
  infer_instance

theorem range_j_subset [IsProper tM.G.hom] : Set.range C.j ⊆ abLocus C.t.G := by
  rintro _ ⟨x, rfl⟩
  rw [abLocus_pullback abLocusOne C.t.semi C.m₂.cart.1, ← abLocus_pullback abLocusOne tM.semi C.m₁.cart.1]
  intro K _ _ t _
  infer_instance

theorem exists_iso (hH : GlobalTheory.LN.HomExtSt) (hR : IsDedekindDomain R) [CharZero R] (hft : Algebra.FiniteType ℤ R)
    [IsProper tM.G.hom] (ρ : MM ≅ MM) (mu : SABMap tM tM ρ.hom) (σ : R ≃+* R)
    (hρ : ρ.hom ≫ sM = sM ≫ spMap σ.toRingHom) :
    ∃ (W' : Scheme.{0}) (e₁ e₂ : W' ⟶ C.W.toScheme) (τ : C.Z ≅ C.Z), IsDominant (e₁ ≫ C.j) ∧
      e₁ ≫ C.W.ι ≫ ρ.hom = e₂ ≫ C.W.ι ∧ (e₁ ≫ C.j) ≫ τ.hom = e₂ ≫ C.j := by
  have := isLocallyNoetherian C
  have := isSeparated C
  have := isReduced_of_normal C.normal
  have := C.j_open
  have := C.j_dom
  have : IsDominant C.W.ι := ⟨by rw [DenseRange, Scheme.Opens.range_ι]; exact C.dense⟩
  have d₁ := isDominant_pullback_fst_of_isOpenMap C.W.ι (C.W.ι ≫ ρ.hom) (C.W.ι ≫ ρ.hom).isOpenEmbedding.isOpenMap
  have d₂ := isDominant_snd (C.W.ι ≫ ρ.hom) C.W.ι
  have he := pullback.condition (f := C.W.ι ≫ ρ.hom) (g := C.W.ι)
  have o₁ : IsOpenImmersion (pullback.fst (C.W.ι ≫ ρ.hom) C.W.ι) := inferInstance
  have o₂ : IsOpenImmersion (pullback.snd (C.W.ι ≫ ρ.hom) C.W.ι) := inferInstance
  set e₁ := pullback.fst (C.W.ι ≫ ρ.hom) C.W.ι
  set e₂ := pullback.snd (C.W.ι ≫ ρ.hom) C.W.ι
  obtain ⟨t', ⟨n₁⟩⟩ : ∃ t' : SAB H _, Nonempty (SABMap t' C.tW e₁) := by
    obtain ⟨_, _, _, _, _, n, -⟩ := sabPull Out.CubePf.cubePull e₁ C.tW
    exact ⟨_, ⟨n⟩⟩
  obtain ⟨k₁, -⟩ := comp_of_eq C.m₁ n₁ rfl
  obtain ⟨k₂, -⟩ := comp_of_eq mu k₁ ((Category.assoc _ _ _).trans he)
  obtain ⟨n₂, -⟩ := cancel_of_eq C.m₁ k₂ rfl
  obtain ⟨p₁, -⟩ := comp_of_eq C.m₂ n₁ rfl
  obtain ⟨p₂, -⟩ := comp_of_eq C.m₂ n₂ rfl
  have hp : IsProper t'.G.hom := MorphismProperty.of_isPullback k₁.cart.1 inferInstance
  have h₂ : (e₂ ≫ C.j) ≫ C.s = (e₁ ≫ C.j) ≫ C.s ≫ spMap σ.toRingHom := by
    simp only [Category.assoc]
    rw [C.j_over, reassoc_of% C.j_over, ← reassoc_of% he, hρ]
  have h₁ : (e₁ ≫ C.j) ≫ C.s = (e₂ ≫ C.j) ≫ C.s ≫ spMap σ.symm.toRingHom := by
    have : spMap σ.toRingHom ≫ spMap σ.symm.toRingHom = 𝟙 _ := by
      rw [spMap_comp, RingEquiv.toRingHom_comp_symm_toRingHom]
      exact Spec.map_id _
    rw [← Category.assoc _ C.s, h₂, Category.assoc (e₁ ≫ C.j), Category.assoc C.s, this, Category.comp_id]
  obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_hom_birational_models_ampleFrames hH E H R C.Z C.Z _ C.s _ C.t C.t t' _ _ p₁ p₂ _ C.amp C.amp hR inferInstance hft
    C.normal C.proj (isProjOver_comp_iso C.proj σ.symm) C.flat inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance hp h₁ rfl rfl
  obtain ⟨τ', hτ'⟩ := GlobalTheory.T.exists_hom_birational_models_ampleFrames hH E H R C.Z C.Z _ C.s _ C.t C.t t' _ _ p₂ p₁ _ C.amp C.amp hR inferInstance hft
    C.normal C.proj (isProjOver_comp_iso C.proj σ) C.flat inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance hp h₂ rfl rfl
  refine ⟨_, e₁, e₂, ⟨τ, τ', ?_, ?_⟩, inferInstance, he, hτ⟩
  · refine ext_of_isDominant (e₁ ≫ C.j) ?_
    rw [← Category.assoc, hτ, hτ', Category.comp_id]
  · refine ext_of_isDominant (e₂ ≫ C.j) ?_
    rw [← Category.assoc, hτ', hτ, Category.comp_id]

end Model

theorem exists_inc {n N : ℕ} (hn : n.Prime) (hN : ∃ j, 1 ≤ j ∧ N = n ^ j) (l : Level H) (h : l.A = N) :
    IsDedekindDomain (RZ H n N) ∧ ∃ β : RZ H n N →+* KA l, IsInc (RZ H n N).subtype (KA l).val.toRingHom β ∧
      Function.Injective β ∧ Flat (spMap β) := by
  subst h
  obtain ⟨j, -, hj⟩ := hN
  obtain ⟨⟨β, hβ⟩, -, h⟩ := BaseRing.isDedFrac_RZ E H l n j hn.pos hj.dvd
  obtain ⟨⟨_, hd⟩, -, hf⟩ := h β hβ
  letI := β.toAlgebra
  refine ⟨hd, β, hβ, IsFractionRing.injective (RZ H n l.A) (KA l), ?_⟩
  rw [Flat.SpecMap_iff]
  exact IsLocalization.flat (KA l) (nonZeroDivisors (RZ H n l.A))

theorem eq_of_isInc {R : Type} [CommRing R] {i : R →+* ℂ} {l : Level H} {β β' : R →+* KA l}
    (h : IsInc i (KA l).val.toRingHom β) (h' : IsInc i (KA l).val.toRingHom β') : β = β' :=
  RingHom.ext fun x => Subtype.ext ((h x).trans (h' x).symm)

theorem eq_of_level (hL : Out.Laws) {D : Datum H} {n N : ℕ} (h3 : 3 ≤ N) (hodd : Odd N) {MM : Scheme.{0}}
    {sM : MM ⟶ Sp (RZ H n N)} {tM : SAB H MM} {lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)} (F : FamCore D sM tM lev)
    {l : Level H} (h : l.A = N) (Xo : Moduli D l) {β : RZ H n N →+* KA l}
    (hβ : IsInc (RZ H n N).subtype (KA l).val.toRingHom β) [Flat (spMap β)] {a a' : Xo.X ⟶ MM}
    (ν : SABMap Xo.univ.t tM a) (ν' : SABMap Xo.univ.t tM a') (ha : a ≫ sM = Xo.s ≫ spMap β)
    (ha' : a' ≫ sM = Xo.s ≫ spMap β) (hν : ∀ x, (Xo.univ.etaA x).left ≫ ν.φ = a ≫ (lev x).left)
    (hν' : ∀ x, (Xo.univ.etaA x).left ≫ ν'.φ = a' ≫ (lev x).left) : a = a' ∧ ν.φ = ν'.φ := by
  subst h
  have := Xo.smooth
  have hs : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  obtain ⟨hr, -, hno⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ Xo.s hs
  have e : a = a' := (F.rep _ _ _ _ hr hno inferInstance (fullObj_of_obj Xo.s Xo.univ β hβ)).unique
    ⟨ha, ν, hν⟩ ⟨ha', ν', hν'⟩
  subst e
  exact ⟨rfl, GlobalTheory.fullObj_rigid hL E H D n _ _ _ sM tM lev _ a ν ν' Xo.univ.etaA h3 hodd F.obj hr
    (charZero_residueField Xo.s) hν hν'⟩

theorem exists_top : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)) (m : ℕ) (C : ZOn sM tM m), 1 ≤ D.p + D.q → AuxiliaryInertOddPrime H n → (∃ j, 1 ≤ j ∧ N = n ^ j) → 0 < m → FamCore D sM tM lev → SiegClause D sM tM lev → ∃ T : Top Xo n N, Nonempty (GlobalTheory.LN.AmpFrames T.t.G T.t.PP.L (m ^ 2)) := by
  intro hH hL hL2 E _ _ _ H D Xo n N MM sM tM lev m C hD hn hN hm F hS
  obtain ⟨U, hU, -⟩ := C.good.1
  obtain ⟨u, tU, mU, mM, hu, ufin, usurj, ⟨W₀, hW₀, hiso⟩, hj⟩ :=
    GlobalTheory.T.abelian_locus_open_family_over_level hH hL hL2 E H D n N MM sM tM lev m C U hn.1 (hN.imp fun _ h => h.2) hm F hU
  obtain ⟨i, hio, hi, hi'⟩ := exists_section u W₀
  have hab := F.obj.proper
  have hft := BaseRing.finiteType_RZ H n N
  have hnoeth : IsNoetherianRing (RZ H n N) := Algebra.FiniteType.isNoetherianRing ℤ _
  have hodd : Odd N := by
    obtain ⟨j, -, rfl⟩ := hN
    exact hn.2.1.pow
  have h3 : 3 ≤ N := by
    obtain ⟨j, hj, rfl⟩ := hN
    have h2 := hn.1.two_le
    obtain ⟨c, hc⟩ := hn.2.1
    exact le_trans (by omega) (Nat.le_self_pow (by omega) n)
  have hgen : ∀ {l : Level H} (β : RZ H n N →+* KA l), Function.Injective β → ∀ {T : Scheme.{0}} (f : T ⟶ MM)
      (c : T ⟶ Sp (KA l)), f ≫ sM = c ≫ spMap β → Set.range f ⊆ Set.range W₀.ι := by
    rintro l β hβ T f c h _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine hW₀ _ ?_
    rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
    exact asIdeal_spMap β hβ _
  have key : ∀ l : Level H, l.A = N → ∃ (β : RZ H n N →+* KA l) (b : (Xo l).X ⟶ W₀.toScheme)
      (ν : SABMap (Xo l).univ.t tM (b ≫ W₀.ι)) (ν' : SABMap (Xo l).univ.t tU (b ≫ i))
      (ν'' : SABMap (Xo l).univ.t C.t (b ≫ i ≫ U.ι)) (h : (b ≫ W₀.ι) ≫ sM = (Xo l).s ≫ spMap β),
      IsInc (RZ H n N).subtype (KA l).val.toRingHom β ∧ Function.Injective β ∧ Flat (spMap β) ∧
      ν.φ = ν'.φ ≫ mM.φ ∧ ν''.φ = ν'.φ ≫ mU.φ ∧
      (∀ x, ((Xo l).univ.etaA x).left ≫ ν.φ = (b ≫ W₀.ι) ≫ (lev x).left) ∧
      IsFinite (pullback.lift _ _ h) ∧ Surjective (pullback.lift _ _ h) := by
    intro l h
    obtain ⟨-, β, hβ, hinj, hfl⟩ := exists_inc hn.1 hN l h
    have hc : N.Coprime l.M := by
      obtain ⟨j, -, rfl⟩ := hN
      exact ((exists_two_auxiliary_inert_odd_primes_coprime_level E H).2 n hn l).pow_left j
    obtain ⟨a, ν, ha, h₁, h₂, h₃⟩ := GlobalTheory.T.moduli_finite_surjective_over_generic_family hL hL2 E H D n N MM sM tM lev l (Xo l) β h hn.1 hn.2.1 hN hc hβ F
    obtain ⟨b, rfl⟩ : ∃ b, b ≫ W₀.ι = a := ⟨_, IsOpenImmersion.lift_fac W₀.ι a (hgen β hinj a _ ha)⟩
    obtain ⟨ν', hν'⟩ := cancel_of_eq (g := b ≫ i) mM ν (by rw [Category.assoc, hi])
    obtain ⟨ν'', hν''⟩ := comp_of_eq mU ν' (Category.assoc _ _ _)
    exact ⟨β, b, ν, ν', ν'', ha, hβ, hinj, hfl, hν', hν'', h₁, h₂, h₃⟩
  choose β b ν ν' ν'' hb hβ hinj hfl hν hν' hlev hfin hsurj using key
  refine ⟨{
    Z := C.Z, s := C.s, normal := C.normal, proj := C.proj, flat := C.flat, t := C.t, qproj := C.qproj
    good := C.good, ga := genericPoints_subset C, a := fun l h => b l h ≫ i ≫ U.ι, m := ν''
    fin := ?_, compat := ?_, sym := ?_, U := U, U_eq := hU, MM := MM, sM := sM, tM := tM, lev := lev
    MM_red := F.red, MM_flat := F.flat, MM_ab := hab, u := u, u_over := hu, u_fin := ufin, u_surj := usurj
    u_gen := ⟨W₀, hW₀, hiso⟩, tU := tU, mU := mU, mM := mM, lev_eq := ?_, sieg := hS }, ⟨C.amp⟩⟩
  · intro l h β' hβ'
    obtain rfl := eq_of_isInc (hβ l h) hβ'
    obtain ⟨f, hf⟩ := exists_finite_lift U C.s sM (spMap (β l h)) u hu W₀.ι i hi hi'
      (hgen _ (hinj l h) _ _ pullback.condition) (b l h) (Xo l).s (hb l h) (hfin l h) (hsurj l h)
    exact ⟨_, f, by rw [← hU]; rfl, hf⟩
  · intro l l' h h' r κ k hk hr hκ
    have hkβ : k.comp (β l h) = β l' h' :=
      eq_of_isInc (i := (RZ H n N).subtype) (fun x => (hk _).trans (hβ l h x)) (hβ l' h')
    obtain ⟨κ', hκ'⟩ := comp_of_eq (ν l h) κ rfl
    have := hfl l' h'
    obtain ⟨e₁, e₂⟩ := eq_of_level hL h3 hodd F h' (Xo l') (hβ l' h') κ' (ν l' h')
      (by rw [Category.assoc, hb, reassoc_of% hr, spMap_comp, hkβ]) (hb l' h')
      (fun x => by rw [hκ', reassoc_of% hκ x, hlev, Category.assoc r]) (hlev l' h')
    have e₃ : r ≫ b l h = b l' h' := by rwa [← cancel_mono W₀.ι, Category.assoc]
    refine ⟨by rw [reassoc_of% e₃], ?_⟩
    have e₄ : κ.φ ≫ (ν' l h).φ = (ν' l' h').φ := by
      apply mM.cart.1.hom_ext
      · rw [Category.assoc]
        exact (congrArg (κ.φ ≫ ·) (hν l h).symm).trans (hκ'.symm.trans (e₂.trans (hν l' h')))
      · rw [Category.assoc, (ν' l h).cart.1.w, (ν' l' h').cart.1.w, reassoc_of% κ.cart.1.w, reassoc_of% e₃]
    rw [hν', hν', reassoc_of% e₄]
  · intro l h r κ g σ hσ hr hκ
    obtain ⟨ρ, mu, σ₀, h₁, h₂, -⟩ := GlobalTheory.T.fullLevelChange_acts_on_unitaryFamily hL hL2 E H D n N MM sM tM lev l (Xo l) (β l h) _ (ν l h) (hb l h) r κ g σ
      hD h hn.1 hn.2.1 hN (hβ l h) F (hsurj l h) (hlev l h) hσ hr hκ
    obtain ⟨W', e₁, e₂, τ, hd, he, hτ⟩ := exists_iso C hH (exists_inc hn.1 hN l h).1 hft ρ mu σ₀ h₂
    obtain ⟨j', hj'⟩ : ∃ j', j' ≫ U.ι = C.j :=
      ⟨_, IsOpenImmersion.lift_fac U.ι C.j (by rw [Scheme.Opens.range_ι, hU]; exact range_j_subset C)⟩
    have hju := hj j' hj'
    have := isSeparated C
    have := isReduced_of_normal C.normal
    rw [← hj'] at hd hτ
    refine ⟨τ, ?_⟩
    rw [← Category.assoc r.hom]
    exact comp_eq_of_dense U.ι u W₀.ι i hi hi' j' e₁ e₂ ρ (by rw [reassoc_of% hju, hju, he]) τ.hom hτ _ _
      (by simpa only [Category.assoc] using h₁)
  · intro l h a' x y ha hy
    have e : a' = b l h ≫ i := by rw [← cancel_mono U.ι, ha, Category.assoc]
    have : Mono mU.φ := MorphismProperty.of_isPullback (P := .monomorphisms _) mU.cart.1.flip
      (inferInstanceAs (Mono U.ι))
    have e' : y = ((Xo l).univ.etaA x).left ≫ (ν' l h).φ := by
      rw [← cancel_mono mU.φ, hy, hν', Category.assoc]
    rw [e', Category.assoc, ← hν, hlev, e, Category.assoc, Category.assoc, reassoc_of% hi]

end GlobalTheory.TopOfFamily
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fullLevel_model_of_family_birationalModel : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)) (m : ℕ) (C : ZOn sM tM m), 1 ≤ D.p + D.q → AuxiliaryInertOddPrime H n → (∃ j, 1 ≤ j ∧ N = n ^ j) → 0 < m → FamCore D sM tM lev → SiegClause D sM tM lev → ∃ T : Top Xo n N, Nonempty (GlobalTheory.LN.AmpFrames T.t.G T.t.PP.L (m ^ 2)) := by
  atlas_forward_decl GlobalTheory.TopOfFamily.exists_top
end
