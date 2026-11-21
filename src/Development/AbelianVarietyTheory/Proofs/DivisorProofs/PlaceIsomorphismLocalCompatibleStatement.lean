import Mathlib
import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsTheRecOfIsRecLit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIrrGLTransportAlongFieldIsoStatement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClassStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceGoodSignature
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSplitPlaceEqFixedTypePrimePlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceEqConjugatePlaceAndEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportIrrGLBijectiveDegreeCharZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsTransport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds

section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.KOneTransport

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

def intMap (i : k ≃+* k') (hv : ∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1) : 𝒪[k] →+* 𝒪[k'] :=
  (i.toRingHom.comp (𝒪[k]).subtype).codRestrict 𝒪[k'] fun x => (hv x).2 x.2

theorem intMap_coe (i : k ≃+* k') (hv : ∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1) (x : 𝒪[k]) :
    ((intMap i hv x : 𝒪[k']) : k') = i x := rfl

theorem symm_hv (i : k ≃+* k') (hv : ∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1) :
    ∀ y : k', valuation k (i.symm y) ≤ 1 ↔ valuation k' y ≤ 1 := fun y => by
  have := hv (i.symm y); rw [RingEquiv.apply_symm_apply] at this; exact this.symm

theorem isLocalHom_intMap (i : k ≃+* k') (hv : ∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1) :
    IsLocalHom (intMap i hv) := by
  refine ⟨fun a ha => ?_⟩
  have h := ha.map (intMap i.symm (symm_hv i hv))
  have e : intMap i.symm (symm_hv i hv) (intMap i hv a) = a := Subtype.ext (by
    rw [intMap_coe, intMap_coe, RingEquiv.symm_apply_apply])
  rwa [e] at h

theorem map_mem_kOne (i : k ≃+* k') (hv : ∀ x : k, valuation k' (i x) ≤ 1 ↔ valuation k x ≤ 1) {n : ℕ}
    {g : GL (Fin n) k} (hg : g ∈ GlobalTheory.SplitWeil.KOne k (Fin n)) :
    GeneralLinearGroup.map i.toRingHom g ∈ GlobalTheory.SplitWeil.KOne k' (Fin n) := by
  haveI := isLocalHom_intMap i hv
  obtain ⟨g0, hg0, rfl⟩ := Subgroup.mem_map.1 hg
  refine Subgroup.mem_map.2 ⟨GeneralLinearGroup.map (intMap i hv) g0, ?_, ?_⟩
  · rw [MonoidHom.mem_ker] at hg0 ⊢
    ext a b
    have h := congrArg (fun m : GL (Fin n) (IsLocalRing.ResidueField 𝒪[k]) => (m.val : Matrix (Fin n) (Fin n) _) a b) hg0
    simp only [GeneralLinearGroup.map_apply, Units.val_one] at h ⊢
    rw [← IsLocalRing.ResidueField.map_residue, h]
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  · ext a b
    simp [GeneralLinearGroup.map_apply]
    rfl

end GlobalTheory.KOneTransport

open GlobalTheory.LocLanglands.FieldCompat GlobalTheory.LocLanglands.TransportGL in

theorem GlobalTheory.KOneTransport.fixed_ne_bot_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (x : IrrGL k) (x' : IrrGL k'), RepRel i x x' → GlobalTheory.PRep.fixed x.rep (GlobalTheory.SplitWeil.KOne k (Fin x.1)) ≠ ⊥ → GlobalTheory.PRep.fixed x'.rep (GlobalTheory.SplitWeil.KOne k' (Fin x'.1)) ≠ ⊥ := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi x x' H hx
  obtain ⟨-, hv, -⟩ := GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation k k' i hi
  rw [← cls_rep x] at H
  obtain ⟨π', e, rfl, he⟩ := GlobalTheory.TheRecTransport.exists_of_repRel _ H
  obtain ⟨v, hv0, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hx
  let φ := equivRep π'
  have h2 : ∀ g v, φ.toLinearEquiv (π'.ρ g v) = π'.cl.rep.ρ g (φ.toLinearEquiv v) := fun g v =>
    φ.toIntertwiningMap.isIntertwining _ _ g v
  rw [Submodule.ne_bot_iff]
  refine ⟨φ.toLinearEquiv (e v), fun h => ?_, ?_⟩
  · have hg : GeneralLinearGroup.map i.symm.toRingHom (h : GL (Fin x.1) k') ∈ GlobalTheory.SplitWeil.KOne k (Fin x.1) :=
      GlobalTheory.KOneTransport.map_mem_kOne i.symm (GlobalTheory.KOneTransport.symm_hv i hv) h.2
    have hfx : x.rep (GeneralLinearGroup.map i.symm.toRingHom (h : GL (Fin x.1) k')) v = v := by
      have := hv0 ⟨_, hg⟩
      simpa using this
    have h3 := he (GeneralLinearGroup.map i.symm.toRingHom (h : GL (Fin x.1) k')) v
    rw [map_map_symm] at h3
    show π'.cl.rep.ρ (h : GL (Fin x.1) k') (φ.toLinearEquiv (e v)) = ((1 : _ →* ℂˣ) h : ℂ) • φ.toLinearEquiv (e v)
    rw [← h2, ← h3]
    erw [hfx]
    simp
  · intro h0
    apply hvne
    have : e v = 0 := φ.toLinearEquiv.map_eq_zero_iff.1 h0
    exact e.map_eq_zero_iff.1 this
end
end

section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruence_fixedVectors_ne_bot_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (x : IrrGL k) (x' : IrrGL k'), RepRel i x x' → GlobalTheory.PRep.fixed x.rep (GlobalTheory.SplitWeil.KOne k (Fin x.1)) ≠ ⊥ → GlobalTheory.PRep.fixed x'.rep (GlobalTheory.SplitWeil.KOne k' (Fin x'.1)) ≠ ⊥ := by
  first | (exact @GlobalTheory.KOneTransport.fixed_ne_bot_transport) | (exact GlobalTheory.KOneTransport.fixed_ne_bot_transport) | (intros; apply GlobalTheory.KOneTransport.fixed_ne_bot_transport  <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LocLanglands GlobalTheory.WeilDeligne GlobalTheory.LocGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TameTransport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {A : ValuationSubring Ω} {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω']
  {A' : ValuationSubring Ω'} {φ : Ω ≃+* Ω'}

theorem val_lt_val_iff (hm : ∀ z, φ z ∈ A' ↔ z ∈ A) (a b : Ω) (hb : b ≠ 0) :
    A'.valuation (φ a) < A'.valuation (φ b) ↔ A.valuation a < A.valuation b := by
  have hb' : φ b ≠ 0 := (map_ne_zero φ).mpr hb
  have h1 : A'.valuation (φ b) ≠ 0 := by simpa using hb'
  have h2 : A.valuation b ≠ 0 := by simpa using hb
  have e1 : A'.valuation (φ a) < A'.valuation (φ b) ↔ A'.valuation (φ (a / b)) < 1 := by
    rw [map_div₀, map_div₀, div_lt_one₀ (zero_lt_iff.mpr h1)]
  have e2 : A.valuation a < A.valuation b ↔ A.valuation (a / b) < 1 := by
    rw [map_div₀, div_lt_one₀ (zero_lt_iff.mpr h2)]
  rw [e1, e2, GlobalTheory.WeilTransport.val_lt_one_iff hm]

theorem isWild_of_rel (hm : ∀ z, φ z ∈ A' ↔ z ∈ A) {σ : G E Ω} {σ' : G E' Ω'}
    (hrel : ∀ z, φ (σ z) = σ' (φ z)) (hσ : Formalism.MainNotions.BlochKatoReduction.IsWild A σ) : Formalism.MainNotions.BlochKatoReduction.IsWild A' σ' := by
  obtain ⟨⟨hdec, hin⟩, hw⟩ := hσ
  refine ⟨⟨(GlobalTheory.WeilTransport.mem_Dec_iff hm hrel).mpr hdec, fun x hx => ?_⟩, fun x hx => ?_⟩
  · obtain ⟨z, rfl⟩ := φ.surjective x
    rw [GlobalTheory.WeilTransport.val_le_one_iff hm] at hx
    rw [← hrel, ← map_sub, GlobalTheory.WeilTransport.val_lt_one_iff hm]
    exact hin z hx
  · obtain ⟨z, rfl⟩ := φ.surjective x
    have hz : z ≠ 0 := by rintro rfl; exact hx (map_zero φ)
    rw [← hrel, ← map_sub, val_lt_val_iff hm _ _ hz]
    exact hw z hz

end GlobalTheory.TameTransport
end

section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.TameTransport in
theorem GlobalTheory.LocLanglands.isTameWD_of_wdRel_refl : ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E Ω] [Algebra E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (w' : HeightOneSpectrum (𝓞 E')) (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), GlobalTheory.LocLanglands.PlaceIso A w A w' (RingEquiv.refl Ω) j i → ∀ (y : WD h) (y' : WD h'), WDRel (RingEquiv.refl Ω) y y' → IsTameWD y → IsTameWD y' := by
  intro E E' Ω _ _ _ _ _ _ _ _ _ A w w' h h' j i hP y y' hrel hy
  obtain ⟨n, b, b', hb, hb', -, hρ⟩ := hrel
  obtain ⟨m, a, ha, hwild⟩ := hy
  obtain ⟨e, he, -⟩ := GlobalTheory.WeilDeligne.WD.mk_eq_mk.mp (ha.trans hb.symm)
  obtain ⟨c, hc, -⟩ := GlobalTheory.T.place_over_transport_ring_iso E Ω A w h E' Ω A w' h' (RingEquiv.refl Ω) j i hP
  refine ⟨n, b', hb', fun σ' hσ' => ?_⟩
  have hr : WeilRel (RingEquiv.refl Ω) (c.symm σ') σ' := (hc (c.symm σ') σ').mpr (by simp)
  have hσ : Formalism.MainNotions.BlochKatoReduction.IsWild A ((c.symm σ' : Weil h) : G E Ω) :=
    isWild_of_rel (φ := RingEquiv.refl Ω) (fun _ => Iff.rfl) (fun z => ?_) hσ'
  · rw [← hρ _ σ' hr]
    refine LinearMap.ext fun v => ?_
    obtain ⟨u, rfl⟩ := e.surjective v
    rw [← he, hwild _ hσ]
    rfl
  · have := hr z
    simpa using this.symm
end

section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_iso_compatible_local_langlands_one : ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E Ω] [Algebra E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (w' : HeightOneSpectrum (𝓞 E')) (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), GlobalTheory.LocLanglands.PlaceIso A w A w' (RingEquiv.refl Ω) j i → ∀ (y : WD h) (y' : WD h'), WDRel (RingEquiv.refl Ω) y y' → IsTameWD y → IsTameWD y' := by
  first | (exact @GlobalTheory.LocLanglands.isTameWD_of_wdRel_refl) | (exact GlobalTheory.LocLanglands.isTameWD_of_wdRel_refl) | (intros; apply GlobalTheory.LocLanglands.isTameWD_of_wdRel_refl  <;> assumption)
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LocLanglands GlobalTheory.WeilDeligne GlobalTheory.LocGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypeLawTransport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
  {φ : Ω ≃+* Ω'} {j : E →+* E'} {i : w.adicCompletion E ≃+* w'.adicCompletion E'}

theorem monodromy_vanishing_iff_of_weil_deligne_rel {y : WD h} {y' : WD h'} (H : WDRel φ y y') : y.mono0 ↔ y'.mono0 := by
  obtain ⟨n, b, b', rfl, rfl, hN, -⟩ := H
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff, WD.monodromyZero_ofWeilDeligneRepClass_iff, hN]

theorem inePol_transport (P : PlaceIso A w A' w' φ j i) {y : WD h} {y' : WD h'} (H : WDRel φ y y')
    {σ : G E Ω} {σ' : G E' Ω'} (hr : ∀ z, φ (σ z) = σ' (φ z)) : y.inePol σ = y'.inePol σ' := by
  obtain ⟨c, -, -, hq, -⟩ := GlobalTheory.WeilTransport.weil_equiv E Ω A w h E' Ω' A' w' h' φ j i P
  have hmem : σ' ∈ Weil h' ↔ σ ∈ Weil h := by
    rw [mem_Weil, mem_Weil, hq]
    exact exists_congr fun a => exists_congr fun b => GlobalTheory.WeilTransport.actsAs_iff P.mem hr _ a b
  obtain ⟨n, b, b', rfl, rfl, -, hb⟩ := H
  by_cases hσ : σ ∈ Weil h
  · have hσ' := hmem.2 hσ
    rw [WD.inePol_of_mem _ hσ, WD.inePol_of_mem _ hσ', WD.charPol_mk, WD.charPol_mk, hb ⟨σ, hσ⟩ ⟨σ', hσ'⟩ hr]
  · have hσ' : σ' ∉ Weil h' := fun h1 => hσ (hmem.1 h1)
    rw [WD.inePol_of_not_mem _ hσ, WD.inePol_of_not_mem _ hσ']

end GlobalTheory.TypeLawTransport

end
end

section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.TypeLawTransport

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.TypeLawTransport.typeLaw_transport_fwd : ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E Ω] [Algebra E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (w' : HeightOneSpectrum (𝓞 E')) (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), GlobalTheory.LocLanglands.PlaceIso A w A w' (RingEquiv.refl Ω) j i → ∀ (rc : IrrGL (w.adicCompletion E) → WD h) (rc' : IrrGL (w'.adicCompletion E') → WD h'), (∀ x x', RepRel i x x' → WDRel (RingEquiv.refl Ω) (rc x) (rc' x')) → UpperTheory.Zero.LLC.TypeLaw h rc → UpperTheory.Zero.LLC.TypeLaw h' rc' := by
  intro E E' Ω _ _ _ _ _ _ _ _ _ A w w' h h' j i P rc rc' hrel hT
  intro E'' _ _ _ _ _ _ g _ w'' h'' ii hii n hn hg hnorm a'' ha'' K _ _ red hred hker θ hθ τ hτ hτc σ' hσ'
  letI iE : Algebra E E'' := ((algebraMap E' E'').comp j).toAlgebra
  haveI : IsScalarTower E E'' Ω := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap E Ω x = algebraMap E'' Ω (algebraMap E' E'' (j x))
    rw [← IsScalarTower.algebraMap_apply]
    exact P.ext x
  haveI := GlobalTheory.LocLanglands.FieldCompat.charZero_compl w
  haveI := GlobalTheory.LocLanglands.FieldCompat.charZero_compl w'
  have hs : Continuous i.symm := (GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation _ _ i P.cont).1
  have hcont : Continuous (ii.trans i.symm) := hs.comp hii
  obtain ⟨T, hT1, -⟩ := GlobalTheory.transport_irrGL_bijective _ _ i.symm hs
  obtain ⟨σ₀, e, h2, he⟩ := GlobalTheory.TheRecTransport.exists_of_repRel σ' ((hT1 _ _).2 rfl)
  have hR' : RepRel i.symm (cls σ') (cls σ₀) := h2 ▸ (hT1 _ _).2 rfl
  have hR : RepRel i (cls σ₀) (cls σ') := GlobalTheory.LocLanglands.FieldCompat.repRel_symm hR'
  have W := hrel _ _ hR
  have hinf : GlobalTheory.SerSys.TameGen.Inflates (σ₀.ρ.comp (Matrix.GeneralLinearGroup.map (ii.trans i.symm).toRingHom)) τ := by
    obtain ⟨f, hf0, hf⟩ := hσ'
    refine ⟨e.toLinearMap ∘ₗ f, fun h0 => hf0 ?_, fun k v => ?_⟩
    · ext v
      have := congrArg (fun F => F v) h0
      simpa using this
    · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, MonoidHom.comp_apply] at hf ⊢
      rw [hf, he]
      rfl
  obtain ⟨hm, hp⟩ := hT E'' g w'' h'' (ii.trans i.symm) hcont n hn hg hnorm a'' ha'' K red hred hker θ hθ τ hτ hτc σ₀ hinf
  refine ⟨(monodromy_vanishing_iff_of_weil_deligne_rel W).1 hm, fun t x z hxz hv => ?_⟩
  rw [← hp t x z hxz hv]
  exact (inePol_transport P W fun _ => rfl).symm
end

section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_iso_compatible_local_langlands_two : ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E Ω] [Algebra E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (w' : HeightOneSpectrum (𝓞 E')) (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), GlobalTheory.LocLanglands.PlaceIso A w A w' (RingEquiv.refl Ω) j i → ∀ (rc : IrrGL (w.adicCompletion E) → WD h) (rc' : IrrGL (w'.adicCompletion E') → WD h'), (∀ x x', RepRel i x x' → WDRel (RingEquiv.refl Ω) (rc x) (rc' x')) → UpperTheory.Zero.LLC.TypeLaw h rc → UpperTheory.Zero.LLC.TypeLaw h' rc' := by
  first | (exact @GlobalTheory.TypeLawTransport.typeLaw_transport_fwd) | (exact GlobalTheory.TypeLawTransport.typeLaw_transport_fwd) | (intros; apply GlobalTheory.TypeLawTransport.typeLaw_transport_fwd  <;> assumption)
end

section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LawsTTransport

open GlobalTheory.LocLanglands.FieldCompat GlobalTheory.LocLanglands.TransportGL

theorem lawsA_transport : ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E Ω] [Algebra E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (w' : HeightOneSpectrum (𝓞 E')) (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), GlobalTheory.LocLanglands.PlaceIso A w A w' (RingEquiv.refl Ω) j i → ∀ (rc : IrrGL (w.adicCompletion E) → WD h) (rc' : IrrGL (w'.adicCompletion E') → WD h'), (∀ x x', RepRel i x x' → WDRel (RingEquiv.refl Ω) (rc x) (rc' x')) → ∀ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a), UpperTheory.Zero.LLC.LawsT a ha rc → ∀ (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a'), (∀ x, (rc' x).lpDim = x.1) ∧ (∀ χ hχ, rc' (.ofChar χ hχ) = WD.lpOfChar h' (χ.comp a') (ha'.smooth hχ)) ∧ (∀ (l : List (Segment (w'.adicCompletion E'))) (x : IrrGL (w'.adicCompletion E')), IsL (l : Multiset (Segment (w'.adicCompletion E'))) x.rep → rc' x = segSum rc' l) ∧ (∀ x, x.IsCusp → IsIrrWD (rc' x)) ∧ (∀ x (s : ℝ), rc' (x.nu s) = (rc' x).lpTw s) := by
  intro E E' Ω _ _ _ _ _ _ _ _ _ A w w' h h' j i P rc rc' hR a ha L a' ha'
  have hG := GlobalTheory.globalArtinReciprocity_holds
  have hC := GlobalTheory.Published.chevalleyUnits'
  have h3 := P.cont
  have := charZero_compl w
  have := charZero_compl w'
  have hs : Continuous i.symm := (GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation _ _ i h3).1
  obtain ⟨T, hT, hTd⟩ := GlobalTheory.T.transportIrrGL_bijective_degree_charZero _ _ i h3
  obtain ⟨hcu, hch⟩ := GlobalTheory.T.transport_keeps_cuspidal_twists_characters _ _ i h3
  obtain ⟨S, hS, hSd, hS0, hSs, hSc, hSt, hSp, hSi, hSo⟩ :=
    GlobalTheory.T.place_over_transport_ring_iso_symm E Ω A w h E' Ω A w' h' (RingEquiv.refl Ω) j i P
  have hart := GlobalTheory.T.localArtinMap_unique_transport_placeIso hG hC E Ω A w h E' Ω A w' h' (RingEquiv.refl Ω) j i P a a' ha ha'
  have hrel : ∀ x', RepRel i (T.symm x') x' := fun x' => (hT _ _).2 (T.apply_symm_apply x')
  have key : ∀ x', rc' x' = S (rc (T.symm x')) := fun x' => ((hS _ _).1 (hR _ _ (hrel x'))).symm
  have hcusp : ∀ x', (T.symm x').IsCusp ↔ x'.IsCusp := fun x' => (hcu _ _ (hrel x')).1
  refine ⟨fun x' => ?_, fun χ' hχ' => ?_, fun l x' hx => ?_, fun x' hx => ?_, fun x' s => ?_⟩
  · rw [key, hSd, L.dim, ← hTd, T.apply_symm_apply]
  · have hχ := isSmoothChar_comp i h3 hχ'
    have R := hch _ hχ χ' hχ' (fun _ => rfl)
    rw [key, ← (hT _ _).1 R, T.symm_apply_apply, L.one]
    refine hSo _ _ _ _ fun σ σ' hσ => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, hart σ σ' hσ]
  · let f : Segment (w'.adicCompletion E') → Segment (w.adicCompletion E) := fun Δ =>
      Segment.ofFirst (T.symm Δ.first) ((hcusp _).2 Δ.isCusp_first) Δ.len Δ.len_pos
    have hl := GlobalTheory.T.isLanglandsData_transport_localFieldIso _ _ i.symm hs l (l.map f) x' (T.symm x')
      (by rw [List.forall₂_map_right_iff, List.forall₂_same]; exact fun Δ _ => ⟨repRel_symm (hrel _), rfl⟩)
      (repRel_symm (hrel x')) hx
    rw [key, L.langlands _ _ hl]
    clear hl hx
    induction l with
    | nil => exact hS0
    | cons Δ l ih =>
      simp only [segSum, sumList, List.map_cons, List.foldr_cons] at ih ⊢
      rw [hSs, ih, hSc, hSt, hSp, show (f Δ).first = T.symm Δ.first from rfl,
        show (f Δ).len = Δ.len from rfl, ← key]
  · rw [key, hSi]
    exact L.cusp _ ((hcusp x').2 hx)
  · have R : RepRel i ((T.symm x').nu s) (x'.nu s) := (hcu _ _ (hrel x')).2 s
    rw [key, ← (hT _ _).1 R, T.symm_apply_apply, L.nu, hSt, ← key]

end GlobalTheory.LawsTTransport

end
end

section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_iso_compatible_local_langlands_three : ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E Ω] [Algebra E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (w' : HeightOneSpectrum (𝓞 E')) (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), GlobalTheory.LocLanglands.PlaceIso A w A w' (RingEquiv.refl Ω) j i → ∀ (rc : IrrGL (w.adicCompletion E) → WD h) (rc' : IrrGL (w'.adicCompletion E') → WD h'), (∀ x x', RepRel i x x' → WDRel (RingEquiv.refl Ω) (rc x) (rc' x')) → ∀ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a), UpperTheory.Zero.LLC.LawsT a ha rc → ∀ (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a'), (∀ x, (rc' x).lpDim = x.1) ∧ (∀ χ hχ, rc' (.ofChar χ hχ) = WD.lpOfChar h' (χ.comp a') (ha'.smooth hχ)) ∧ (∀ (l : List (Segment (w'.adicCompletion E'))) (x : IrrGL (w'.adicCompletion E')), IsL (l : Multiset (Segment (w'.adicCompletion E'))) x.rep → rc' x = segSum rc' l) ∧ (∀ x, x.IsCusp → IsIrrWD (rc' x)) ∧ (∀ x (s : ℝ), rc' (x.nu s) = (rc' x).lpTw s) := by
  first | (exact @GlobalTheory.LawsTTransport.lawsA_transport) | (exact GlobalTheory.LawsTTransport.lawsA_transport) | (intros; apply GlobalTheory.LawsTTransport.lawsA_transport  <;> assumption)
end

section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.LocLanglands.FieldCompat GlobalTheory.LocLanglands.TransportGL GlobalTheory.TheRecTransport

namespace GlobalTheory.LawsTTransport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}

theorem eig_of_wdRel {φ : Ω ≃+* Ω'} {y : WD h} {y' : WD h'} (H : WDRel φ y y') {σ : Weil h} {σ' : Weil h'}
    (hσ : WeilRel φ σ σ') : y.eig σ = y'.eig σ' := by
  obtain ⟨n, b, b', e1, e2, -, hb⟩ := H
  rw [← e1, ← e2, WD.eig, WD.eig, WD.charPol_mk, WD.charPol_mk, hb σ _ hσ]

end GlobalTheory.LawsTTransport

theorem GlobalTheory.LawsTTransport.lawsT_transport : ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E Ω] [Algebra E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (w' : HeightOneSpectrum (𝓞 E')) (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), GlobalTheory.LocLanglands.PlaceIso A w A w' (RingEquiv.refl Ω) j i → ∀ (rc : IrrGL (w.adicCompletion E) → WD h) (rc' : IrrGL (w'.adicCompletion E') → WD h'), (∀ x x', RepRel i x x' → WDRel (RingEquiv.refl Ω) (rc x) (rc' x')) → (∀ x x', RepRel i x x' → (UpperTheory.Zero.LLC.Good x ↔ UpperTheory.Zero.LLC.Good x')) → ∀ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a), UpperTheory.Zero.LLC.LawsT a ha rc → ∀ (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a'), (∀ (x : IrrGL (w'.adicCompletion E')) ω, HasCentralChar x.rep ω → ∀ σ, ‖((rc' x).eig σ).prod‖ = ‖(ω (a' σ) : ℂ)‖) ∧ (∀ x χ hχ, UpperTheory.Zero.LLC.Good x → rc' (x.tw χ hχ) = (rc' x).lpChar (rc' (.ofChar χ hχ))) ∧ (∀ (x : IrrGL (w'.adicCompletion E')) ω, UpperTheory.Zero.LLC.Good x → HasCentralChar x.rep ω → ∀ σ, ((rc' x).eig σ).prod = (ω (a' σ) : ℂ)) ∧ (∀ (n : ℕ) (π π' : IrrRep (GL (Fin n) (w'.adicCompletion E'))), UpperTheory.Zero.LLC.Good (cls π) → Nonempty (π'.ρ.Equiv (contra π.ρ)) → rc' (cls π') = (rc' (cls π)).lpDual) ∧ (∀ x y, UpperTheory.Zero.LLC.Good y → rc' x = rc' y → x = y) := by
  intro E E' Ω _ _ _ _ _ _ _ _ _ A w w' h h' j i P rc rc' hR hG a ha L a' ha'
  have h3 := P.cont
  have := charZero_compl w
  have := charZero_compl w'
  have hs : Continuous i.symm := (GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation _ _ i h3).1
  obtain ⟨T, hT, -⟩ := GlobalTheory.T.transportIrrGL_bijective_degree_charZero _ _ i h3
  obtain ⟨-, hch⟩ := GlobalTheory.T.transport_keeps_cuspidal_twists_characters _ _ i h3
  obtain ⟨S, hS, -, -, -, hSc, -⟩ := GlobalTheory.T.place_over_transport_ring_iso_symm E Ω A w h E' Ω A w' h' (RingEquiv.refl Ω) j i P
  obtain ⟨c, hc, -⟩ := GlobalTheory.T.place_over_transport_ring_iso E Ω A w h E' Ω A w' h' (RingEquiv.refl Ω) j i P
  have hart := GlobalTheory.T.localArtinMap_unique_transport_placeIso GlobalTheory.globalArtinReciprocity_holds GlobalTheory.Published.chevalleyUnits'
    E Ω A w h E' Ω A w' h' (RingEquiv.refl Ω) j i P a a' ha ha'
  have hRS : ∀ x x', RepRel i x x' → rc' x' = S (rc x) := fun x x' r => ((hS _ _).1 (hR x x' r)).symm
  have hrel : ∀ x', RepRel i (T.symm x') x' := fun x' => (hT _ _).2 (T.apply_symm_apply x')
  have hwd : ∀ y, WDRel (RingEquiv.refl Ω) y (S y) := fun y => (hS _ _).2 rfl
  have hσ : ∀ σ', WeilRel (RingEquiv.refl Ω) (c.symm σ') σ' := fun σ' => (hc _ _).2 (c.apply_symm_apply σ')
  have hv : ∀ (ω : (w'.adicCompletion E')ˣ →* ℂˣ) (z : (w.adicCompletion E)ˣ),
      (ω.comp (Units.map i.symm.symm.toRingHom.toMonoidHom)) z = ω (Units.map i.toRingHom.toMonoidHom z) :=
    fun ω z => rfl

  have heig : ∀ x' σ', (rc' x').eig σ' = (rc (T.symm x')).eig (c.symm σ') := fun x' σ' => by
    rw [hRS _ _ (hrel x')]
    exact (GlobalTheory.LawsTTransport.eig_of_wdRel (hwd _) (hσ σ')).symm
  have hcent : ∀ (x' : IrrGL (w'.adicCompletion E')) ω, HasCentralChar x'.rep ω →
      HasCentralChar (T.symm x').rep (ω.comp (Units.map i.symm.symm.toRingHom.toMonoidHom)) :=
    fun x' ω hω => central_transport i.symm (repRel_symm (hrel x')) hω
  refine ⟨fun x' ω hω σ' => ?_, fun x' χ hχ hg => ?_, fun x' ω hg hω σ' => ?_,
    fun n π π' hg ⟨u₀⟩ => ?_, fun x' y' hg e => ?_⟩
  · rw [heig, L.absCentral _ _ (hcent x' ω hω) (c.symm σ'), hart _ _ (hσ σ'), hv]
  · have hχ0 := isSmoothChar_comp i h3 hχ
    have htw : ∀ x x', RepRel i x x' → RepRel i (x.tw _ hχ0) (x'.tw χ hχ) := by
      rintro x x' ⟨n, π, π', e, rfl, rfl, he⟩
      exact repRel_tw i π π' e he _ hχ0 χ hχ (fun _ => rfl)
    rw [hRS _ _ (htw _ _ (hrel x')), L.twist _ _ _ ((hG _ _ (hrel x')).2 hg), hSc, ← hRS _ _ (hrel x'),
      ← hRS _ _ (hch _ hχ0 χ hχ (fun _ => rfl))]
  · rw [heig, L.central _ _ ((hG _ _ (hrel x')).2 hg) (hcent x' ω hω) (c.symm σ'), hart _ _ (hσ σ'), hv]
  · obtain ⟨π₀, e, h1, he⟩ := exists_of_repRel π (repRel_symm (hrel (cls π)))
    obtain ⟨π₀', u, h2, hu⟩ := exists_of_repRel π' (repRel_symm (hrel (cls π')))
    have r1 : RepRel i (cls π₀) (cls π) := h1 ▸ hrel (cls π)
    have r2 : RepRel i (cls π₀') (cls π') := h2 ▸ hrel (cls π')
    rw [hRS _ _ r2, hRS _ _ r1, ← equiv_lpDual P S hS,
      L.dual n π₀ π₀' ((hG _ _ r1).2 hg) (contra_transport i.symm hs h3 π π' π₀ π₀' e he u hu u₀)]
  · have e2 : rc (T.symm x') = rc (T.symm y') := by
      apply S.injective
      rw [← hRS _ _ (hrel x'), ← hRS _ _ (hrel y'), e]
    exact T.symm.injective (L.inj _ _ ((hG _ _ (hrel y')).2 hg) e2)
end

section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_iso_compatible_local_langlands_four : ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E Ω] [Algebra E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (w' : HeightOneSpectrum (𝓞 E')) (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), GlobalTheory.LocLanglands.PlaceIso A w A w' (RingEquiv.refl Ω) j i → ∀ (rc : IrrGL (w.adicCompletion E) → WD h) (rc' : IrrGL (w'.adicCompletion E') → WD h'), (∀ x x', RepRel i x x' → WDRel (RingEquiv.refl Ω) (rc x) (rc' x')) → (∀ x x', RepRel i x x' → (UpperTheory.Zero.LLC.Good x ↔ UpperTheory.Zero.LLC.Good x')) → ∀ (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a), UpperTheory.Zero.LLC.LawsT a ha rc → ∀ (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a'), (∀ (x : IrrGL (w'.adicCompletion E')) ω, HasCentralChar x.rep ω → ∀ σ, ‖((rc' x).eig σ).prod‖ = ‖(ω (a' σ) : ℂ)‖) ∧ (∀ x χ hχ, UpperTheory.Zero.LLC.Good x → rc' (x.tw χ hχ) = (rc' x).lpChar (rc' (.ofChar χ hχ))) ∧ (∀ (x : IrrGL (w'.adicCompletion E')) ω, UpperTheory.Zero.LLC.Good x → HasCentralChar x.rep ω → ∀ σ, ((rc' x).eig σ).prod = (ω (a' σ) : ℂ)) ∧ (∀ (n : ℕ) (π π' : IrrRep (GL (Fin n) (w'.adicCompletion E'))), UpperTheory.Zero.LLC.Good (cls π) → Nonempty (π'.ρ.Equiv (contra π.ρ)) → rc' (cls π') = (rc' (cls π)).lpDual) ∧ (∀ x y, UpperTheory.Zero.LLC.Good y → rc' x = rc' y → x = y) := by
  first | (exact @GlobalTheory.LawsTTransport.lawsT_transport) | (exact GlobalTheory.LawsTTransport.lawsT_transport) | (intros; apply GlobalTheory.LawsTTransport.lawsT_transport  <;> assumption)
end

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.RecTTransport.isRecT_transport : ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E Ω] [Algebra E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (w' : HeightOneSpectrum (𝓞 E')) (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), GlobalTheory.LocLanglands.PlaceIso A w A w' (RingEquiv.refl Ω) j i → ∀ rc : IrrGL (w.adicCompletion E) → WD h, UpperTheory.Zero.LLC.IsRecT h rc → (∃ rc₀ : IrrGL (w'.adicCompletion E') → WD h', UpperTheory.Zero.LLC.IsRecT h' rc₀) → ∃ rc' : IrrGL (w'.adicCompletion E') → WD h', UpperTheory.Zero.LLC.IsRecT h' rc' ∧ ∀ x x', GlobalTheory.LocLanglands.RepRel i x x' → GlobalTheory.LocLanglands.WDRel (RingEquiv.refl Ω) (rc x) (rc' x') := by
  intro E E' Ω _ _ _ _ _ _ _ _ _ A w w' h h' j i P rc hrc hrc₀
  obtain ⟨rc₀, a', ha', -⟩ := hrc₀
  have := FieldCompat.charZero_compl w
  have := FieldCompat.charZero_compl w'
  have hs : Continuous i.symm := (GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation _ _ i P.cont).1
  obtain ⟨T, hT, -⟩ := GlobalTheory.T.transportIrrGL_bijective_degree_charZero _ _ i P.cont
  obtain ⟨S, hS, -⟩ := GlobalTheory.T.place_over_transport_ring_iso_symm E Ω A w h E' Ω A w' h' (RingEquiv.refl Ω) j i P
  obtain ⟨a, ha, H⟩ := hrc
  have hR : ∀ x x', RepRel i x x' → WDRel (RingEquiv.refl Ω) (rc x) ((fun x' => S (rc (T.symm x'))) x') :=
    fun x x' hx => (hS _ _).2 (by rw [← (hT _ _).1 hx]; exact congrArg (fun z => S (rc z)) (T.symm_apply_apply x).symm)
  have hG : ∀ x x', RepRel i x x' → (UpperTheory.Zero.LLC.Good x ↔ UpperTheory.Zero.LLC.Good x') := fun x x' hx =>
    ⟨GlobalTheory.T.good_irrGL_transport_along_fieldIso _ _ i P.cont x x' hx,
      GlobalTheory.T.good_irrGL_transport_along_fieldIso _ _ i.symm hs x' x (FieldCompat.repRel_symm hx)⟩
  obtain ⟨l1, l2, l3, l4, l5⟩ := GlobalTheory.T.place_iso_compatible_local_langlands_three E E' Ω A w w' h h' j i P rc _ hR a ha H a' ha'
  obtain ⟨m1, m2, m3, m4, m5⟩ := GlobalTheory.T.place_iso_compatible_local_langlands_four E E' Ω A w w' h h' j i P rc _ hR hG a ha H a' ha'
  refine ⟨fun x' => S (rc (T.symm x')), ⟨a', ha', ⟨l1, l2, l3, l4, l5, m1, m2, m3, m4, m5, fun x' hg hf => ?_,
    GlobalTheory.T.place_iso_compatible_local_langlands_two E E' Ω A w w' h h' j i P rc _ hR H.type⟩⟩, hR⟩
  have hx : RepRel i (T.symm x') x' := (hT _ _).2 (T.apply_symm_apply x')
  have hx' := FieldCompat.repRel_symm hx
  refine GlobalTheory.T.place_iso_compatible_local_langlands_one E E' Ω A w w' h h' j i P _ _ (hR _ _ hx) (H.depth _ ?_ ?_)
  · exact GlobalTheory.T.good_irrGL_transport_along_fieldIso _ _ i.symm hs _ _ hx' hg
  · exact GlobalTheory.T.principalCongruence_fixedVectors_ne_bot_transport _ _ i.symm hs _ _ hx' hf

end
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_isomorphism_local_compatible : ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E Ω] [Algebra E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (w' : HeightOneSpectrum (𝓞 E')) (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), GlobalTheory.LocLanglands.PlaceIso A w A w' (RingEquiv.refl Ω) j i → ∀ rc : IrrGL (w.adicCompletion E) → WD h, UpperTheory.Zero.LLC.IsRecT h rc → (∃ rc₀ : IrrGL (w'.adicCompletion E') → WD h', UpperTheory.Zero.LLC.IsRecT h' rc₀) → ∃ rc' : IrrGL (w'.adicCompletion E') → WD h', UpperTheory.Zero.LLC.IsRecT h' rc' ∧ ∀ x x', GlobalTheory.LocLanglands.RepRel i x x' → GlobalTheory.LocLanglands.WDRel (RingEquiv.refl Ω) (rc x) (rc' x') := by
  first | (exact @GlobalTheory.RecTTransport.isRecT_transport) | (exact GlobalTheory.RecTTransport.isRecT_transport) | (intros; apply GlobalTheory.RecTTransport.isRecT_transport <;> assumption)
end
