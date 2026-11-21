import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionIsDomainAndIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeConditionsCoverModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmplePointsLocalizedModel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorResidueUnramifiedFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationMaximalIdealMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationResidueFiniteUnram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompleteUnramifiedExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionUnramifiedNormal

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GModStalk

theorem charZero_essFiniteType_stalk : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : GMod Xo c) (z : Z.X),
    CharZero (Z.X.presheaf.stalk z) ∧ Algebra.EssFiniteType ℤ (Z.X.presheaf.stalk z) := by
  intro E _ _ _ H D l Xo c Z z
  haveI := c.fin
  haveI : NumberField c.F := {}
  obtain ⟨-, hft, -⟩ := GlobalTheory.CoeffRings.coeff_isDedFrac E H l c
  haveI := GlobalTheory.ThetaDescent.isProper_of_isProjOver Z.proj
  haveI : Flat Z.s := Z.flat
  let y : PrimeSpectrum (𝓞 c.F) := Z.s z
  letI : Algebra (𝓞 c.F) ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z)) := StructureSheaf.stalkAlgebra _ y
  haveI : IsLocalization.AtPrime ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z)) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := algebraMap (𝓞 c.F) ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z))
  have h₁ : (Z.s.stalkMap z).hom.EssFiniteType := LocallyOfFiniteType.stalkMap Z.s z
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  have hφ : Function.Injective φ :=
    IsLocalization.injective ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z)) y.asIdeal.primeCompl_le_nonZeroDivisors
  have hσ : Function.Injective (Z.s.stalkMap z).hom := by
    have h := Flat.stalkMap Z.s z
    algebraize [(Z.s.stalkMap z).hom]
    have : IsLocalHom (algebraMap ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z)) (Z.X.presheaf.stalk z)) :=
      Z.s.toLRSHom.prop z
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := (Sp (𝓞 c.F)).presheaf.stalk (Z.s z))
      (B := Z.X.presheaf.stalk z)
    exact FaithfulSMul.algebraMap_injective ((Sp (𝓞 c.F)).presheaf.stalk (Z.s z)) (Z.X.presheaf.stalk z)
  refine ⟨charZero_of_injective_ringHom (f := (Z.s.stalkMap z).hom.comp φ) (hσ.comp hφ), ?_⟩
  have hO : Algebra.EssFiniteType ℤ (𝓞 c.F) := inferInstance
  refine RingHom.essFiniteType_algebraMap.1 ?_
  convert (RingHom.essFiniteType_algebraMap.2 hO).comp (h₂.comp h₁) using 1
  exact Subsingleton.elim _ _

end GlobalTheory.GModStalk
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalk_charZero_essFiniteType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : GMod Xo c) (z : Z.X), CharZero (Z.X.presheaf.stalk z) ∧ Algebra.EssFiniteType ℤ (Z.X.presheaf.stalk z) := by
  first | exact @GlobalTheory.GModStalk.charZero_essFiniteType_stalk | exact GlobalTheory.GModStalk.charZero_essFiniteType_stalk | (intros; apply GlobalTheory.GModStalk.charZero_essFiniteType_stalk <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem fromSpecStalk_bot_mem_range_j : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : GMod Xo c) (z : Z.X) (p : PrimeSpectrum (Z.X.presheaf.stalk z)),
    p.asIdeal = ⊥ → Z.X.fromSpecStalk z p ∈ Set.range Z.j := by
  intro E _ _ _ H D l Xo c Z z p hp
  haveI := c.fin
  haveI : NumberField c.F := {}
  haveI hdom : IsDomain (Z.X.presheaf.stalk z) := (Z.normal z).1
  have hfl : (Scheme.stalkClosedPointTo (Z.X.fromSpecStalk z)).hom.Flat := by
    rw [Scheme.stalkClosedPointTo_fromSpecStalk]
    exact RingHom.Flat.of_bijective (Iso.commRingCatIsoToRingEquiv _).bijective
  obtain ⟨y, hy⟩ := @DomFine.exists_generic_point (𝓞 c.F) c.F _ _ _ _ _ Z.X (Xo.XF c) Z.s Z.jQ Z.flat Z.proj Z.jQ_open
    Z.jQ_dense (Z.X.presheaf.stalk z) _ hdom _ (Z.X.fromSpecStalk z) hfl
  let w : PrimeSpectrum (FractionRing (Z.X.presheaf.stalk z)) := ⊥
  have hw : (jK (Z.X.presheaf.stalk z)) w = p := by
    apply PrimeSpectrum.ext
    rw [hp]
    show Ideal.comap (algebraMap (Z.X.presheaf.stalk z) (FractionRing (Z.X.presheaf.stalk z))) (⊥ : Ideal _) = ⊥
    rw [← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective _ _)
  refine ⟨y w, ?_⟩
  have e := congrArg (fun f => f w) hy
  simp only [Scheme.Hom.comp_apply] at e
  rw [← hw]
  exact e

end GlobalTheory.TorRef
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_stalk_point_in_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Z : GMod Xo c) (z : Z.X) (p : PrimeSpectrum (Z.X.presheaf.stalk z)), p.asIdeal = ⊥ → Z.X.fromSpecStalk z p ∈ Set.range Z.j := by
  atlas_forward_decl GlobalTheory.TorRef.fromSpecStalk_bot_mem_range_j
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.ChartBir

theorem isIso_stalkMap_j {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Y : GMod Xo c) (u : Xo.XF c) : IsIso (Y.j.stalkMap u) := by
  have hb : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of (𝓞 c.F)) (S := c.F) (nonZeroDivisors (𝓞 c.F))
  have hbf : Flat (spMap (algebraMap (𝓞 c.F) c.F)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat c.F (nonZeroDivisors (𝓞 c.F)))
  have h1 : IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hb
  have h2 : Flat (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback _ _).flip hbf
  haveI := Y.jQ_open
  have i1 : IsIso ((pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).stalkMap (Y.jQ u)) :=
    GlobalTheory.isIso_stalkMap_of_flat_of_surjectiveOnStalks _ _
  have i2 : IsIso (Y.jQ.stalkMap u) := (IsOpenImmersion.iff_isIso_stalkMap.1 inferInstance).2 u
  show IsIso ((Y.jQ ≫ pullback.fst _ _).stalkMap u)
  rw [Scheme.Hom.stalkMap_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ i1 i2

theorem stalkMap_birational : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), Z.j ≫ π = X.j → π ≫ X.s = Z.s →
    ∀ z : Z.X, Function.Injective (π.stalkMap z).hom ∧ ∀ b : Z.X.presheaf.stalk z, ∃ a s : X.X.presheaf.stalk (π z),
      (π.stalkMap z).hom s ≠ 0 ∧ (π.stalkMap z).hom s * b = (π.stalkMap z).hom a := by
  intro E _ _ _ H D l Xo c X Z π hj _ z
  obtain ⟨hBd, -⟩ := Z.normal z
  obtain ⟨hAd, -⟩ := X.normal (π z)
  let p0 : PrimeSpectrum (Z.X.presheaf.stalk z) := ⟨⊥, Ideal.bot_prime⟩
  obtain ⟨w, hw⟩ := GlobalTheory.T.generic_stalk_point_in_interior E H D l Xo c Z z p0 rfl
  have hy : Z.j w ⤳ z := by
    have hm : Z.X.fromSpecStalk z p0 ∈ Set.range (Z.X.fromSpecStalk z) := ⟨p0, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hm
    rw [hw]; exact hm

  have hg : IsIso (π.stalkMap (Z.j w)) := by
    have h1 : IsIso ((Z.j ≫ π).stalkMap w) := by rw [hj]; exact isIso_stalkMap_j X w
    rw [Scheme.Hom.stalkMap_comp] at h1
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (isIso_stalkMap_j Z w) h1
  have hgb := (ConcreteCategory.isIso_iff_bijective (π.stalkMap (Z.j w))).1 hg
  have hπy : π (Z.j w) ⤳ π z := hy.map π.continuous

  have sq : ∀ a : X.X.presheaf.stalk (π z), (Z.X.presheaf.stalkSpecializes hy).hom ((π.stalkMap z).hom a) =
      (π.stalkMap (Z.j w)).hom ((X.X.presheaf.stalkSpecializes hπy).hom a) := fun a =>
    (Scheme.Hom.stalkSpecializes_stalkMap_apply π (Z.j w) z hy a).symm
  have hσ := GlobalTheory.PushInv.stalkSpecializes_injective (X := Z.X) hy
  have hτ := GlobalTheory.PushInv.stalkSpecializes_injective (X := X.X) hπy
  have hinj : Function.Injective (π.stalkMap z).hom := by
    refine (injective_iff_map_eq_zero _).2 fun a ha => hτ ?_
    rw [map_zero]
    apply hgb.1
    rw [← sq, ha, map_zero, map_zero]
  refine ⟨hinj, fun b => ?_⟩
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X.X) (U := ⊤) (x := π z) trivial
  have hyU : π (Z.j w) ∈ U := hπy.mem_open U.2 hxU
  obtain ⟨κ, hκ⟩ := hgb.2 ((Z.X.presheaf.stalkSpecializes hy).hom b)
  obtain ⟨r, t, ht, e⟩ := GlobalTheory.PushInv.exists_frac hU hyU κ
  have er := GlobalTheory.PushInv.gs_specializes (𝟙 X.X) hπy U hxU r
  have et := GlobalTheory.PushInv.gs_specializes (𝟙 X.X) hπy U hxU t
  refine ⟨gs (𝟙 X.X) (π z) U r, gs (𝟙 X.X) (π z) U t, fun h0 => ?_, hσ ?_⟩
  · have h0' := hinj (h0.trans (map_zero _).symm)
    rw [h0', map_zero] at et
    rw [← et] at ht
    exact not_isUnit_zero ht
  · rw [map_mul, sq, sq, et, er, ← e, map_mul, hκ, mul_comm]

end GlobalTheory.ChartBir
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalk_map_injective_birational : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), Z.j ≫ π = X.j → π ≫ X.s = Z.s → ∀ z : Z.X, Function.Injective (π.stalkMap z).hom ∧ ∀ b : Z.X.presheaf.stalk z, ∃ a s : X.X.presheaf.stalk (π z), (π.stalkMap z).hom s ≠ 0 ∧ (π.stalkMap z).hom s * b = (π.stalkMap z).hom a := by
  atlas_forward_decl GlobalTheory.ChartBir.stalkMap_birational
end

section
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem flat_baseChange_birational_isDomain_and_includeRight_injective
    (A B R : Type) [CommRing A] [CommRing B] [IsDomain B] [CommRing R] [IsDomain R]
    [Algebra A B] [Algebra A R] [Module.Flat A R]
    (_hAB : Function.Injective (algebraMap A B))
    (hfrac : ∀ b : B, ∃ a s : A, algebraMap A B s ≠ 0 ∧ algebraMap A B s * b = algebraMap A B a) :
    IsDomain (TensorProduct A B R) ∧
      Function.Injective (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R) := by

  have hinc : Function.Injective (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R) := by
    have hcomp : ∀ r : R, (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R) r =
        (LinearMap.rTensor R (Algebra.linearMap A B)) ((TensorProduct.lid A R).symm r) := by
      intro r
      simp [Algebra.TensorProduct.includeRight_apply]
    intro r r' h
    rw [hcomp, hcomp] at h
    have h1 := Module.Flat.rTensor_preserves_injective_linearMap (M := R) (Algebra.linearMap A B) _hAB h
    exact (TensorProduct.lid A R).symm.injective h1

  have hmove : ∀ (a : A) (r : R), (algebraMap A B a) ⊗ₜ[A] r = (1 : B) ⊗ₜ[A] (algebraMap A R a * r) := by
    intro a r
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def]

  have hmulInj : ∀ c : B, c ≠ 0 → ∀ x : TensorProduct A B R, (c ⊗ₜ[A] (1 : R)) * x = 0 → x = 0 := by
    intro c hc x hx
    have heq : ∀ y : TensorProduct A B R, (c ⊗ₜ[A] (1 : R)) * y =
        (LinearMap.rTensor R (LinearMap.mulLeft A c)) y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b r => simp [Algebra.TensorProduct.tmul_mul_tmul]
      | add y z hy hz => rw [mul_add, map_add, hy, hz]
    have hinjc : Function.Injective (LinearMap.mulLeft A c) := by
      intro u v huv
      exact mul_left_cancel₀ hc huv
    have := Module.Flat.rTensor_preserves_injective_linearMap (M := R) _ hinjc
    apply this
    rw [← heq, hx, map_zero]

  have hden : ∀ x : TensorProduct A B R, ∃ s : A, algebraMap A B s ≠ 0 ∧
      ∃ r : R, (algebraMap A B s ⊗ₜ[A] (1 : R)) * x = (1 : B) ⊗ₜ[A] r := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨1, by simp, 0, by simp⟩
    | tmul b r =>
      obtain ⟨a, s, hs, hsb⟩ := hfrac b
      refine ⟨s, hs, algebraMap A R a * r, ?_⟩
      rw [Algebra.TensorProduct.tmul_mul_tmul, hsb, one_mul, hmove]
    | add x y hx hy =>
      obtain ⟨s, hs, r, hr⟩ := hx
      obtain ⟨s', hs', r', hr'⟩ := hy
      refine ⟨s * s', by rw [map_mul]; exact mul_ne_zero hs hs',
        algebraMap A R s' * r + algebraMap A R s * r', ?_⟩
      have e1 : (algebraMap A B (s * s') ⊗ₜ[A] (1 : R)) =
          (algebraMap A B s' ⊗ₜ[A] (1 : R)) * (algebraMap A B s ⊗ₜ[A] (1 : R)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul, mul_comm]
      have e2 : (algebraMap A B (s * s') ⊗ₜ[A] (1 : R)) =
          (algebraMap A B s ⊗ₜ[A] (1 : R)) * (algebraMap A B s' ⊗ₜ[A] (1 : R)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul]
      rw [mul_add]
      conv_lhs => arg 1; rw [e1, mul_assoc, hr]
      conv_lhs => arg 2; rw [e2, mul_assoc, hr']
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one,
        hmove, hmove, one_mul, one_mul, ← TensorProduct.tmul_add]

  haveI : Nontrivial (TensorProduct A B R) := by
    refine ⟨⟨Algebra.TensorProduct.includeRight (1 : R), Algebra.TensorProduct.includeRight (0 : R), ?_⟩⟩
    intro h
    exact one_ne_zero (hinc h)
  haveI : NoZeroDivisors (TensorProduct A B R) := by
    refine ⟨fun {x y} hxy => ?_⟩
    obtain ⟨s, hs, r, hr⟩ := hden x
    obtain ⟨s', hs', r', hr'⟩ := hden y
    have hprod : (1 : B) ⊗ₜ[A] (r * r') = 0 := by
      have : ((algebraMap A B s ⊗ₜ[A] (1 : R)) * x) * ((algebraMap A B s' ⊗ₜ[A] (1 : R)) * y) = 0 := by
        rw [mul_mul_mul_comm, hxy, mul_zero]
      rw [hr, hr', Algebra.TensorProduct.tmul_mul_tmul, one_mul] at this
      exact this
    have hrr : r * r' = 0 := by
      apply hinc
      rw [map_zero, Algebra.TensorProduct.includeRight_apply]
      exact hprod
    rcases mul_eq_zero.mp hrr with h0 | h0
    · left
      apply hmulInj _ hs
      rw [hr, h0, TensorProduct.tmul_zero]
    · right
      apply hmulInj _ hs'
      rw [hr', h0, TensorProduct.tmul_zero]
  exact ⟨NoZeroDivisors.to_isDomain _, hinc⟩

end GlobalTheory
end

open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_domain_birational : ∀ (A B R : Type) [CommRing A] [CommRing B] [IsDomain B] [CommRing R] [IsDomain R] [Algebra A B] [Algebra A R] [Module.Flat A R], Function.Injective (algebraMap A B) → (∀ b : B, ∃ a s : A, algebraMap A B s ≠ 0 ∧ algebraMap A B s * b = algebraMap A B a) → IsDomain (TensorProduct A B R) ∧ Function.Injective (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R) := by
  atlas_forward_decl GlobalTheory.flat_baseChange_birational_isDomain_and_includeRight_injective
end

section
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_residue_unramified_finite : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] [IsLocalRing R] [Algebra A B] [Algebra A R], ((IsLocalRing.residue R).comp (algebraMap A R)).Finite → ((IsLocalRing.residue R).comp (algebraMap A R)).FormallyUnramified → Algebra.FormallyUnramified B (TensorProduct A B R ⧸ (IsLocalRing.maximalIdeal R).map (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R)) ∧ Module.Finite B (TensorProduct A B R ⧸ (IsLocalRing.maximalIdeal R).map (Algebra.TensorProduct.includeRight : R →ₐ[A] TensorProduct A B R)) := by
  first | exact @GlobalTheory.tensor_quot_maximalIdeal_finite_formallyUnramified | exact GlobalTheory.tensor_quot_maximalIdeal_finite_formallyUnramified | (intros; apply GlobalTheory.tensor_quot_maximalIdeal_finite_formallyUnramified <;> assumption)
end

section
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_maximal_ideal_map : ∀ (B S : Type) [CommRing B] [IsLocalRing B] [CommRing S] [Algebra B S] (J q : Ideal S) [q.IsMaximal], J ≤ (IsLocalRing.maximalIdeal B).map (algebraMap B S) → (IsLocalRing.maximalIdeal B).map (algebraMap B S) ≤ q → Algebra.FormallyUnramified B (S ⧸ J) → Module.Finite B (S ⧸ J) → (IsLocalRing.maximalIdeal B).map ((algebraMap S (Localization.AtPrime q)).comp (algebraMap B S)) = IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
  first | exact @GlobalTheory.map_maximalIdeal_localization_eq_of_formallyUnramified_quotient | exact GlobalTheory.map_maximalIdeal_localization_eq_of_formallyUnramified_quotient | (intros; apply GlobalTheory.map_maximalIdeal_localization_eq_of_formallyUnramified_quotient <;> assumption)
end

section
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_residue_finite_unram : ∀ (B S : Type) [CommRing B] [CommRing S] [Algebra B S] (J q : Ideal S) [q.IsMaximal], J ≤ q → Algebra.FormallyUnramified B (S ⧸ J) → Module.Finite B (S ⧸ J) → ((IsLocalRing.residue (Localization.AtPrime q)).comp ((algebraMap S (Localization.AtPrime q)).comp (algebraMap B S))).Finite ∧ ((IsLocalRing.residue (Localization.AtPrime q)).comp ((algebraMap S (Localization.AtPrime q)).comp (algebraMap B S))).FormallyUnramified := by
  first | exact @GlobalTheory.residue_atMaximal_finite_formallyUnramified | exact GlobalTheory.residue_atMaximal_finite_formallyUnramified | (intros; apply GlobalTheory.residue_atMaximal_finite_formallyUnramified <;> assumption)
end

section
section
open IsLocalRing TensorProduct

namespace GlobalTheory.LocalChart
theorem exists_localised_base_change : ∀ (A B R : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [CommRing B] [IsDomain B] [IsLocalRing B] [CommRing R] [IsDomain R] [IsLocalRing R] (f : A →+* B) (g : A →+* R), IsNoetherianRing A → IsNoetherianRing R → Algebra.EssFiniteType ℤ B → IsLocalHom f → Function.Injective f → (∀ b : B, ∃ a s : A, f s ≠ 0 ∧ f s * b = f a) → IsLocalHom g → GlobalTheory.Toroidal.IsEtaleCompletion g → ((IsLocalRing.residue R).comp g).FormallyUnramified → ∃ (C : Type) (_ : CommRing C) (_ : IsDomain C) (_ : IsLocalRing C) (φ : R →+* C) (ψ : B →+* C), IsNoetherianRing C ∧ IsLocalHom φ ∧ Function.Injective φ ∧ IsLocalHom ψ ∧ Function.Injective ψ ∧ ψ.Flat ∧ (IsLocalRing.maximalIdeal B).map ψ = IsLocalRing.maximalIdeal C ∧ ((IsLocalRing.residue C).comp ψ).Finite ∧ ((IsLocalRing.residue C).comp ψ).FormallyUnramified ∧ ψ.comp f = φ.comp g := by
  intro A B R _ _ _ _ _ _ _ _ _ f g hA hR hB hfl hfi hbir hgl hEt hFU
  obtain ⟨hflat, hmax, hfin⟩ := hEt
  letI := f.toAlgebra
  letI := g.toAlgebra
  haveI : Module.Flat A R := hflat
  haveI : IsLocalHom (algebraMap A R) := hgl
  haveI : IsLocalHom (algebraMap A B) := hfl
  haveI : Module.FaithfullyFlat A R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  obtain ⟨hdom, hinjR⟩ := GlobalTheory.T.tensor_domain_birational A B R hfi hbir
  haveI := hdom
  haveI : Algebra.EssFiniteType A B := Algebra.EssFiniteType.of_comp ℤ A B
  haveI : IsNoetherianRing (B ⊗[A] R) :=
    haveI := Algebra.EssFiniteType.isNoetherianRing R (R ⊗[A] B)
    isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm A R B).toRingEquiv
  have hne : (maximalIdeal B).map (algebraMap B (B ⊗[A] R)) ≠ ⊤ := by
    intro h
    have := Ideal.comap_map_eq_self_of_faithfullyFlat (B := B ⊗[A] R) (maximalIdeal B)
    rw [h, Ideal.comap_top] at this
    exact (maximalIdeal.isMaximal B).ne_top this.symm
  obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hne
  set C := Localization.AtPrime q
  have hJ : (maximalIdeal R).map (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R) ≤ (maximalIdeal B).map (algebraMap B (B ⊗[A] R)) := by
    rw [← hmax, Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro a ha
    have e : (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R) (g a) = algebraMap B (B ⊗[A] R) (f a) :=
      ((Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R).commutes a).trans
        ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R).commutes a).symm
    simp only [Ideal.mem_comap]
    rw [e]
    exact Ideal.mem_map_of_mem _ (map_nonunit f a ha)
  obtain ⟨hFU1, hFin1⟩ := GlobalTheory.T.tensor_residue_unramified_finite A B R hfin hFU
  have e1 := GlobalTheory.T.localization_maximal_ideal_map B (B ⊗[A] R) _ q hJ hle hFU1 hFin1
  obtain ⟨e2, e3⟩ := GlobalTheory.T.localization_residue_finite_unram B (B ⊗[A] R) _ q (hJ.trans hle) hFU1 hFin1
  refine ⟨C, inferInstance, inferInstance, inferInstance, (algebraMap (B ⊗[A] R) C).comp (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R).toRingHom, (algebraMap (B ⊗[A] R) C).comp (algebraMap B (B ⊗[A] R)), inferInstance, ?_, ?_, ?_, ?_, ?_, e1, e2, e3, ?_⟩
  · refine ((local_hom_TFAE _).out 0 2).2 ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_map]
    exact Ideal.map_mono (le_trans (hmax ▸ hJ) hle)
  · exact (IsLocalization.injective C q.primeCompl_le_nonZeroDivisors).comp hinjR
  · refine ((local_hom_TFAE _).out 0 2).2 ?_
    rw [e1]
  · refine (IsLocalization.injective C q.primeCompl_le_nonZeroDivisors).comp ?_
    show Function.Injective (algebraMap B (B ⊗[A] R))
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker, ← Ideal.map_bot (f := algebraMap B (B ⊗[A] R))]
    exact Ideal.comap_map_eq_self_of_faithfullyFlat _
  · exact RingHom.Flat.comp ((RingHom.flat_algebraMap_iff).2 (Module.Flat.baseChange A B R)) ((RingHom.flat_algebraMap_iff).2 (IsLocalization.flat C q.primeCompl))
  · ext a
    simp only [RingHom.comp_apply]
    congr 1
    exact ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R).commutes a).trans
        ((Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R).commutes a).symm

end GlobalTheory.LocalChart
end

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_comp_formal_completion : ∀ (A B R : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [CommRing B] [IsDomain B] [IsLocalRing B] [CommRing R] [IsDomain R] [IsLocalRing R] (f : A →+* B) (g : A →+* R), IsNoetherianRing A → IsNoetherianRing R → Algebra.EssFiniteType ℤ B → IsLocalHom f → Function.Injective f → (∀ b : B, ∃ a s : A, f s ≠ 0 ∧ f s * b = f a) → IsLocalHom g → GlobalTheory.Toroidal.IsEtaleCompletion g → ((IsLocalRing.residue R).comp g).FormallyUnramified → ∃ (C : Type) (_ : CommRing C) (_ : IsDomain C) (_ : IsLocalRing C) (φ : R →+* C) (ψ : B →+* C), IsNoetherianRing C ∧ IsLocalHom φ ∧ Function.Injective φ ∧ IsLocalHom ψ ∧ Function.Injective ψ ∧ ψ.Flat ∧ (IsLocalRing.maximalIdeal B).map ψ = IsLocalRing.maximalIdeal C ∧ ((IsLocalRing.residue C).comp ψ).Finite ∧ ((IsLocalRing.residue C).comp ψ).FormallyUnramified ∧ ψ.comp f = φ.comp g := by
  atlas_forward_decl GlobalTheory.LocalChart.exists_localised_base_change
end

section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complete_unramified_extension : ∀ (B C : Type) [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C] (ψ : B →+* C), IsNoetherianRing C → IsLocalHom ψ → ψ.Flat → (IsLocalRing.maximalIdeal B).map ψ = IsLocalRing.maximalIdeal C → ((IsLocalRing.residue C).comp ψ).Finite → ((IsLocalRing.residue C).comp ψ).FormallyUnramified → ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (ι : C →+* R'), IsNoetherianRing R' ∧ IsAdicComplete (IsLocalRing.maximalIdeal R') R' ∧ IsLocalHom ι ∧ Function.Injective ι ∧ GlobalTheory.Toroidal.IsEtaleCompletion (ι.comp ψ) ∧ ((IsLocalRing.residue R').comp (ι.comp ψ)).FormallyUnramified := by
  first | exact @GlobalTheory.CompletionEtale.exists_completion | exact GlobalTheory.CompletionEtale.exists_completion | (intros; apply GlobalTheory.CompletionEtale.exists_completion <;> assumption)
end

section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_unramified_normal : ∀ (D E : Type) [CommRing D] [IsDomain D] [IsLocalRing D] [CommRing E] [IsLocalRing E] (h : D →+* E), IsNoetherianRing D → IsDomain (AdicCompletion (IsLocalRing.maximalIdeal D) D) → IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal D) D) → IsNoetherianRing E → IsAdicComplete (IsLocalRing.maximalIdeal E) E → IsLocalHom h → GlobalTheory.Toroidal.IsEtaleCompletion h → ((IsLocalRing.residue E).comp h).FormallyUnramified → IsDomain E ∧ IsIntegrallyClosed E := by
  first | exact @GlobalTheory.EtaleCompletionNormal.isDomain_and_isIntegrallyClosed | exact GlobalTheory.EtaleCompletionNormal.isDomain_and_isIntegrallyClosed | (intros; apply GlobalTheory.EtaleCompletionNormal.isDomain_and_isIntegrallyClosed <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TorRef.ChartAbove

theorem specMap_stalkCongr_fromSpecStalk {X : Scheme.{0}} {x y : X} (h : x = y) :
    Spec.map (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ X.fromSpecStalk x = X.fromSpecStalk y := by
  subst h
  simp

theorem exists_complete_normal_above (A B R : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [CommRing B] [IsDomain B] [IsLocalRing B]
    [IsIntegrallyClosed B] [CharZero B] [Algebra.EssFiniteType ℤ B] [CommRing R] [IsDomain R] [IsLocalRing R]
    (f : A →+* B) (g : A →+* R) (hA : IsNoetherianRing A) (hf : IsLocalHom f) (hfi : Function.Injective f)
    (hbir : ∀ b : B, ∃ a s : A, f s ≠ 0 ∧ f s * b = f a) (hg : IsLocalHom g) (hR : IsCN R)
    (het : IsEtaleCompletion g) (hfu : ((residue R).comp g).FormallyUnramified) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (φ : R →+* R') (ψ : B →+* R'),
      IsCN R' ∧ IsLocalHom ψ ∧ Function.Injective ψ ∧ IsEtaleCompletion ψ ∧
      ((residue R').comp ψ).FormallyUnramified ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ψ.comp f = φ.comp g := by
  obtain ⟨C, _, _, _, φ0, ψ0, hCn, hφl, hφi, hψl, hψi, hψf, hψm, hψfin, hψfu, hcomm⟩ :=
    GlobalTheory.T.residue_comp_formal_completion A B R f g hA hR.1 inferInstance hf hfi hbir hg het hfu
  obtain ⟨R', _, _, ι, hRn, hRc, hιl, hιi, hιe, hιu⟩ := GlobalTheory.T.exists_complete_unramified_extension B C ψ0 hCn hψl hψf hψm hψfin hψfu
  have hBn : IsNoetherianRing B := Algebra.EssFiniteType.isNoetherianRing ℤ B
  obtain ⟨hd, hic⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed B
  haveI := hιl
  haveI := hψl
  haveI := hφl
  have hloc : IsLocalHom (ι.comp ψ0) := inferInstance
  obtain ⟨hRd, hRi⟩ := GlobalTheory.T.completion_unramified_normal B R' (ι.comp ψ0) hBn hd hic hRn hRc hloc hιe hιu
  have hinj : Function.Injective (ι.comp ψ0) := hιi.comp hψi
  haveI : CharZero R' := charZero_of_injective_ringHom hinj
  refine ⟨R', inferInstance, hRd, inferInstance, ι.comp φ0, ι.comp ψ0, ⟨hRn, hRi, hRc, inferInstance⟩, hloc, hinj,
    hιe, hιu, hιi.comp hφi, inferInstance, ?_⟩
  rw [RingHom.comp_assoc, hcomm, ← RingHom.comp_assoc]

theorem exists_chart_above : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), Z.j ≫ π = X.j → π ≫ X.s = Z.s → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X.X) (z : Z.X), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → ξ (closedPoint R) = π z → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ξ' : Sp R' ⟶ Z.X) (φ : R →+* R'), IsCN R' ∧ ξ' (closedPoint R') = z ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ').hom ∧ ((residue R').comp (Scheme.stalkClosedPointTo ξ').hom).FormallyUnramified ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ξ' ≫ π = spMap φ ≫ ξ ∧ Dense (ξ' ⁻¹' Set.range Z.j) := by
  intro E _ _ _ H D l Xo c X Z π hj hs R _ _ _ ξ z hR het hfu hpt
  haveI := (Z.normal z).1
  haveI := (Z.normal z).2
  haveI := (X.normal (ξ (closedPoint R))).1
  obtain ⟨hcz, hez⟩ := GlobalTheory.T.stalk_charZero_essFiniteType E H D l Xo c Z z
  obtain ⟨-, hexX⟩ := GlobalTheory.T.stalk_charZero_essFiniteType E H D l Xo c X (ξ (closedPoint R))
  have hAn : IsNoetherianRing (X.X.presheaf.stalk (ξ (closedPoint R))) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  obtain ⟨hbi, hbb⟩ := GlobalTheory.T.stalk_map_injective_birational E H D l Xo c X Z π hj hs z
  let e := X.X.presheaf.stalkCongr (Inseparable.of_eq hpt)
  have heb : Function.Bijective e.hom.hom := ConcreteCategory.bijective_of_isIso e.hom
  let f : X.X.presheaf.stalk (ξ (closedPoint R)) →+* Z.X.presheaf.stalk z := (π.stalkMap z).hom.comp e.hom.hom
  have hfi : Function.Injective f := hbi.comp heb.1
  have hbir : ∀ b : Z.X.presheaf.stalk z, ∃ a s : X.X.presheaf.stalk (ξ (closedPoint R)), f s ≠ 0 ∧ f s * b = f a := by
    intro b
    obtain ⟨a, s, hs0, hsb⟩ := hbb b
    obtain ⟨a', rfl⟩ := heb.2 a
    obtain ⟨s', rfl⟩ := heb.2 s
    exact ⟨a', s', hs0, hsb⟩
  have hfl : IsLocalHom f := inferInstance
  let g := (Scheme.stalkClosedPointTo ξ).hom
  obtain ⟨R', _, _, _, φ, ψ, hR', hψl, hψi, het', hfu', hφi, hφl, hcomm⟩ :=
    exists_complete_normal_above _ _ R f g hAn hfl hfi hbir inferInstance hR het hfu

  haveI := hψl
  let ψc : Z.X.presheaf.stalk z ⟶ CommRingCat.of R' := CommRingCat.ofHom ψ
  haveI : IsLocalHom ψc.hom := hψl
  let ξ' : Sp R' ⟶ Z.X := (SpecToEquivOfLocalRing Z.X (CommRingCat.of R')).symm ⟨z, ⟨ψc, inferInstance⟩⟩
  have hsym := (SpecToEquivOfLocalRing Z.X (CommRingCat.of R')).apply_symm_apply ⟨z, ⟨ψc, inferInstance⟩⟩
  rw [SpecToEquivOfLocalRing_eq_iff] at hsym
  obtain ⟨h1, h2⟩ := hsym
  have hpt' : ξ' (closedPoint R') = z := h1
  have h2' : (Scheme.stalkClosedPointTo ξ').hom = ψ.comp (Z.X.presheaf.stalkCongr (Inseparable.of_eq h1)).hom.hom := by
    exact congrArg (fun q => q.hom) h2
  refine ⟨R', inferInstance, inferInstance, inferInstance, ξ', φ, hR', hpt', ?_, ?_, hφi, hφl, ?_, ?_⟩
  · rw [h2']
    exact isEtaleCompletion_comp_bij _ (ConcreteCategory.bijective_of_isIso _) ψ het'
  · rw [h2']
    have hsurj : Function.Surjective (Z.X.presheaf.stalkCongr (Inseparable.of_eq h1)).hom.hom :=
      (ConcreteCategory.bijective_of_isIso _).2
    have h3 := RingHom.FormallyUnramified.comp (RingHom.FormallyUnramified.of_surjective hsurj) hfu'
    exact h3
  · have hcomm' : Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom φ = e.hom ≫ π.stalkMap z ≫ ψc := by
      ext a
      have := congrArg (fun q : _ →+* R' => q a) hcomm
      exact this.symm
    calc ξ' ≫ π = Spec.map ψc ≫ Z.X.fromSpecStalk z ≫ π := by simp only [ξ', SpecToEquivOfLocalRing_symm_apply, Category.assoc]
      _ = Spec.map ψc ≫ Spec.map (π.stalkMap z) ≫ X.X.fromSpecStalk (π z) := by
          rw [Scheme.SpecMap_stalkMap_fromSpecStalk]
      _ = Spec.map ψc ≫ Spec.map (π.stalkMap z) ≫ Spec.map e.hom ≫ X.X.fromSpecStalk (ξ (closedPoint R)) := by
          rw [specMap_stalkCongr_fromSpecStalk hpt]
      _ = Spec.map (e.hom ≫ π.stalkMap z ≫ ψc) ≫ X.X.fromSpecStalk (ξ (closedPoint R)) := by
          simp only [Spec.map_comp, Category.assoc]
      _ = Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom φ) ≫ X.X.fromSpecStalk (ξ (closedPoint R)) := by
          rw [hcomm']
      _ = spMap φ ≫ ξ := by
          rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · let η0 : PrimeSpectrum R' := ⟨⊥, Ideal.isPrime_bot⟩
    let η : Sp R' := η0
    have hη : η ∈ ξ' ⁻¹' Set.range Z.j := by
      show ξ' η ∈ Set.range Z.j
      have hxi : ξ' η = Z.X.fromSpecStalk z ((Spec.map ψc) η) := rfl
      rw [hxi]
      apply GlobalTheory.T.generic_stalk_point_in_interior E H D l Xo c Z z
      show Ideal.comap ψ ⊥ = ⊥
      rw [← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot ψ).1 hψi
    have hcl0 : closure ({η0} : Set (PrimeSpectrum R')) = Set.univ := by
      rw [PrimeSpectrum.closure_singleton]
      exact PrimeSpectrum.zeroLocus_bot
    have hcl : closure ({η} : Set (Sp R')) = Set.univ := hcl0
    rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro p
    have hp : p ∈ closure ({η} : Set (Sp R')) := by rw [hcl]; trivial
    exact closure_mono (Set.singleton_subset_iff.2 hη) hp

end GlobalTheory.TorRef.ChartAbove
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formally_unramified_compatible_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X), Z.j ≫ π = X.j → π ≫ X.s = Z.s → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X.X) (z : Z.X), IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → ξ (closedPoint R) = π z → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ξ' : Sp R' ⟶ Z.X) (φ : R →+* R'), IsCN R' ∧ ξ' (closedPoint R') = z ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ').hom ∧ ((residue R').comp (Scheme.stalkClosedPointTo ξ').hom).FormallyUnramified ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ξ' ≫ π = spMap φ ≫ ξ ∧ Dense (ξ' ⁻¹' Set.range Z.j) := by
  atlas_forward_decl GlobalTheory.TorRef.ChartAbove.exists_chart_above
end
