import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateCondCongr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsIntClosedLocalizationAndQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRootSubMemOfEvalMem
import BuildAid.ForwardExisting

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel GlobalTheory.UPelLevel
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem asIdeal_spMap_field {B k : Type} [CommRing B] [Field k] (φ : B →+* k) (u : Sp k) :
    ((spMap φ).base u).asIdeal = RingHom.ker φ := by
  have hu : u.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ u.isPrime
  rw [RingHom.ker_eq_comap_bot, ← hu]
  rw [spMap, Spec.map_base]
  rfl

theorem exists_ringHom_pair_of_specializes {X : Scheme.{0}} {k k' : Type} [Field k] [Field k'] (x : Sp k ⟶ X)
    (x' : Sp k' ⟶ X) (u : Sp k) (u' : Sp k') (h : x'.base u' ⤳ x.base u) :
    ∃ (B : Type) (_ : CommRing B) (g : B →+* k) (g' : B →+* k') (ρ : Sp B ⟶ X),
      RingHom.ker g' ≤ RingHom.ker g ∧ spMap g ≫ ρ = x ∧ spMap g' ≫ ρ = x' := by
  obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show x.base u ∈ (⊤ : X.Opens) from trivial)
  have hV' : IsAffineOpen V := hV
  have hx'V : x'.base u' ∈ V := h.mem_open V.isOpen hxV
  have hsub : Set.range x.base ⊆ Set.range hV'.fromSpec := by
    rw [hV'.range_fromSpec]
    rintro _ ⟨v, rfl⟩
    rwa [Subsingleton.elim v u]
  have hsub' : Set.range x'.base ⊆ Set.range hV'.fromSpec := by
    rw [hV'.range_fromSpec]
    rintro _ ⟨v, rfl⟩
    rwa [Subsingleton.elim v u']
  let xV := IsOpenImmersion.lift hV'.fromSpec x hsub
  let x'V := IsOpenImmersion.lift hV'.fromSpec x' hsub'
  have hfx : xV ≫ hV'.fromSpec = x := IsOpenImmersion.lift_fac _ _ _
  have hfx' : x'V ≫ hV'.fromSpec = x' := IsOpenImmersion.lift_fac _ _ _
  have e1 : spMap (Spec.preimage xV).hom = xV := Spec.map_preimage xV
  have e2 : spMap (Spec.preimage x'V).hom = x'V := Spec.map_preimage x'V
  refine ⟨Γ(X, V), inferInstance, (Spec.preimage xV).hom, (Spec.preimage x'V).hom, hV'.fromSpec, ?_, ?_, ?_⟩
  · rw [← asIdeal_spMap_field _ u, ← asIdeal_spMap_field _ u']
    refine (PrimeSpectrum.le_iff_specializes ((spMap (Spec.preimage x'V).hom).base u')
      ((spMap (Spec.preimage xV).hom).base u)).mpr ?_
    rw [e1, e2]
    have h2 : hV'.fromSpec (x'V u') ⤳ hV'.fromSpec (xV u) := by
      rw [← hfx, ← hfx'] at h
      simpa only [Scheme.Hom.comp_apply] using h
    exact (hV'.fromSpec.isOpenEmbedding.isInducing.specializes_iff).mp h2
  · rw [e1]; exact hfx
  · rw [e2]; exact hfx'

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel GlobalTheory.UPelLevel
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_ring_hom_pair_of_specializes : ∀ {X : Scheme.{0}} {k k' : Type} [Field k] [Field k'] (x : Sp k ⟶ X) (x' : Sp k' ⟶ X) (u : Sp k) (u' : Sp k'), x'.base u' ⤳ x.base u → ∃ (B : Type) (_ : CommRing B) (g : B →+* k) (g' : B →+* k') (ρ : Sp B ⟶ X), RingHom.ker g' ≤ RingHom.ker g ∧ spMap g ≫ ρ = x ∧ spMap g' ≫ ρ = x' := by
  atlas_forward_decl GlobalTheory.exists_ringHom_pair_of_specializes
end

section
section
open Polynomial

namespace GlobalTheory

theorem exists_integral_domain_extension_monic_roots :
    ∀ (D : Type) [CommRing D] [IsDomain D], ∃ (C : Type) (_ : CommRing C) (_ : Algebra D C),
      IsDomain C ∧ Algebra.IsIntegral D C ∧ Function.Injective (algebraMap D C) ∧
      (∀ f : C[X], f.Monic → 0 < f.natDegree → ∃ y : C, f.eval y = 0) ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (h : D →+* K), Function.Injective h →
        ∃ e : C →+* K, Function.Injective e ∧ e.comp (algebraMap D C) = h := by
  intro D _ _
  have hDL : Function.Injective (algebraMap D (AlgebraicClosure (FractionRing D))) := by
    rw [IsScalarTower.algebraMap_eq D (FractionRing D) (AlgebraicClosure (FractionRing D))]
    exact (algebraMap (FractionRing D) (AlgebraicClosure (FractionRing D))).injective.comp
      (IsFractionRing.injective D (FractionRing D))
  have hCL : Function.Injective (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D)))
      (AlgebraicClosure (FractionRing D))) := Subtype.val_injective
  refine ⟨integralClosure D (AlgebraicClosure (FractionRing D)), inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro a b hab
    apply hDL
    simpa using congrArg Subtype.val hab
  · intro f hf hdeg
    have hdeg' : (f.map (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D)))
        (AlgebraicClosure (FractionRing D)))).degree ≠ 0 := by
      rw [degree_map_eq_of_injective hCL, degree_eq_natDegree hf.ne_zero]
      exact_mod_cast hdeg.ne'
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg'
    have hy' : f.eval₂ (algebraMap (integralClosure D (AlgebraicClosure (FractionRing D)))
        (AlgebraicClosure (FractionRing D))) y = 0 := by rwa [IsRoot, eval_map] at hy
    have hyC : IsIntegral (integralClosure D (AlgebraicClosure (FractionRing D))) y :=
      ⟨f, hf, hy'⟩
    have hyD : IsIntegral D y := isIntegral_trans y hyC
    refine ⟨⟨y, hyD⟩, ?_⟩
    apply hCL
    rw [← eval₂_at_apply, map_zero]
    exact hy'
  · intro K _ _ h hinj
    letI : Algebra (FractionRing D) K := (IsFractionRing.lift hinj : FractionRing D →+* K).toAlgebra
    let φ : AlgebraicClosure (FractionRing D) →ₐ[FractionRing D] K := IsAlgClosed.lift
    refine ⟨φ.toRingHom.comp (integralClosure D (AlgebraicClosure (FractionRing D))).val.toRingHom,
      φ.toRingHom.injective.comp Subtype.val_injective, ?_⟩
    ext a
    show φ (algebraMap D (AlgebraicClosure (FractionRing D)) a) = h a
    rw [IsScalarTower.algebraMap_apply D (FractionRing D) (AlgebraicClosure (FractionRing D)),
      AlgHom.commutes]
    exact IsFractionRing.lift_algebraMap hinj a

end GlobalTheory
end

open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_domain_extension_with_monic_roots : ∀ (D : Type) [CommRing D] [IsDomain D], ∃ (C : Type) (_ : CommRing C) (_ : Algebra D C), IsDomain C ∧ Algebra.IsIntegral D C ∧ Function.Injective (algebraMap D C) ∧ (∀ f : C[X], f.Monic → 0 < f.natDegree → ∃ y : C, f.eval y = 0) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (h : D →+* K), Function.Injective h → ∃ e : C →+* K, Function.Injective e ∧ e.comp (algebraMap D C) = h := by
  atlas_forward_decl GlobalTheory.exists_integral_domain_extension_monic_roots
end

section
section
open Polynomial

namespace GlobalTheory

theorem ringHom_extend_of_isIntegral_isAlgClosed (A C K : Type) [CommRing A] [CommRing C]
    [Algebra A C] [Algebra.IsIntegral A C] [Field K] [IsAlgClosed K] (h : A →+* K)
    (hk : RingHom.ker (algebraMap A C) ≤ RingHom.ker h) :
    ∃ ψ : C →+* K, ψ.comp (algebraMap A C) = h := by
  classical
  haveI hp : (RingHom.ker h).IsPrime := RingHom.ker_isPrime h
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker h) (⊥ : Ideal C)
    (by simpa [← RingHom.ker_eq_comap_bot] using hk)
  haveI : Q.LiesOver (RingHom.ker h) := (Ideal.liesOver_iff _ _).mpr hQc.symm
  letI : Algebra (A ⧸ RingHom.ker h) K := (RingHom.kerLift h).toAlgebra
  haveI : FaithfulSMul (A ⧸ RingHom.ker h) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective h)
  haveI : FaithfulSMul (A ⧸ RingHom.ker h) (C ⧸ Q) := inferInstance
  haveI : Nontrivial (A ⧸ RingHom.ker h) := Ideal.Quotient.nontrivial_iff.mpr hp.ne_top
  haveI : Algebra.IsIntegral (A ⧸ RingHom.ker h) (C ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver (A := A) (p := RingHom.ker h) (P := Q)
  haveI : Algebra.IsAlgebraic (A ⧸ RingHom.ker h) (C ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker h) (C ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective _ _)
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker h) K :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.kerLift_injective h)
  let φ : (C ⧸ Q) →ₐ[A ⧸ RingHom.ker h] K := IsAlgClosed.lift
  refine ⟨φ.toRingHom.comp (Ideal.Quotient.mk Q), ?_⟩
  ext a
  have e1 : (Ideal.Quotient.mk Q) (algebraMap A C a) =
      algebraMap (A ⧸ RingHom.ker h) (C ⧸ Q) (Ideal.Quotient.mk _ a) := rfl
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [e1, φ.commutes]
  rfl

end GlobalTheory
end

open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_extend_of_isIntegral_of_isAlgClosed : ∀ (A C K : Type) [CommRing A] [CommRing C] [Algebra A C] [Algebra.IsIntegral A C] [Field K] [IsAlgClosed K] (h : A →+* K), RingHom.ker (algebraMap A C) ≤ RingHom.ker h → ∃ ψ : C →+* K, ψ.comp (algebraMap A C) = h := by
  atlas_forward_decl GlobalTheory.ringHom_extend_of_isIntegral_isAlgClosed
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel GlobalTheory.UPelLevel
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open Polynomial

theorem geomPoints_factor_henselian_of_specializes :
  ∀ {X : Scheme.{0}} {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] (x : Sp k ⟶ X) (x' : Sp k' ⟶ X) (u : Sp k) (u' : Sp k'), x'.base u' ⤳ x.base u → ∃ (R : Type) (_ : CommRing R) (_ : HenselianLocalRing R) (_ : IsAlgClosed (IsLocalRing.ResidueField R)) (r : Sp R ⟶ X) (i : Sp k ⟶ Sp R) (i' : Sp k' ⟶ Sp R), i ≫ r = x ∧ i' ≫ r = x' := by
  intro X k k' _ _ _ _ x x' u u' hsp
  obtain ⟨B, _, g, g', ρ, hker, hx, hx'⟩ := GlobalTheory.T.exists_affine_ring_hom_pair_of_specializes x x' u u' hsp
  set q := RingHom.ker g' with hq
  haveI : q.IsPrime := RingHom.ker_isPrime g'
  let D := B ⧸ q
  let h' : D →+* k' := RingHom.kerLift g'
  have h'inj : Function.Injective h' := RingHom.kerLift_injective g'
  let h : D →+* k := Ideal.Quotient.lift q g (fun b hb => hker hb)
  obtain ⟨C, _, _, hCdom, hCint, hCinj, hCroot, hCext⟩ := GlobalTheory.T.exists_integral_domain_extension_with_monic_roots D
  obtain ⟨e', he'inj, he'⟩ := hCext k' h' h'inj
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_ringHom_extend_of_isIntegral_of_isAlgClosed D C k h (by
    intro a ha; rw [RingHom.mem_ker] at ha ⊢
    rw [show a = 0 from hCinj (by rw [ha, map_zero])]; exact map_zero h)
  let P := RingHom.ker ψ
  haveI : P.IsPrime := RingHom.ker_isPrime ψ
  let R := Localization.AtPrime P
  have h0 : (0 : C) ∉ P.primeCompl := fun h0 => h0 P.zero_mem
  have hRloc := (absIntClosed_localization_and_quotient C ⟨hCdom, hCroot⟩).1 P.primeCompl h0
  obtain ⟨hH, hAC, -⟩ := AbsIntClosedLocal.henselian_isAlgClosed_pow_surj R hRloc
  let φ : B →+* R := (algebraMap C R).comp ((algebraMap D C).comp (Ideal.Quotient.mk q))
  let f : R →+* k := IsLocalization.lift (M := P.primeCompl) (g := ψ) (fun s => by
    refine IsUnit.mk0 _ ?_
    exact s.2)
  let f' : R →+* k' := IsLocalization.lift (M := P.primeCompl) (g := e') (fun s => by
    refine IsUnit.mk0 _ ?_
    intro hs
    exact s.2 (by rw [show (s : C) = 0 from he'inj (by rw [hs, map_zero])]; exact P.zero_mem))
  have hf : f.comp φ = g := by
    ext b
    simp only [f, φ, RingHom.comp_apply, IsLocalization.lift_eq]
    rw [← RingHom.comp_apply ψ, hψ]
    rfl
  have hf' : f'.comp φ = g' := by
    ext b
    simp only [f', φ, RingHom.comp_apply, IsLocalization.lift_eq]
    rw [← RingHom.comp_apply e', he']
    rfl
  refine ⟨R, inferInstance, hH, hAC, spMap φ ≫ ρ, spMap f, spMap f', ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hf, hx]
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hf', hx']

end GlobalTheory
end
