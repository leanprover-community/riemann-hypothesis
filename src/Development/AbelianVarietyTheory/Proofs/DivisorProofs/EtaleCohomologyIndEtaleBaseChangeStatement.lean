import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyLocalToGlobalRingMapIndEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistFinitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyNegativeVanishingDegreeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheafStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyGenericFibreHenselLineSubsingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonEtaleCohomologyGenericFibreHenselianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HZeroPullbackTwistBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldMonicRootsTensorFractionRingStrictlyHense

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC TensorProduct

namespace GlobalTheory.EtC.LineLocal

open Polynomial

theorem bijective_of_subsingleton {X Y : Type*} [Subsingleton X] [Subsingleton Y] (f : X → Y) (x : X) :
    Function.Bijective f :=
  ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨x, Subsingleton.elim _ _⟩⟩

theorem idem_of_domain {A : Type} [CommRing A] [IsDomain A] (e : A) (he : IsIdempotentElem e) :
    e = 0 ∨ e = 1 := by
  have h : e * (e - 1) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

theorem isDomain_tensor_fractionRing (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [IsDomain O]
    [Algebra T O] (hinj : Function.Injective (algebraMap T O)) : IsDomain (O ⊗[T] FractionRing T) := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
      (O ⊗[T] FractionRing T) := by
    rw [Algebra.isLocalization_iff_isPushout (nonZeroDivisors T) (FractionRing T)]
    infer_instance
  exact IsLocalization.isDomain_of_le_nonZeroDivisors (M := Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
    (O ⊗[T] FractionRing T) (by
      rintro _ ⟨a, ha, rfl⟩
      exact mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero ha)))

theorem eqv_local : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T →
    IsUnit (q : T) → ∀ (O : Type) [CommRing O] [Algebra (Polynomial T) O] [Algebra T O]
    [IsScalarTower T (Polynomial T) O], SH O → IndEt (Polynomial T) O → ∀ i : ℤ,
    Eqv _ (spMap (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := O)).toRingHom)
      (tw q i) := by
  intro q _ T _ _ _ hT hq O _ _ _ _ hSH hInd i
  unfold Eqv
  intro n
  have hfac : ∀ a : O, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E)
      (_ : Algebra.Etale (Polynomial T) E) (φ : E →ₐ[Polynomial T] O), a ∈ φ.range := by
    intro a
    obtain ⟨C, _, _, _, ψ, χ, h⟩ := exists_etale_factor_of_indEt (Polynomial T) O hInd
      (Polynomial (Polynomial T)) (Polynomial.aeval a)
    refine ⟨C, ‹_›, ‹_›, ‹_›, χ, ⟨ψ Polynomial.X, ?_⟩⟩
    have := DFunLike.congr_fun h Polynomial.X
    simpa using this
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have h1 := (GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q i)).1
    haveI := h1 (sp O) n hn
    haveI := h1 (sp (TensorProduct T (FractionRing T) O)) n hn
    exact bijective_of_subsingleton _ 0
  · haveI : IsIntegrallyClosed T := GlobalTheory.AICStalk.isIntegrallyClosed_of_aic hT
    obtain ⟨hH, -⟩ := hSH
    haveI : IsLocalRing O := hH.toIsLocalRing
    haveI : IsDomain O := GlobalTheory.AICStalk.isDomain_of_indEt hInd
    have hinjX : Function.Injective (algebraMap (Polynomial T) O) :=
      GlobalTheory.AICStalk.algebraMap_injective_of_indEt hInd
    have hinj : Function.Injective (algebraMap T O) := by
      rw [IsScalarTower.algebraMap_eq T (Polynomial T) O]
      exact hinjX.comp (Polynomial.C_injective)
    haveI : IsDomain (O ⊗[T] FractionRing T) := isDomain_tensor_fractionRing T O hinj
    haveI : IsDomain (TensorProduct T (FractionRing T) O) :=
      MulEquiv.isDomain _ (Algebra.TensorProduct.comm T (FractionRing T) O).toRingEquiv.toMulEquiv
    have hqO : IsUnit (q : O) := by
      have := hq.map (algebraMap T O)
      rwa [map_natCast] at this
    obtain ⟨z, hz⟩ := hT (Polynomial.cyclotomic q T) (Polynomial.cyclotomic.monic q T) (by
      rw [Polynomial.natDegree_cyclotomic]; exact Nat.totient_pos.2 (NeZero.pos q))
    have hζ : Polynomial.aeval (algebraMap T O z) (Polynomial.cyclotomic q ℤ) = 0 := by
      rw [Polynomial.aeval_algebraMap_apply, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
        Polynomial.map_cyclotomic, hz, map_zero]
    exact GlobalTheory.T.h_zero_pullback_twist_bijective q O (TensorProduct T (FractionRing T) O)
      (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := O)).toRingHom hqO
      ⟨_, hζ⟩ inferInstance (idem_of_domain) (idem_of_domain) i
  · haveI : Subsingleton (H (ZMod q) (sp O) (tw q i) n) := GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) O hSH (tw q i) n hn
    haveI : Subsingleton (H (ZMod q) (sp (TensorProduct T (FractionRing T) O)) (tw q i) n) := by
      rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | h2
      · exact GlobalTheory.T.subsingleton_ht_one_genericFibre_of_sh_etale_cover q T hT hq O hSH hfac i
      · exact GlobalTheory.T.subsingleton_etaleCohomology_genericFibre_henselianLine q T hT hq O hSH hInd n i h2
    exact bijective_of_subsingleton _ 0

end GlobalTheory.EtC.LineLocal
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_equiv_strictHenselian_line_point : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (O : Type) [CommRing O] [Algebra (Polynomial T) O] [Algebra T O] [IsScalarTower T (Polynomial T) O], SH O → IndEt (Polynomial T) O → ∀ i : ℤ, Eqv _ (spMap (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := O)).toRingHom) (tw q i) := by
  first | (exact @GlobalTheory.EtC.LineLocal.eqv_local) | (exact GlobalTheory.EtC.LineLocal.eqv_local) | (intros; apply GlobalTheory.EtC.LineLocal.eqv_local  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC TensorProduct

noncomputable section

namespace GlobalTheory.EtC.LineAcyc

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  dsimp only [spMap]
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (sp A) := by
  dsimp only [spMap]
  rw [CommRingCat.ofHom_id, Spec.map_id]
  exact sch.map_id _

theorem pull_bijective_of_ringEquiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)
    (R : Type) [CommRing R] (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R (spMap (e : A →+* B)) F n) := by
  have h1 : ∀ x, pull R (spMap (e.symm : B →+* A)) F n (pull R (spMap (e : A →+* B)) F n x) = x := by
    intro x
    rw [← pull_comp, ← spMap_comp', show ((e.symm : B →+* A).comp (e : A →+* B)) = RingHom.id A by
      ext; simp, spMap_id', pull_id]
  have h2 : ∀ x, pull R (spMap (e : A →+* B)) F n (pull R (spMap (e.symm : B →+* A)) F n x) = x := by
    intro x
    rw [← pull_comp, ← spMap_comp', show ((e : A →+* B).comp (e.symm : B →+* A)) = RingHom.id B by
      ext; simp, spMap_id', pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem eqv_of_square {X Y X' Y' : Type} [CommRing X] [CommRing Y] [CommRing X'] [CommRing Y']
    (g : X →+* Y) (g' : X' →+* Y') (eX : X ≃+* X') (eY : Y ≃+* Y')
    (h : (eY : Y →+* Y').comp g = g'.comp (eX : X →+* X')) {R : Type} [CommRing R] (F : Shv R) :
    Eqv R (spMap g') F → Eqv R (spMap g) F := by
  intro hg' n
  have hc : spMap (eY : Y →+* Y') ≫ spMap g = spMap g' ≫ spMap (eX : X →+* X') := by
    rw [← spMap_comp', ← spMap_comp', h]
  have key : (pull R (spMap (eY : Y →+* Y')) F n) ∘ (pull R (spMap g) F n) =
      (pull R (spMap g') F n) ∘ (pull R (spMap (eX : X →+* X')) F n) := by
    funext x
    simp only [Function.comp_apply]
    rw [← pull_comp, ← pull_comp, hc]
  have hY := pull_bijective_of_ringEquiv eY R F n
  have hX := pull_bijective_of_ringEquiv eX R F n
  refine (Function.Bijective.of_comp_iff' hY _).mp ?_
  rw [key]
  exact (hg' n).comp hX

end GlobalTheory.EtC.LineAcyc

namespace GlobalTheory.EtC.LineAcyc

theorem affineLine_localAcyclicity_of_strictHenselian_points (core : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
    ∀ (O : Type) [CommRing O] [Algebra (Polynomial T) O] [Algebra T O] [IsScalarTower T (Polynomial T) O],
    SH O → IndEt (Polynomial T) O → ∀ i : ℤ,
    Eqv _ (spMap (Algebra.TensorProduct.includeRight (R := T) (A := FractionRing T) (B := O)).toRingHom) (tw q i)) : C3 := by
  intro q _ T _ _ _ hT hq B _ _ _ _ _ i

  have hB := GlobalTheory.T.etaleCohomology_local_to_global_ringMap_indEtale (ZMod q) (tw q i) (GlobalTheory.T.tateTwist_finitary q i) B B (B ⊗[T] FractionRing T)
    (Algebra.ofId B (B ⊗[T] FractionRing T))

  refine eqv_of_square _ (Algebra.ofId B (B ⊗[T] FractionRing T)).toRingHom (RingEquiv.refl B)
    (Algebra.TensorProduct.comm T (FractionRing T) B).toRingEquiv ?_ _ (hB ?_)
  · ext b
    simp [Algebra.TensorProduct.algebraMap_apply]
  intro O _ _ hO hOi
  letI : Algebra (Polynomial T) O := ((algebraMap B O).comp (algebraMap (Polynomial T) B)).toAlgebra
  letI : Algebra T O := ((algebraMap B O).comp (algebraMap T B)).toAlgebra
  haveI : IsScalarTower T (Polynomial T) O := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap B O (algebraMap T B x) = algebraMap B O (algebraMap (Polynomial T) B (algebraMap T (Polynomial T) x))
    rw [IsScalarTower.algebraMap_apply T (Polynomial T) B x]
  haveI : IsScalarTower T B O := IsScalarTower.of_algebraMap_eq fun x => rfl
  have hOi' : IndEt (Polynomial T) O :=
    isIndEtale_comp_etale (algebraMap (Polynomial T) B) (RingHom.etale_algebraMap.2 inferInstance)
      (algebraMap B O) hOi
  have hc := core q T hT hq O hO hOi' i
  refine eqv_of_square _ _ (Algebra.TensorProduct.rid B B O).toRingEquiv
    ((Algebra.TensorProduct.cancelBaseChange T B B O (FractionRing T)).toRingEquiv.trans
      (Algebra.TensorProduct.comm T O (FractionRing T)).toRingEquiv) ?_ _ hc
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul o b => simp [Algebra.smul_def]
  | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]

end GlobalTheory.EtC.LineAcyc

namespace GlobalTheory.EtC.LineAcyc

theorem c3 : C3 := affineLine_localAcyclicity_of_strictHenselian_points GlobalTheory.T.etaleCohomology_equiv_strictHenselian_line_point

end GlobalTheory.EtC.LineAcyc
end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_cohomology_ind_etale_base_change : GlobalTheory.EtC.C3 := by
  first | (exact @GlobalTheory.EtC.LineAcyc.c3) | (exact GlobalTheory.EtC.LineAcyc.c3) | (intros; apply GlobalTheory.EtC.LineAcyc.c3  <;> assumption)
end
