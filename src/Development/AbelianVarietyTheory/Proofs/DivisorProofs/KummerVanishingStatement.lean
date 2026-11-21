import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDegreeClassesDieOnEtaleCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleFaithfullyFlatRefiningEtaleSurjectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCocycleCoboundaryIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicFaithfullyFlatDescentUnitCocyclesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistOneToRootsOfUnitySectionsInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuValInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.MuTw

noncomputable section
namespace GlobalTheory.EtC.MuTw

theorem appTop_comp_apply' {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Γ(U, ⊤)) :
    (k ≫ g).appTop.hom a = k.appTop.hom (g.appTop.hom a) := by
  rw [Scheme.Hom.comp_appTop]; rfl

theorem isUnit_natCast_of_hom {V U : Scheme.{0}} (g : V ⟶ U) (q : ℕ) (hq : IsUnit (q : Γ(U, ⊤))) :
    IsUnit (q : Γ(V, ⊤)) := by
  have := hq.map g.appTop.hom
  rwa [map_natCast] at this

theorem muVal_pow (q : ℕ) [NeZero q] {U : Scheme.{0}} (y : Sec (muS q) U) : muVal q y ^ q = 1 := by
  have hr := (mem_rootsOfUnity q _).1 (Additive.toMul (ULift.down (α := Additive (rootsOfUnity q Γ(U, ⊤))) y)).2
  change (( _ : Γ(U, ⊤)ˣ) : Γ(U, ⊤)) ^ q = 1
  rw [← Units.val_pow_eq_pow_val, hr, Units.val_one]

theorem etaS_lift_pow (q : ℕ) [NeZero q] (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)) (z : Sec (muS q) V) (a : ℕ)
    (h : muVal q z = ζ.1 ^ a) :
    Sec.map (etaS q) (ofRings.sec (twF q 1) V
      (Submodule.Quotient.mk (Finsupp.single ζ (ULift.up (a : ZMod q))))) = z := by
  refine (etaS_sec q V _).trans ((eta_mk q Γ(V, ⊤) ζ _).trans ?_)
  apply muVal_injective q V
  rw [h]
  change (((Additive.toMul (((a : ZMod q)) • Additive.ofMul (root q ζ)) : rootsOfUnity q Γ(V, ⊤)) :
    Γ(V, ⊤)ˣ) : Γ(V, ⊤)) = _
  rw [smul_eq, toMul_nsmul, toMul_ofMul, root_pow_coe, ZMod.val_natCast]
  exact (pow_eq_pow_mod a (prim_pow q ζ)).symm

end GlobalTheory.EtC.MuTw

namespace GlobalTheory.EtC.MuTw

theorem etaS_surjective : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
    Function.Surjective ((etaS q).hom.app (op U)).hom := by
  intro q _ U hq y
  have hloc : Loc U fun V g => ∃ s : Sec (tw q 1) V, Sec.map (etaS q) s = Sec.res g y := by
    refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.2.2.2.1 U _ ?_
    refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 U _ _ ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q U).1 hq) ?_
    rintro V g ⟨ζ⟩
    refine (GlobalTheory.T.etaleLocal_property_calculus_rules).2.1 V _ _
      ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).2.2.1 ζ (muVal q (Sec.res g y)) (muVal_pow q _)) ?_
    rintro W k ⟨a, ha⟩
    refine ⟨_, etaS_lift_pow q W (Prim.map k.appTop.hom ζ) (Sec.res (k ≫ g) y) a ?_⟩
    rw [muVal_res, appTop_comp_apply', ← muVal_res, ha]
    rfl
  obtain ⟨S, hS, hSy⟩ := hloc
  choose s hs using hSy
  have hsh := (tw q 1).cond
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))),
    isSheaf_iff_isSheaf_of_type] at hsh
  let fam : Presieve.FamilyOfElements ((tw q 1).obj ⋙ forget (ModuleCat.{1} (ULift.{1} (ZMod q)))) S.arrows :=
    fun V g hg => s V g hg
  have hfam : fam.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
    apply GlobalTheory.T.tateTwistOneToRootsOfUnity_sections_injective q Z (isUnit_natCast_of_hom (g₁ ≫ f₁) q hq)
    change Sec.map (etaS q) (Sec.res g₁ (s _ f₁ h₁)) = Sec.map (etaS q) (Sec.res g₂ (s _ f₂ h₂))
    rw [etaS_res, etaS_res, hs, hs]
    apply muVal_injective q Z
    simp only [muVal_res]
    rw [← appTop_comp_apply', ← appTop_comp_apply', e]
  obtain ⟨x, hx, -⟩ := hsh S hS fam hfam
  refine ⟨x, ?_⟩
  have hsep := (muS q).cond
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} (ZMod q)))),
    isSheaf_iff_isSheaf_of_type] at hsep
  refine (hsep S hS).isSeparatedFor.ext (fun V g hg => ?_)
  change Sec.res g (Sec.map (etaS q) x) = Sec.res g y
  rw [← etaS_res]
  have h1 : Sec.res g x = s V g hg := hx g hg
  rw [h1, hs]

end GlobalTheory.EtC.MuTw
end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.EtC.MuTw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistOneToRootsOfUnity_sections_surjective : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Function.Surjective ((etaS q).hom.app (op U)).hom := by
  first | (exact @GlobalTheory.EtC.MuTw.etaS_surjective) | (exact GlobalTheory.EtC.MuTw.etaS_surjective) | (intros; apply GlobalTheory.EtC.MuTw.etaS_surjective  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

open GlobalTheory.EtC.MuTw in

theorem GlobalTheory.EtC.tw_one_mu : ∀ (q : ℕ) [NeZero q], ∃ e : ∀ (C : Type) [CommRing C], IsUnit (q : C) → (onRings (tw q 1)).obj (CommRingCat.of C) ≃+ Additive (rootsOfUnity q C), ∀ (C D : Type) [CommRing C] [CommRing D] (φ : C →+* D) (hC : IsUnit (q : C)) (hD : IsUnit (q : D)) (x : (onRings (tw q 1)).obj (CommRingCat.of C)), ((Additive.toMul (e D hD (((onRings (tw q 1)).map (CommRingCat.ofHom φ)).hom x)) : rootsOfUnity q D) : Dˣ) = Units.map φ.toMonoidHom ((Additive.toMul (e C hC x) : rootsOfUnity q C) : Cˣ) := by
  intro q _
  have hunit : ∀ (C : Type) [CommRing C], IsUnit (q : C) → IsUnit (q : Γ(Spec (CommRingCat.of C), ⊤)) := by
    intro C _ hC
    have := hC.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom
    simpa using this
  let e : ∀ (C : Type) [CommRing C], IsUnit (q : C) → (onRings (tw q 1)).obj (CommRingCat.of C) ≃+ Additive (rootsOfUnity q C) :=
    fun C _ hC =>
      ((AddEquiv.ofBijective ((etaS q).hom.app (op (Spec (CommRingCat.of C)))).hom.toAddMonoidHom
        ⟨GlobalTheory.T.tateTwistOneToRootsOfUnity_sections_injective q _ (hunit C hC), GlobalTheory.T.tateTwistOneToRootsOfUnity_sections_surjective q _ (hunit C hC)⟩).trans AddEquiv.ulift).trans
        (MulEquiv.restrictRootsOfUnity (Scheme.ΓSpecIso (CommRingCat.of C)).commRingCatIsoToRingEquiv.toMulEquiv q).toAdditive
  refine ⟨e, ?_⟩
  intro C D _ _ φ hC hD x
  apply Units.ext
  have h1 := etaS_res q (Spec.map (CommRingCat.ofHom φ)) x
  have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  change (Scheme.ΓSpecIso (CommRingCat.of D)).hom.hom (muVal q (Sec.map (etaS q) (Sec.res (Spec.map (CommRingCat.ofHom φ)) x))) = φ ((Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom (muVal q (Sec.map (etaS q) x)))
  rw [h1, muVal_res]
  exact congrArg (fun f => f.hom (muVal q (Sec.map (etaS q) x))) h2
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistOne_sections_eq_rootsOfUnity : ∀ (q : ℕ) [NeZero q], ∃ e : ∀ (C : Type) [CommRing C], IsUnit (q : C) → (onRings (tw q 1)).obj (CommRingCat.of C) ≃+ Additive (rootsOfUnity q C), ∀ (C D : Type) [CommRing C] [CommRing D] (φ : C →+* D) (hC : IsUnit (q : C)) (hD : IsUnit (q : D)) (x : (onRings (tw q 1)).obj (CommRingCat.of C)), ((Additive.toMul (e D hD (((onRings (tw q 1)).map (CommRingCat.ofHom φ)).hom x)) : rootsOfUnity q D) : Dˣ) = Units.map φ.toMonoidHom ((Additive.toMul (e C hC x) : rootsOfUnity q C) : Cˣ) := by
  first | (exact @GlobalTheory.EtC.tw_one_mu) | (exact GlobalTheory.EtC.tw_one_mu) | (intros; apply GlobalTheory.EtC.tw_one_mu  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC

theorem uCoc_one (A B : Type) [CommRing A] [CommRing B] [Algebra A B] : UCoc A B 1 := by
  unfold UCoc
  simp [Algebra.TensorProduct.one_def]

theorem uCoc_mul {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {u v : (B ⊗[A] B)ˣ}
    (hu : UCoc A B u) (hv : UCoc A B v) : UCoc A B (u * v) := by
  unfold UCoc at *
  simp only [Units.val_mul, map_mul, hu, hv]
  ring

theorem uCoc_pow {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {u : (B ⊗[A] B)ˣ}
    (hu : UCoc A B u) (n : ℕ) : UCoc A B (u ^ n) := by
  induction n with
  | zero => simpa using uCoc_one A B
  | succ n ih => rw [pow_succ]; exact uCoc_mul ih hu

theorem kummer_vanishing : B6h1 := by
  intro q _ A _ hq hu hp
  suffices h : ∀ x : Ht q (sp A) 1 1, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
  intro x
  obtain ⟨Y, f, hfe, hfs, hx⟩ := GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover (ZMod q) (Spec (CommRingCat.of A)) (tw q 1) 1 one_pos x
  obtain ⟨B, g, h, hg, hhf⟩ := GlobalTheory.T.exists_etaleFaithfullyFlat_refining_etale_surjection (CommRingCat.of A) Y f hfe hfs
  letI : Algebra A B := g.hom.toAlgebra
  haveI : Algebra.Etale A B := hg.1
  haveI : Module.FaithfullyFlat A B := hg.2
  have hxB : pull (ZMod q) (spMap (algebraMap A B)) (tw q 1) 1 x = 0 := by
    have : spMap (algebraMap A B) = sch.map h ≫ sch.map f := by
      rw [← sch.map_comp, hhf]; rfl
    rw [this, pull_comp, hx, map_zero]
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.etale_cocycle_coboundary_iff (ZMod q) (tw q 1) A
  obtain ⟨hγ0, hγs, -, -⟩ := hγ B
  obtain ⟨u, rfl⟩ := hγs x hxB
  rw [hγ0]

  obtain ⟨e, he⟩ := GlobalTheory.T.tateTwistOne_sections_eq_rootsOfUnity q
  have hqB : IsUnit (q : (B : Type)) := by simpa using hq.map (algebraMap A B)
  have hqBB : IsUnit (q : B ⊗[A] B) := by simpa using hq.map (algebraMap A (B ⊗[A] B))
  have hqBBB : IsUnit (q : B ⊗[A] (B ⊗[A] B)) := by simpa using hq.map (algebraMap A (B ⊗[A] (B ⊗[A] B)))
  have hUq : ((Additive.toMul (e _ hqBB u.1) : rootsOfUnity q (B ⊗[A] B)) : (B ⊗[A] B)ˣ) ^ q = 1 :=
    (mem_rootsOfUnity _ _).1 (Additive.toMul (e _ hqBB u.1)).2
  have hUc : UCoc A B ((Additive.toMul (e _ hqBB u.1) : rootsOfUnity q (B ⊗[A] B)) : (B ⊗[A] B)ˣ) := by
    have h2 := u.2
    change _ = _ at h2
    have h3 := congrArg (fun y => ((Additive.toMul (e _ hqBBB y) : rootsOfUnity q _) : (B ⊗[A] (B ⊗[A] B))ˣ)) h2
    simp only [AddMonoidHom.add_apply, map_add, toMul_add, Subgroup.coe_mul, LinearMap.toAddMonoidHom_coe] at h3
    rw [he _ _ _ hqBB hqBBB, he _ _ _ hqBB hqBBB, he _ _ _ hqBB hqBBB] at h3
    have h4 := congrArg Units.val h3
    simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, AlgHom.coe_toRingHom] at h4
    exact h4

  set U := ((Additive.toMul (e _ hqBB u.1) : rootsOfUnity q (B ⊗[A] B)) : (B ⊗[A] B)ˣ) with hUdef
  obtain ⟨δ, hδ⟩ := GlobalTheory.T.pic_faithfullyFlat_descent_unitCocycles A
  obtain ⟨hmul, hone, -, -, -⟩ := hδ B
  have hδ1 : δ B 1 = 1 := by
    have := hmul 1 1 (uCoc_one A B) (uCoc_one A B)
    rw [mul_one] at this
    simpa using this
  have hδpow : ∀ n : ℕ, δ B (U ^ n) = δ B U ^ n := by
    intro n
    induction n with
    | zero => simpa using hδ1
    | succ n ih => rw [pow_succ, hmul _ _ (uCoc_pow hUc n) hUc, ih, pow_succ]
  have hδU : δ B U = 1 := hp _ (by rw [← hδpow, hUq, hδ1])
  obtain ⟨w, hw⟩ := (hone U hUc).1 hδU
  let iL : (B : Type) →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeLeft
  let iR : (B : Type) →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeRight
  have hwU : U * Units.map iR.toRingHom.toMonoidHom w = Units.map iL.toRingHom.toMonoidHom w :=
    Units.ext (by simpa [iL, iR] using hw)
  have hWq : Units.map iL.toRingHom.toMonoidHom (w ^ q) = Units.map iR.toRingHom.toMonoidHom (w ^ q) := by
    rw [map_pow, map_pow, ← hwU, mul_pow, hUq, one_mul]
  have hWq' : Units.map iL.toRingHom.toMonoidHom (w ^ q)⁻¹ = Units.map iR.toRingHom.toMonoidHom (w ^ q)⁻¹ := by
    rw [map_inv, map_inv, hWq]
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_algebraMap_eq_of_faithfullyFlat_includeLeft_eq_includeRight A B ((w ^ q : (B : Type)ˣ) : (B : Type)) (by simpa [iL, iR] using congrArg Units.val hWq)
  obtain ⟨a', ha'⟩ := GlobalTheory.T.exists_algebraMap_eq_of_faithfullyFlat_includeLeft_eq_includeRight A B (((w ^ q)⁻¹ : (B : Type)ˣ) : (B : Type)) (by simpa [iL, iR] using congrArg Units.val hWq')
  have haa : a * a' = 1 :=
    FaithfulSMul.algebraMap_injective A B (by rw [map_mul, ha, ha', Units.mul_inv, map_one])
  obtain ⟨v, hv⟩ := hu ⟨a, a', haa, by rw [mul_comm, haa]⟩
  let vB : (B : Type)ˣ := Units.map (algebraMap A B).toMonoidHom v
  have hvB : vB ^ q = w ^ q := by
    apply Units.ext
    rw [← map_pow, ← hv, Units.coe_map]
    exact ha
  have hT : (vB * w⁻¹) ^ q = 1 := by rw [mul_pow, hvB, inv_pow, mul_inv_cancel]
  let Tr : rootsOfUnity q (B : Type) := ⟨vB * w⁻¹, (mem_rootsOfUnity _ _).2 hT⟩
  have hV : Units.map iR.toRingHom.toMonoidHom vB = Units.map iL.toRingHom.toMonoidHom vB := by
    apply Units.ext
    simp [vB, iL, iR]
  refine ⟨(e _ hqB).symm (Additive.ofMul Tr), ?_⟩
  apply (e _ hqBB).injective
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [map_sub, toMul_sub, SubgroupClass.coe_div, he _ _ _ hqB hqBB, he _ _ _ hqB hqBB, AddEquiv.apply_symm_apply]
  change U = Units.map iR.toRingHom.toMonoidHom (vB * w⁻¹) / Units.map iL.toRingHom.toMonoidHom (vB * w⁻¹)
  rw [div_eq_mul_inv, eq_mul_inv_iff_mul_eq, map_mul, map_mul, map_inv, map_inv, hV, ← hwU]
  rw [mul_inv_rev, mul_left_comm, ← mul_assoc U, mul_comm U, mul_assoc, mul_inv_cancel, mul_one]
end GlobalTheory.EtC
end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_etale_vanishing : GlobalTheory.EtC.B6h1 := by
  first | (exact @GlobalTheory.EtC.kummer_vanishing) | (exact GlobalTheory.EtC.kummer_vanishing) | (intros; apply GlobalTheory.EtC.kummer_vanishing  <;> assumption)
end
