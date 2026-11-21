import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfDerHomEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTangentEqOfCrystallineValuesEq

section
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

open Opposite TopologicalSpace

theorem const_of_isAbelianScheme : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → Const A.hom := by
  intro R _ _ A _ hA
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  haveI : GeometricallyIntegral A.hom := GlobalTheory.geometricallyIntegral_of_smooth A.hom
  have hbij := ((GlobalTheory.ProperFunctions.functions_of_isProper).2.2 R A.left A.hom).1
  intro g hg
  have hc : ∀ (U V : A.left.affineOpens) (h : V.1 ≤ U.1),
      A.left.presheaf.map (homOfLE h).op (g (op U)) = g (op V) := by
    intro U V h
    have e := congrFun (congrFun (congrFun hg (op U)) (op V)) (homOfLE h).op
    exact (sub_eq_zero.1 e).symm
  obtain ⟨t, ht, -⟩ := A.left.sheaf.existsUnique_gluing' (fun U : A.left.affineOpens ↦ U.1) ⊤
    (fun _ ↦ homOfLE le_top) (iSup_affineOpens_eq_top A.left).ge (fun U ↦ g (op U)) (by
      intro U V
      refine A.left.sheaf.eq_of_locally_eq' (fun W : {W : A.left.affineOpens // W.1 ≤ U.1 ⊓ V.1} ↦ W.1.1)
        (U.1 ⊓ V.1) (fun W ↦ homOfLE W.2) ?_ _ _ fun W ↦ ?_
      · intro x hx
        obtain ⟨W, hW, hxW, hWUV⟩ := Opens.isBasis_iff_nbhd.mp A.left.isBasis_affineOpens hx
        exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, hWUV⟩, hxW⟩
      · dsimp only
        have e : ∀ {a b c : Opens A.left} (f : b ⟶ a) (f' : c ⟶ b) (x : Γ(A.left, a)),
            A.left.presheaf.map f'.op (A.left.presheaf.map f.op x) = A.left.presheaf.map (f' ≫ f).op x := by
          intros; simp
        refine (e _ _ _).trans ((hc U W.1 (W.2.trans inf_le_left)).trans
          ((hc V W.1 (W.2.trans inf_le_right)).symm.trans (e _ _ _).symm)))
  obtain ⟨r, hr⟩ := hbij.2 t
  refine ⟨r, fun U ↦ ?_⟩
  rw [← ht U.unop, ← hr]
  rfl

end GlobalTheory.LiftSys
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalFunctionsAreConstant_abelianScheme_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → Const A.hom := by
  atlas_forward_decl GlobalTheory.LiftSys.const_of_isAbelianScheme
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ParPt

theorem tanVal_pullForm_ofModule : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (A : Over (Sp R)) (A' : Over (Sp R')) (φ : A'.left ⟶ A.left) (m : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R') (A'.hom ≫ 𝟙 (Sp R')) (algebraMap R R') φ) (v : epsR R' ⟶ A') (hy : (v.left ≫ φ) ≫ A.hom ≫ 𝟙 (Sp R) = spMap (algebraMap R (DualNumber R'))) (f : Form (A.hom ≫ 𝟙 (Sp R))), tanVal v (m.pullForm f) = TrivSqZeroExt.snd ((SqExt.ofModule R R' R').val (v.left ≫ φ) hy f.1) := by
  intro R R' _ _ _ A A' φ m v hy f
  let E := SqExt.ofModule R R' R'
  let E' := SqExt.dual R'
  have hy' := pt_w v
  have hc : ∀ r : R, RingHom.id (DualNumber R') (algebraMap R (DualNumber R') r) =
      algebraMap R' (DualNumber R') (algebraMap R R' r) := fun r =>
    IsScalarTower.algebraMap_apply R R' (DualNumber R') r
  have e₀ : spMap (RingHom.id R') ≫ spMap (E.π : E.C →+* E.B) ≫ v.left ≫ φ =
      (spMap (E'.π : E'.C →+* E'.B) ≫ v.left) ≫ φ := by
    rw [Category.assoc, ← Category.assoc, ← Cris.spMap_comp]
    rfl
  have e : spMap (RingHom.id (DualNumber R')) ≫ v.left ≫ φ = v.left ≫ φ := by
    rw [Cris.spMap_id, Category.id_comp]
  let Φ : E.thick _ (E.red_w hy) ⟶ m.obj (E'.thick _ (E'.red_w hy')) :=
    { φ := { RingHom.id (DualNumber R') with commutes' := hc }
      φ₀ := RingHom.id R'
      comm := fun b => rfl
      dp := isDPMorphism_sqDP E.sq E'.sq _ fun a ha => ha
      pt := e₀ }
  let a : Thick.triv E.C _ hy ⟶ m.obj (Thick.triv E'.C _ hy') :=
    Thick.trivHom { RingHom.id (DualNumber R') with commutes' := hc } e
  let b : Thick.triv E.B _ (E.red_w hy) ⟶ m.obj (Thick.triv E'.B _ (E'.red_w hy')) :=
    Thick.trivHom { RingHom.id R' with commutes' := fun _ => rfl } e₀
  have k1 := Form.ev_sq f a (m.functor.map (E'.idHom hy')) (E.idHom hy) Φ rfl rfl fun _ => rfl
  have k2 := Form.ev_sq f b (m.functor.map (E'.secHom (E'.red_w hy') E'.i E'.π_i))
    (E.secHom (E.red_w hy) E.i E.π_i) Φ rfl rfl fun c => rfl
  have k : E'.val v.left hy' (m.pullForm f).1 = E.val (v.left ≫ φ) hy f.1 :=
    (congrArg₂ (fun u v : E'.C => u - v) k2 k1).trans
      (add_sub_add_right_eq_sub (G := E'.C) _ _ _)
  rw [tanVal_apply]
  exact congrArg (TrivSqZeroExt.snd (R := R')) k

end GlobalTheory.ParPt
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_value_pullback_crystalline_form_dual_numbers : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (A : Over (Sp R)) (A' : Over (Sp R')) (φ : A'.left ⟶ A.left) (m : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R') (A'.hom ≫ 𝟙 (Sp R')) (algebraMap R R') φ) (v : epsR R' ⟶ A') (hy : (v.left ≫ φ) ≫ A.hom ≫ 𝟙 (Sp R) = spMap (algebraMap R (DualNumber R'))) (f : Form (A.hom ≫ 𝟙 (Sp R))), tanVal v (m.pullForm f) = TrivSqZeroExt.snd ((SqExt.ofModule R R' R').val (v.left ≫ φ) hy f.1) := by
  atlas_forward_decl GlobalTheory.ParPt.tanVal_pullForm_ofModule
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct

namespace GlobalTheory.BaseChangeForm

theorem existsUnique_of_baseChange {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    {G G' : Type} {F F' : Type 1} [AddCommGroup G] [Module R G] [AddCommGroup G'] [Module R' G']
    [AddCommGroup F] [Module R F] [AddCommGroup F'] [Module R' F']
    (c : F →ₗ[R] G) (hc : Function.Surjective c) (c' : F' →ₗ[R'] G')
    (p : F →ₛₗ[algebraMap R R'] F') (e : R' ⊗[R] G ≃ₗ[R'] G') (hp : ∀ f, c' (p f) = e (1 ⊗ₜ c f))
    (l : G →ₗ[R] R') :
    ∃! ψ : F' →ₗ[R'] R', (∀ f, c' f = 0 → ψ f = 0) ∧ ∀ f, ψ (p f) = l (c f) := by
  have key : ∀ x : R' ⊗[R] G, ∃ f' : F', c' f' = e x ∧
      ∀ ψ : F' →ₗ[R'] R', (∀ f, ψ (p f) = l (c f)) → ψ f' = LinearMap.liftBaseChange R' l x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp, fun ψ _ ↦ by simp⟩
    | tmul b y =>
      obtain ⟨f, rfl⟩ := hc y
      refine ⟨b • p f, ?_, fun ψ hψ ↦ ?_⟩
      · rw [map_smul, hp, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      · rw [map_smul, hψ, LinearMap.liftBaseChange_tmul]
    | add x y hx hy =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨b, hb, hb'⟩ := hy
      exact ⟨a + b, by rw [map_add, map_add, ha, hb],
        fun ψ hψ ↦ by rw [map_add, map_add, ha' ψ hψ, hb' ψ hψ]⟩
  refine ⟨LinearMap.liftBaseChange R' l ∘ₗ e.symm.toLinearMap ∘ₗ c', ⟨fun f hf ↦ ?_, fun f ↦ ?_⟩,
    fun ψ hψ ↦ LinearMap.ext fun f ↦ ?_⟩
  · simp [hf]
  · simp [hp]
  · obtain ⟨f', h1, h2⟩ := key (e.symm (c' f))
    have h3 : ψ (f - f') = 0 := hψ.1 _ (by rw [map_sub, h1, LinearEquiv.apply_symm_apply, sub_self])
    rw [map_sub, sub_eq_zero] at h3
    rw [h3, h2 ψ hψ.2]
    rfl

set_option maxHeartbeats 1600000 in

theorem existsUnique_functional : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] [Algebra R R'] (A' : Over (Sp R')) (φ : A'.left ⟶ A.left), IsPullback φ A'.hom A.hom (spMap (algebraMap R R')) → ∀ (m : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R') (A'.hom ≫ 𝟙 (Sp R')) (algebraMap R R') φ) (l : GlobForm (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R'), ∃! ψ : Form (A'.hom ≫ 𝟙 (Sp R')) →ₗ[R'] R', (∀ f, cmpForm (A'.hom ≫ 𝟙 (Sp R')) f = 0 → ψ f = 0) ∧ ∀ f, ψ (m.pullForm f) = l (GlobalTheory.LieDual.glob (A.hom ≫ 𝟙 (Sp R)) f) := by
  intro hC hH R _ A _ g hab hdim R' _ _ A' φ hφ m l
  obtain ⟨e, he⟩ : ∃ e : R' ⊗[R] GlobForm (A.hom ≫ 𝟙 (Sp R)) ≃ₗ[R'] GlobForm (A'.hom ≫ 𝟙 (Sp R')),
      ∀ c, IsPullForm m.w c (e (1 ⊗ₜ c)) :=
    ((hH R A g hab hdim).2.2.2.2.2 R' A'.left A'.hom φ hφ).2.1
  have hp : ∀ f, GlobalTheory.LieDual.glob _ (m.pullForm f) = e (1 ⊗ₜ GlobalTheory.LieDual.glob _ f) := fun f ↦
    (GlobalTheory.T.affinePairRestriction_injective_firstCohomology φ (A'.hom ≫ 𝟙 (Sp R'))).2.1 ((GlobalTheory.LieDual.isPullForm_glob m f).symm.trans (he _))
  obtain ⟨ψ, hψ, hu⟩ := existsUnique_of_baseChange (GlobalTheory.LieDual.glob (A.hom ≫ 𝟙 (Sp R)))
    (GlobalTheory.LieDual.glob_surjective hC hH A g hab hdim) (GlobalTheory.LieDual.glob (A'.hom ≫ 𝟙 (Sp R')))
    m.pullForm e hp l
  exact ⟨ψ, ⟨fun f hf ↦ hψ.1 f (congrArg Subtype.val hf), hψ.2⟩,
    fun χ hχ ↦ hu χ ⟨fun f hf ↦ hχ.1 f (Subtype.ext hf), hχ.2⟩⟩

end GlobalTheory.BaseChangeForm
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_forms_functional_abelian_base_change : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] [Algebra R R'] (A' : Over (Sp R')) (φ : A'.left ⟶ A.left), IsPullback φ A'.hom A.hom (spMap (algebraMap R R')) → ∀ (m : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R') (A'.hom ≫ 𝟙 (Sp R')) (algebraMap R R') φ) (l : GlobForm (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R'), ∃! ψ : Form (A'.hom ≫ 𝟙 (Sp R')) →ₗ[R'] R', (∀ f, cmpForm (A'.hom ≫ 𝟙 (Sp R')) f = 0 → ψ f = 0) ∧ ∀ f, ψ (m.pullForm f) = l (GlobalTheory.LieDual.glob (A.hom ≫ 𝟙 (Sp R)) f) := by
  atlas_forward_decl GlobalTheory.BaseChangeForm.existsUnique_functional
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TanAdd

theorem tanVal_const_point {S : Type} [CommRing S] {A : Over (Sp S)} (c : epsR S ⟶ A) (p : Sp S ⟶ A.left)
    (hc : c.left = spMap (algebraMap S (DualNumber S)) ≫ p) (f : Form (A.hom ≫ 𝟙 _)) :
    tanVal c f = 0 := by
  have e : GlobalTheory.GrpTangent.epsScale (0 : S) ≫ c = c := by
    refine Over.OverMorphism.ext ?_
    have h := Over.w (GlobalTheory.GrpTangent.epsScale (0 : S))
    rw [Over.comp_left, hc, ← Category.assoc]
    exact congrArg (· ≫ p) h
  rw [← e, tanVal_epsScale, zero_mul]

theorem isTangent_iff_reduction_eq_one {S : Type} [CommRing S] {A : Over (Sp S)} [GrpObj A] (z : epsR S ⟶ A) :
    IsTangent z ↔ spOver (TrivSqZeroExt.fstHom S S S) ≫ z = 1 := by
  have h1 : (1 : Over.mk (spMap (algebraMap S S)) ⟶ A).left = η[A].left := by
    rw [Hom.one_def, Over.comp_left]
    have : (CartesianMonoidalCategory.toUnit (Over.mk (spMap (algebraMap S S)))).left = 𝟙 (Sp S) := by
      have h := Over.w (CartesianMonoidalCategory.toUnit (Over.mk (spMap (algebraMap S S))))
      refine (Category.comp_id _).symm.trans (h.trans ?_)
      exact Spec.map_id _
    rw [this]
    exact Category.id_comp _
  constructor
  · intro h
    exact Over.OverMorphism.ext (h.trans h1.symm)
  · intro h
    exact (congrArg Over.Hom.left h).trans h1

theorem translate_const (hC : CrystallineSmoothLift) (hH : AbelianHodgeDeRham) (S : Type) [CommRing S]
    (A : Over (Sp S)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (c : epsR S ⟶ A) (p : Sp S ⟶ A.left)
    (hc : c.left = spMap (algebraMap S (DualNumber S)) ≫ p) (y : epsR S ⟶ A) :
    (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ y.left =
      spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ c.left ↔ IsTangent (y * c⁻¹)) ∧
      ∀ f, tanVal y f = tanVal (y * c⁻¹) f := by
  refine ⟨?_, fun f ↦ ?_⟩
  · rw [isTangent_iff_reduction_eq_one, MonObj.comp_mul, GrpObj.comp_inv, mul_inv_eq_one]
    exact ⟨fun h ↦ Over.OverMorphism.ext h, fun h ↦ congrArg Over.Hom.left h⟩
  · have h := tanVal_mul_all hC hH S A g hA hg f (y * c⁻¹) c
    rw [inv_mul_cancel_right, tanVal_const_point c p hc f, add_zero] at h
    exact h

end GlobalTheory.TanAdd
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_dual_number_point_inverse_constant_tangent : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (S : Type) [CommRing S] (A : Over (Sp S)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (c : epsR S ⟶ A) (p : Sp S ⟶ A.left), c.left = spMap (algebraMap S (DualNumber S)) ≫ p → ∀ y : epsR S ⟶ A, (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ y.left = spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ c.left ↔ IsTangent (y * c⁻¹)) ∧ ∀ f, tanVal y f = tanVal (y * c⁻¹) f := by
  atlas_forward_decl GlobalTheory.TanAdd.translate_const
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ParPt

theorem t4 : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (A : Over (Sp R)) (A' : Over (Sp R')) (φ : A'.left ⟶ A.left) (m : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R') (A'.hom ≫ 𝟙 (Sp R')) (algebraMap R R') φ) (v : epsR R' ⟶ A') (hy : (v.left ≫ φ) ≫ A.hom ≫ 𝟙 (Sp R) = spMap (algebraMap R (DualNumber R'))) (f : Form (A.hom ≫ 𝟙 (Sp R))), tanVal v (m.pullForm f) = TrivSqZeroExt.snd ((SqExt.ofModule R R' R').val (v.left ≫ φ) hy f.1) := GlobalTheory.T.tangent_value_pullback_crystalline_form_dual_numbers

theorem t5 : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] [Algebra R R'] (A' : Over (Sp R')) (φ : A'.left ⟶ A.left), IsPullback φ A'.hom A.hom (spMap (algebraMap R R')) → ∀ (m : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R') (A'.hom ≫ 𝟙 (Sp R')) (algebraMap R R') φ) (l : GlobForm (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R'), ∃! ψ : Form (A'.hom ≫ 𝟙 (Sp R')) →ₗ[R'] R', (∀ f, cmpForm (A'.hom ≫ 𝟙 (Sp R')) f = 0 → ψ f = 0) ∧ ∀ f, ψ (m.pullForm f) = l (GlobalTheory.LieDual.glob (A.hom ≫ 𝟙 (Sp R)) f) := GlobalTheory.T.existsUnique_forms_functional_abelian_base_change

theorem t6 : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (S : Type) [CommRing S] (A : Over (Sp S)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (c : epsR S ⟶ A) (p : Sp S ⟶ A.left), c.left = spMap (algebraMap S (DualNumber S)) ≫ p → ∀ y : epsR S ⟶ A, (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ y.left = spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ c.left ↔ IsTangent (y * c⁻¹)) ∧ ∀ f, tanVal y f = tanVal (y * c⁻¹) f := GlobalTheory.T.translate_dual_number_point_inverse_constant_tangent

section Main

variable {R : Type} [CommRing R] (A : Over (Sp R)) (V : A.left.affineOpens)

local notation "𝔰" => A.hom ≫ 𝟙 (Sp R)
local notation "𝔅" => Sec (A.hom ≫ 𝟙 (Sp R)) (Subtype.val V)
set_option quotPrecheck false in
local notation "𝔄" => (Over.pullback (spMap (algebraMap R (Sec (A.hom ≫ 𝟙 (Sp R)) (Subtype.val V))))).obj A
local notation "𝔣" => pullback.fst A.hom (spMap (algebraMap R (Sec (A.hom ≫ 𝟙 (Sp R)) (Subtype.val V))))

theorem affPt_hom : affPt (𝔰) V ≫ A.hom = spMap (algebraMap R 𝔅) :=
  (congrArg (affPt (𝔰) V ≫ ·) (Category.comp_id A.hom).symm).trans (affPt_w _ V)

theorem derHom_hom (δ : Ω[𝔅⁄R] →ₗ[𝔅] 𝔅) :
    (spMap (derHom δ : 𝔅 →+* DualNumber 𝔅) ≫ affPt (𝔰) V) ≫ A.hom =
      spMap (algebraMap 𝔅 (DualNumber 𝔅)) ≫ spMap (algebraMap R 𝔅) := by
  rw [Category.assoc, affPt_hom, ← Cris.spMap_comp, ← Cris.spMap_comp, AlgHom.comp_algebraMap,
    ← IsScalarTower.algebraMap_eq]

def ptOf (δ : Ω[𝔅⁄R] →ₗ[𝔅] 𝔅) : epsR 𝔅 ⟶ 𝔄 :=
  Over.homMk (pullback.lift (spMap (derHom δ : 𝔅 →+* DualNumber 𝔅) ≫ affPt (𝔰) V)
    (spMap (algebraMap 𝔅 (DualNumber 𝔅))) (derHom_hom A V δ)) (pullback.lift_snd _ _ _)

theorem ptOf_fst (δ : Ω[𝔅⁄R] →ₗ[𝔅] 𝔅) :
    (ptOf A V δ).left ≫ 𝔣 = spMap (derHom δ : 𝔅 →+* DualNumber 𝔅) ≫ affPt (𝔰) V :=
  pullback.lift_fst _ _ _

theorem ptOf_snd (δ : Ω[𝔅⁄R] →ₗ[𝔅] 𝔅) :
    (ptOf A V δ).left ≫ pullback.snd A.hom (spMap (algebraMap R 𝔅)) = spMap (algebraMap 𝔅 (DualNumber 𝔅)) :=
  pullback.lift_snd _ _ _

def basePt : Sp 𝔅 ⟶ (𝔄).left :=
  pullback.lift (affPt (𝔰) V) (𝟙 _) (by rw [affPt_hom, Category.id_comp])

theorem ptOf_zero : (ptOf A V 0).left = spMap (algebraMap 𝔅 (DualNumber 𝔅)) ≫ basePt A V := by
  refine pullback.hom_ext ?_ ?_
  · rw [ptOf_fst, basePt, Category.assoc, pullback.lift_fst]
    congr 2
    ext b <;> simp [derHom, TrivSqZeroExt.algebraMap_eq_inl']
  · rw [ptOf_snd, basePt, Category.assoc, pullback.lift_snd]
    exact (Category.comp_id _).symm

theorem fst_derHom_spMap (δ : Ω[𝔅⁄R] →ₗ[𝔅] 𝔅) : spMap (TrivSqZeroExt.fstHom 𝔅 𝔅 𝔅).toRingHom ≫
    spMap (derHom δ : 𝔅 →+* DualNumber 𝔅) = 𝟙 _ := by
  refine (Cris.spMap_comp _ _).symm.trans ((congrArg spMap ?_).trans (Cris.spMap_id _))
  ext b
  exact fst_derHom δ b

theorem ptOf_red (δ : Ω[𝔅⁄R] →ₗ[𝔅] 𝔅) : spMap (TrivSqZeroExt.fstHom 𝔅 𝔅 𝔅).toRingHom ≫ (ptOf A V δ).left =
    spMap (TrivSqZeroExt.fstHom 𝔅 𝔅 𝔅).toRingHom ≫ (ptOf A V 0).left := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, ptOf_fst, ptOf_fst, ← Category.assoc, ← Category.assoc,
      fst_derHom_spMap, fst_derHom_spMap]
  · rw [Category.assoc, Category.assoc, ptOf_snd, ptOf_snd]

theorem over_fst (y : epsR 𝔅 ⟶ 𝔄) : (y.left ≫ 𝔣) ≫ 𝔰 = spMap (algebraMap R (DualNumber 𝔅)) := by
  rw [← Category.assoc]
  refine (Category.comp_id _).trans ?_
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  erw [Over.w y]
  change spMap _ ≫ spMap _ = _
  rw [← Cris.spMap_comp, ← IsScalarTower.algebraMap_eq]

theorem isMor_fst : IsMor (dp0 R) (𝔰) (dp0 𝔅) ((𝔄).hom ≫ 𝟙 (Sp 𝔅)) (algebraMap R 𝔅) 𝔣 :=
  IsMor.of_dividedPowersZeroIdeal _ (by rw [Category.comp_id, Category.comp_id]; exact pullback.condition)

theorem tanVal_ptOf (δ : Ω[𝔅⁄R] →ₗ[𝔅] 𝔅) (f : Form (𝔰)) :
    tanVal (ptOf A V δ) ((isMor_fst A V).pullForm f) = δ ((GlobalTheory.LieDual.glob (𝔰) f).1 (Opposite.op V)) :=
  (t4 R 𝔅 A 𝔄 𝔣 (isMor_fst A V) (ptOf A V δ) (over_fst A V _) f).trans
    (snd_val_derHom (𝔰) V δ _ (over_fst A V _) (ptOf_fst A V δ).symm f)

variable (hC : CrystallineSmoothLift) (hH : AbelianHodgeDeRham) [GrpObj A] (g : ℕ) (hab : IsAbelianScheme A)
  (hdim : SmoothOfRelativeDimension g A.hom)

include hC hH hab hdim in
theorem key (l : GlobForm 𝔰 →ₗ[R] 𝔅) :
    ∃! δ : Ω[𝔅⁄R] →ₗ[𝔅] 𝔅, ∀ w : GlobForm 𝔰, δ (w.1 (Opposite.op V)) = l w := by
  have hφ : IsGrpPullback (𝔄) A (spMap (algebraMap R 𝔅)) (𝔣) := isGrpPullback_pullback A _
  have habB := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hab hφ
  have hdimB : SmoothOfRelativeDimension g (𝔄).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback hφ.1 hdim
  have hglob := GlobalTheory.LieDual.glob_surjective hC hH A g hab hdim
  have uniq : ∀ δ₁ δ₂ : Ω[𝔅⁄R] →ₗ[𝔅] 𝔅, (∀ w : GlobForm 𝔰, δ₁ (w.1 (Opposite.op V)) = l w) →
      (∀ w : GlobForm 𝔰, δ₂ (w.1 (Opposite.op V)) = l w) → δ₁ = δ₂ := by
    intro δ₁ δ₂ h₁ h₂
    have T₁ := t6 hC hH 𝔅 𝔄 g habB hdimB (ptOf A V 0) (basePt A V) (ptOf_zero A V) (ptOf A V δ₁)
    have T₂ := t6 hC hH 𝔅 𝔄 g habB hdimB (ptOf A V 0) (basePt A V) (ptOf_zero A V) (ptOf A V δ₂)
    have ht₁ := T₁.1.1 (ptOf_red A V δ₁)
    have ht₂ := T₂.1.1 (ptOf_red A V δ₂)
    have k₁ : ∀ f, tanVal (ptOf A V δ₁ * (ptOf A V 0)⁻¹) ((isMor_fst A V).pullForm f) = l (GlobalTheory.LieDual.glob (𝔰) f) :=
      fun f ↦ (T₁.2 _).symm.trans ((tanVal_ptOf A V δ₁ f).trans (h₁ _))
    have k₂ : ∀ f, tanVal (ptOf A V δ₂ * (ptOf A V 0)⁻¹) ((isMor_fst A V).pullForm f) = l (GlobalTheory.LieDual.glob (𝔰) f) :=
      fun f ↦ (T₂.2 _).symm.trans ((tanVal_ptOf A V δ₂ f).trans (h₂ _))
    have hψ := (t5 hC hH R A g hab hdim 𝔅 𝔄 𝔣 hφ.1 (isMor_fst A V) l).unique
      ⟨fun f hf ↦ GlobalTheory.TanVanish.tanVal_eq_zero_of_cmpForm_eq_zero 𝔅 𝔄 _ f hf, k₁⟩
      ⟨fun f hf ↦ GlobalTheory.TanVanish.tanVal_eq_zero_of_cmpForm_eq_zero 𝔅 𝔄 _ f hf, k₂⟩
    have hv := GlobalTheory.LieInj.tangent_eq_of_tanVal_eq hC hH 𝔅 𝔄 g habB hdimB _ _ ht₁ ht₂
      fun f ↦ LinearMap.congr_fun hψ f
    have hy : ptOf A V δ₁ = ptOf A V δ₂ := mul_right_cancel hv
    apply eq_of_affPt_eq (𝔰) V
    rw [← ptOf_fst, ← ptOf_fst, hy]
  obtain ⟨ψ, ⟨hψ0, hψ⟩, -⟩ := t5 hC hH R A g hab hdim 𝔅 𝔄 𝔣 hφ.1 (isMor_fst A V) l
  obtain ⟨v, hv, hvψ⟩ := GlobalTheory.LieDual.exists_tangent_of_functional hC hH 𝔅 𝔄 g habB hdimB ψ hψ0
  have T := t6 hC hH 𝔅 𝔄 g habB hdimB (ptOf A V 0) (basePt A V) (ptOf_zero A V) (v * ptOf A V 0)
  have hvc : v * ptOf A V 0 * (ptOf A V 0)⁻¹ = v := mul_inv_cancel_right v _
  have hr := T.1.2 (hvc.symm ▸ hv)
  have hred' : spMap (TrivSqZeroExt.fstHom 𝔅 𝔅 𝔅).toRingHom ≫ ((v * ptOf A V 0).left ≫ 𝔣) = affPt (𝔰) V := by
    rw [← Category.assoc, hr, Category.assoc, ptOf_fst, ← Category.assoc, fst_derHom_spMap, Category.id_comp]
  obtain ⟨δ, hδ⟩ := exists_derHom (𝔰) V _ (over_fst A V _) hred'
  have hmain : ∀ w : GlobForm 𝔰, δ (w.1 (Opposite.op V)) = l w := by
    intro w
    obtain ⟨f, rfl⟩ := hglob w
    have e1 := snd_val_derHom (𝔰) V δ _ (over_fst A V (v * ptOf A V 0)) hδ f
    have e2 := t4 R 𝔅 A 𝔄 𝔣 (isMor_fst A V) (v * ptOf A V 0) (over_fst A V _) f
    have e3 : tanVal (v * ptOf A V 0) ((isMor_fst A V).pullForm f) = l (GlobalTheory.LieDual.glob (𝔰) f) :=
      (T.2 _).trans ((congrArg (fun z ↦ tanVal z ((isMor_fst A V).pullForm f)) hvc).trans ((hvψ _).trans (hψ f)))
    exact e1.symm.trans (e2.symm.trans e3)
  exact ⟨δ, hmain, fun δ' h' ↦ uniq δ' δ h' hmain⟩

end Main

theorem exists_unique_of_globForm : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (U : AffOp A.left) (l : GlobForm A.hom →ₗ[R] Sec A.hom U.unop.1), ∃! δ : Ω[Sec A.hom U.unop.1⁄R] →ₗ[Sec A.hom U.unop.1] Sec A.hom U.unop.1, ∀ w : GlobForm A.hom, δ (w.1 U) = l w := by
  intro hC hH R _ A _ g hab hdim U l
  have k := fun l ↦ key A U.unop hC hH g hab hdim l
  rw [Category.comp_id] at k
  exact k l

end GlobalTheory.ParPt
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_vectorField_of_globalOneForm_values : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (U : AffOp A.left) (l : GlobForm A.hom →ₗ[R] Sec A.hom U.unop.1), ∃! δ : Ω[Sec A.hom U.unop.1⁄R] →ₗ[Sec A.hom U.unop.1] Sec A.hom U.unop.1, ∀ w : GlobForm A.hom, δ (w.1 U) = l w := by
  atlas_forward_decl GlobalTheory.ParPt.exists_unique_of_globForm
end

section
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct
namespace GlobalTheory.ParForm

theorem isBaseChange_of_dual {R B M N : Type} [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N] [Module.Finite R M] [Module.Projective R M]
    [Module.Finite B N] [Module.Projective B N] (f : M →ₗ[R] N)
    (h : ∀ l : M →ₗ[R] B, ∃! δ : N →ₗ[B] B, ∀ w, δ (f w) = l w) : IsBaseChange B f := by
  let F : B ⊗[R] M →ₗ[B] N := f.liftBaseChange B
  have hF : ∀ w, F (1 ⊗ₜ w) = f w := fun w ↦ by simp [F]
  have hd : Function.Bijective F.dualMap := by
    rw [Function.bijective_iff_existsUnique]
    intro φ
    obtain ⟨δ, h1, h2⟩ := h ((φ.restrictScalars R).comp (TensorProduct.mk R B M 1))
    refine ⟨δ, ?_, fun δ' e ↦ h2 δ' fun w ↦ ?_⟩
    · refine (LinearMap.liftBaseChangeEquiv B).symm.injective (LinearMap.ext fun w ↦ ?_)
      simpa [hF] using h1 w
    · rw [← hF]
      exact LinearMap.congr_fun e (1 ⊗ₜ w)
  have hdd : Function.Bijective F.dualMap.dualMap :=
    (LinearEquiv.ofBijective _ hd).dualMap.bijective
  have hb : Function.Bijective F := by
    have e : ⇑(Module.Dual.eval B N) ∘ ⇑F = ⇑F.dualMap.dualMap ∘ ⇑(Module.Dual.eval B (B ⊗[R] M)) :=
      funext fun x ↦ rfl
    rw [← Function.Bijective.of_comp_iff' (Module.bijective_dual_eval B N), e]
    exact hdd.comp (Module.bijective_dual_eval B _)
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective F hb) hF

theorem smooth_sec {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hs : Smooth s)
    (U : X.affineOpens) : Algebra.Smooth R (Sec s U.1) := by
  have h1 : RingHom.Smooth (s.appLE ⊤ U.1 le_top).hom :=
    HasRingHomProperty.appLE @Smooth s hs ⟨⊤, isAffineOpen_top _⟩ U le_top
  have h2 : RingHom.Smooth (secMap s U.1).hom :=
    RingHom.Smooth.respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h1
  exact h2

theorem par : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Par A.hom := by
  intro H H' R _ A _ g hA hg U
  have hs : Smooth A.hom := SmoothOfRelativeDimension.smooth g A.hom
  have := smooth_sec A.hom hs U.unop
  obtain ⟨-, -, ⟨h1, h2, -⟩, -⟩ := H' R A g hA hg
  exact isBaseChange_of_dual _ (GlobalTheory.T.exists_unique_vectorField_of_globalOneForm_values H H' R A g hA hg U)

end GlobalTheory.ParForm
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_differentials_from_globalForms : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Par A.hom := by
  atlas_forward_decl GlobalTheory.ParForm.par
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem good_of_isAbelianScheme : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R]
    [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → Good A.hom := by
  intro HC HH R _ _ A _ g hA hg
  have hs : Smooth A.hom := hA.smooth
  have hp : IsProper A.hom := hA.proper
  have hsep : IsSeparated A.hom := inferInstance
  have hqc : QuasiCompact A.hom := inferInstance
  have bij := HC.bijective_cechDeRhamComparison_degreeOne A.hom hs hsep hqc
  obtain ⟨-, -, ⟨-, hproj, -⟩, -, ⟨hcl, hinj, -⟩, -⟩ := HH R A g hA hg
  have key : ∀ f : Form A.hom, cmp1 A.hom (Form.cl A.hom f) = clForm A.hom (cmpForm A.hom f) :=
    comparison_formClass A.hom
  refine ⟨GlobalTheory.T.globalFunctionsAreConstant_abelianScheme_noetherian R A hA, GlobalTheory.T.abelianScheme_differentials_from_globalForms HC HH R A g hA hg, hproj, fun w ↦ ?_, fun f ↦ ?_⟩
  · have hw : w ∈ ClosedForm A.hom := hcl ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := bij.2 (clForm A.hom ⟨w, hw⟩)
    have h1 : clForm A.hom ⟨w, hw⟩ ∈ CechHodgeFiltration A.hom := (cechHodgeFiltration_eq_range A.hom).symm ▸ ⟨_, rfl⟩
    have h2 : c ∈ F1 A.hom := by
      change toH1O A.hom c = 0
      apply cmpO_injective R A.left A.hom
      rw [← structureSheaf_comparison_comm, hc, map_zero]
      exact h1
    rw [hodgeFiltration_eq_range] at h2
    obtain ⟨f, rfl⟩ := h2
    refine ⟨f, ?_⟩
    have := hinj ((key f).symm.trans hc)
    exact congrArg Subtype.val this
  · constructor
    · intro h
      apply hinj
      rw [← key, h, map_zero, map_zero]
    · intro h
      apply bij.1
      rw [key, h, map_zero, map_zero]

end GlobalTheory.LiftSys
end
end

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodForSquareZeroLiftClassification_of_abelianScheme : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Good A.hom := by
  atlas_forward_decl GlobalTheory.LiftSys.good_of_isAbelianScheme
end
