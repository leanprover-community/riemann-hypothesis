import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaUniformisationComplexAbelianVarietiesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliPrimePowerFullLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyLevelQuot
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfRigidifiedFaithfullyFlatDescent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfSurjectiveAppTopOfSection
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjRigidClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleDeeperLevelCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NsmulMemSmulTop
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLiftOfNil
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverCompOfIsFiniteNoetherianBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverBaseChangeAndFiniteRestrict
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliRepOfBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfBaseEq

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ObjDescent

theorem isGrpPullback_id {S S₂ : Scheme.{0}} {G G' : Over S} {G₂ : Over S₂} [GrpObj G] [GrpObj G'] [GrpObj G₂]
    {q : S₂ ⟶ S} [Flat q] [Surjective q] {a : G₂.left ⟶ G.left} {c : G₂.left ⟶ G'.left}
    (h : IsGrpPullback G₂ G q a) (h' : IsGrpPullback G₂ G' q c) (φ : G.left ⟶ G'.left) [IsIso φ] (e : a ≫ φ = c)
    (w : φ ≫ G'.hom = G.hom ≫ 𝟙 S) : IsGrpPullback G G' (𝟙 S) φ := by
  refine ⟨IsPullback.of_horiz_isIso ⟨w⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let r := pullback.fst T.hom q
  have : Epi r := Flat.epi_of_flat_of_surjective _
  let T' : Over S₂ := Over.mk (pullback.snd T.hom q)
  have up : ∀ z : T ⟶ G, ∃ z' : T' ⟶ G₂, r ≫ z.left = z'.left ≫ a := fun z =>
    ⟨Over.homMk (h.1.lift (r ≫ z.left) (pullback.snd T.hom q)
      (by rw [Category.assoc, Over.w z]; exact pullback.condition)) (h.1.lift_snd _ _ _),
      (h.1.lift_fst _ _ _).symm⟩
  obtain ⟨x', hx'⟩ := up x
  obtain ⟨y', hy'⟩ := up y
  let R : Over.mk (T'.hom ≫ q) ⟶ T := Over.homMk r pullback.condition
  let R' : Over.mk (T'.hom ≫ q) ⟶ Over.mk (T.hom ≫ 𝟙 S) :=
    Over.homMk r ((congrArg (r ≫ ·) (Category.comp_id T.hom)).trans pullback.condition)
  have e₁ := h.2 T' x' y' (R ≫ x) (R ≫ y) hx' hy'
  have e₂ := h'.2 T' x' y' (R' ≫ x₀) (R' ≫ y₀)
    (by show r ≫ x₀.left = _; rw [hx, ← Category.assoc, hx', Category.assoc, e])
    (by show r ≫ y₀.left = _; rw [hy, ← Category.assoc, hy', Category.assoc, e])
  rw [← MonObj.comp_mul] at e₁ e₂
  rw [← cancel_epi r, ← Category.assoc]
  refine e₂.trans ?_
  rw [← e, ← Category.assoc]
  exact congrArg (· ≫ φ) e₁.symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {b : Base l B} {b' : Base l B'} {b'' : Base l B''}
  {S S₂ : Scheme.{0}} {s : S ⟶ Sp B} {s' : S ⟶ Sp B'} {s'' : S₂ ⟶ Sp B''}
  {u : Obj D l b s} {ob : Obj D l b' s'} {ob₂ : Obj D l b'' s''} {q : S₂ ⟶ S}

theorem exists_congr {q' : S₂ ⟶ S} (e : q = q') (m : ObjMap ob₂ ob q) :
    ∃ m' : ObjMap ob₂ ob q', m'.toSABMap.φ = m.toSABMap.φ := by
  subst e
  exact ⟨m, rfl⟩

theorem comp_eq_of_comp_eq (hL : Out.Laws) (m : ObjMap ob₂ ob q) (n : ObjMap ob₂ u q) {Z : Scheme.{0}}
    (g₁ g₂ : Z ⟶ ob₂.t.G.left) (h : g₁ ≫ m.toSABMap.φ = g₂ ≫ m.toSABMap.φ) :
    g₁ ≫ n.toSABMap.φ = g₂ ≫ n.toSABMap.φ := by
  have hp : (g₁ ≫ ob₂.t.G.hom) ≫ q = (g₂ ≫ ob₂.t.G.hom) ≫ q := by
    rw [Category.assoc, Category.assoc, ← m.cart.1.w, ← Category.assoc, h, Category.assoc]
  obtain ⟨o, ⟨m₁⟩⟩ := obj_pull E H D l B'' B'' b'' b'' (RingHom.id _) S₂ Z s'' ((g₁ ≫ ob₂.t.G.hom) ≫ s'')
    (g₁ ≫ ob₂.t.G.hom) rfl rfl ((Category.comp_id _).symm.trans (congrArg _ (Spec.map_id _).symm)) ob₂
  obtain ⟨k, hk⟩ := ObjComp.objMap_comp m m₁
  obtain ⟨k', hk'⟩ := exists_congr hp k
  obtain ⟨m₂, hm₂⟩ := ObjComp.objMap_cancel m k'
  obtain ⟨n₁, hn₁⟩ := ObjComp.objMap_comp n m₁
  obtain ⟨n₁', hn₁'⟩ := exists_congr hp n₁
  obtain ⟨n₂, hn₂⟩ := ObjComp.objMap_comp n m₂
  have e := obj_rigid_of_pol hL obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ _ _ _ _ _ _ u o _
    n₁'.toSABMap n₂.toSABMap fun a => ⟨_, n₁'.eta a, n₂.eta a⟩
  rw [hn₁', hn₁, hn₂] at e
  rw [hk', hk] at hm₂
  let σ := m₁.cart.1.lift g₁ (𝟙 Z) (Category.id_comp _).symm
  have h₁ : σ ≫ m₁.toSABMap.φ = g₁ := m₁.cart.1.lift_fst _ _ _
  have h₀ : σ ≫ o.t.G.hom = 𝟙 Z := m₁.cart.1.lift_snd _ _ _
  have h₂ : σ ≫ m₂.toSABMap.φ = g₂ := by
    apply m.cart.1.hom_ext
    · rw [Category.assoc]
      refine (congrArg (σ ≫ ·) hm₂.symm).trans ?_
      rw [← Category.assoc, h₁, h]
    · rw [Category.assoc, m₂.cart.1.w, ← Category.assoc, h₀, Category.id_comp]
  refine (congrArg (· ≫ n.toSABMap.φ) h₁).symm.trans (Eq.trans ?_ (congrArg (· ≫ n.toSABMap.φ) h₂))
  exact (Category.assoc _ _ _).trans ((congrArg (σ ≫ ·) e).trans (Category.assoc _ _ _).symm)

variable [Flat q] [Surjective q] [QuasiCompact q]

theorem effectiveEpi (m : ObjMap ob₂ ob q) : EffectiveEpi m.toSABMap.φ := by
  have : Flat m.toSABMap.φ := MorphismProperty.of_isPullback m.cart.1.flip inferInstance
  have : Surjective m.toSABMap.φ := MorphismProperty.of_isPullback m.cart.1.flip inferInstance
  have : QuasiCompact m.toSABMap.φ := MorphismProperty.of_isPullback m.cart.1.flip inferInstance
  infer_instance

theorem exists_fac (hL : Out.Laws) (m : ObjMap ob₂ ob q) (n : ObjMap ob₂ u q) :
    ∃ φ : ob.t.G.left ⟶ u.t.G.left, m.toSABMap.φ ≫ φ = n.toSABMap.φ :=
  have := effectiveEpi m
  ⟨EffectiveEpi.desc m.toSABMap.φ n.toSABMap.φ (comp_eq_of_comp_eq hL m n), EffectiveEpi.fac _ _ _⟩

theorem nonempty_objMap_id (hL : Out.Laws) (m : ObjMap ob₂ ob q) (n : ObjMap ob₂ u q) :
    Nonempty (ObjMap ob u (𝟙 S)) := by
  obtain ⟨φ, hφ⟩ := exists_fac hL m n
  obtain ⟨ψ, hψ⟩ := exists_fac hL n m
  have := effectiveEpi m
  have := effectiveEpi n
  have : Epi q := Flat.epi_of_flat_of_surjective _
  have : IsIso φ := ⟨ψ, by rw [← cancel_epi m.toSABMap.φ, ← Category.assoc, hφ, hψ, Category.comp_id],
    by rw [← cancel_epi n.toSABMap.φ, ← Category.assoc, hψ, hφ, Category.comp_id]⟩
  have w : φ ≫ u.t.G.hom = ob.t.G.hom ≫ 𝟙 S := by
    rw [← cancel_epi m.toSABMap.φ, ← Category.assoc, hφ, Category.comp_id, m.cart.1.w, n.cart.1.w]
  have gp : IsGrpPullback ob.t.G u.t.G (𝟙 S) φ := isGrpPullback_id m.cart n.cart φ hφ w
  have hact : ∀ a, (ob.t.act.act a).left ≫ φ = φ ≫ (u.t.act.act a).left := fun a => by
    rw [← cancel_epi m.toSABMap.φ, ← Category.assoc, ← m.act, Category.assoc, hφ, n.act, ← Category.assoc, hφ]
  have hiso : LBIso ob.t.PP.L (u.t.PP.L.pull φ) := by
    have h₁ := ob.t.PP.isLB
    have h₂ := pull_isLB u.t.PP.isLB φ
    have hN := LB.isLB_div h₂ h₁
    have cN : CechPic.cls _ hN = CechPic.pull φ (CechPic.cls _ u.t.PP.isLB) - CechPic.cls _ h₁ :=
      CechPic.cls_div h₂ h₁ hN
    have cl : ∀ {t : SAB H S} (k : SABMap ob₂.t t q),
        CechPic.cls _ ob₂.t.PP.isLB = CechPic.pull k.φ (CechPic.cls _ t.PP.isLB) := fun {t} k => by
      obtain ⟨w, hw, -⟩ := k.lin
      exact (CechPic.cls_eq_iff _ (pull_isLB t.PP.isLB _)).2 ⟨w, hw⟩
    have z : ∀ t : SAB H S, CechPic.pull (eSec t.G) (CechPic.cls _ t.PP.isLB) = 0 := fun t =>
      (CechPic.cls_eq_zero_iff (pull_isLB t.PP.isLB _)).2 ⟨_, t.PP.rigGen⟩
    refine GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange hL.globalFns S S₂ q ob.t.G _ (ObjDim.isAbelianScheme ob) hN inferInstance inferInstance
      inferInstance ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
      ((CechPic.cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
    · have he : eSec ob.t.G ≫ φ = 𝟙 S ≫ eSec u.t.G := (cubeMapOf gp).e_comm
      rw [CechPic.cls_pull hN, cN, map_sub, ← CechPic.pull_comp, z, he, Category.id_comp, z, sub_zero]
    · rw [CechPic.cls_pull hN, cN, ← m.cart.1.isoPullback_inv_fst, CechPic.pull_comp, map_sub, ← CechPic.pull_comp,
        hφ, ← cl, ← cl, sub_self, map_zero]
  obtain ⟨k, hk⟩ := exists_sabMap_of_isProper_of_lbIso hL.globalFns E H S S u.t ob.t (𝟙 S) φ u.proper gp hiso hact
  have key : ∀ (σ₂ : S₂ ⟶ ob₂.t.G.left) (σ : S ⟶ ob.t.G.left) (τ : S ⟶ u.t.G.left),
      σ₂ ≫ m.toSABMap.φ = q ≫ σ → σ₂ ≫ n.toSABMap.φ = q ≫ τ → σ ≫ k.φ = 𝟙 S ≫ τ := fun σ₂ σ τ h₁ h₂ => by
    rw [← cancel_epi q, hk, Category.id_comp, ← Category.assoc, ← h₁, ← h₂, Category.assoc, hφ]
  exact ⟨⟨k, fun a => key _ _ _ (m.eta a) (n.eta a), fun a => key _ _ _ (m.etaA a) (n.etaA a)⟩⟩

end GlobalTheory.ObjDescent

namespace GlobalTheory

theorem nonempty_objMap_of_finite_etale_cover : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b' : Base l B') (b'' : Base l B'') (X S S₂ : Scheme.{0}) (s : X ⟶ Sp B) (s' : S ⟶ Sp B') (s'' : S₂ ⟶ Sp B'') (u : Obj D l b s) (ob : Obj D l b' s') (ob₂ : Obj D l b'' s'') (q : S₂ ⟶ S) (f : S ⟶ X), (IsReduced S ∨ IsLocallyNoetherian S) → IsFinite q → Etale q → Surjective q → Nonempty (ObjMap ob₂ ob q) → Nonempty (ObjMap ob₂ u (q ≫ f)) → Nonempty (ObjMap ob u f) := by
  intro hL _ E _ _ _ H D l B B' B'' _ _ _ b b' b'' X S S₂ s s' s'' u ob ob₂ q f _ _ _ _ ⟨m⟩ ⟨n⟩
  obtain ⟨u', ⟨p⟩⟩ := obj_pull E H D l B B b b (RingHom.id _) X S s (f ≫ s) f rfl rfl
    ((Category.comp_id _).symm.trans (congrArg _ (Spec.map_id _).symm)) u
  obtain ⟨n', -⟩ := ObjComp.objMap_cancel p n
  obtain ⟨k⟩ := ObjDescent.nonempty_objMap_id hL m n'
  obtain ⟨k', -⟩ := ObjComp.objMap_comp p k
  obtain ⟨k'', -⟩ := ObjDescent.exists_congr (Category.id_comp f) k'
  exact ⟨k''⟩

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_objMap_of_finite_etale_surjective_cover : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (b : Base l B) (b' : Base l B') (b'' : Base l B'') (X S S₂ : Scheme.{0}) (s : X ⟶ Sp B) (s' : S ⟶ Sp B') (s'' : S₂ ⟶ Sp B'') (u : Obj D l b s) (ob : Obj D l b' s') (ob₂ : Obj D l b'' s'') (q : S₂ ⟶ S) (f : S ⟶ X), (IsReduced S ∨ IsLocallyNoetherian S) → IsFinite q → Etale q → Surjective q → Nonempty (ObjMap ob₂ ob q) → Nonempty (ObjMap ob₂ u (q ≫ f)) → Nonempty (ObjMap ob u f) := by
  first | exact @GlobalTheory.nonempty_objMap_of_finite_etale_cover | exact GlobalTheory.nonempty_objMap_of_finite_etale_cover | (intros; apply GlobalTheory.nonempty_objMap_of_finite_etale_cover <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.LevelCover

noncomputable section

namespace GlobalTheory.LevelQuotRep

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem isSeparated_of_qproj {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsQProjOver f) :
    IsSeparated f := by
  obtain ⟨N, i, hi, -, rfl⟩ := h
  unfold PSpace.str
  infer_instance

theorem exists_lift_geom {W Z : Scheme.{0}} (q : W ⟶ Z) [LocallyOfFiniteType q] [Surjective q] {K : Type} [Field K]
    [IsAlgClosed K] (x : Sp K ⟶ Z) : ∃ h : Sp K ⟶ W, h ≫ q = x := by
  obtain ⟨y, -⟩ := (pullback.snd q x).surjective (IsLocalRing.closedPoint K)
  have : JacobsonSpace ↥(pullback q x) := LocallyOfFiniteType.jacobsonSpace (pullback.snd q x)
  obtain ⟨y', -, hy'⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback q x)))
    ⟨y, trivial⟩ isOpen_univ.isLocallyClosed
  have hc : IsClosed {y'} := hy'
  refine ⟨pointOfClosedPoint (pullback.snd q x) y' hc ≫ pullback.fst q x, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

theorem finite_etale_onto_spMap {K L : Type} [Field K] [Field L] [CharZero K] [CharZero L] [FiniteDimensional ℚ L]
    (k : K →+* L) : IsFinite (spMap k) ∧ Etale (spMap k) ∧ Surjective (spMap k) := by
  algebraize [k]
  have : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun x => by simp
  have hf : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  refine ⟨?_, ?_, ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩⟩
  · rw [IsFinite.SpecMap_iff]
    exact hf
  · rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
    have : Algebra.FinitePresentation K L := Algebra.FinitePresentation.of_finiteType.mp inferInstance
    exact (⟨inferInstance, inferInstance⟩ : Algebra.Etale K L)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l₂ : Level H}

theorem finiteDimensional_KA (l : Level H) : FiniteDimensional ℚ (KA l) := by
  refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
  rcases hx with rfl | rfl
  · refine IsIntegral.of_pow two_pos ?_
    rw [H.sqrt_neg_disc_sq]
    exact (isIntegral_algebraMap (x := (H.d : ℚ))).neg
  · refine IsIntegral.of_pow l.A_pos ?_
    rw [show zeta l.A ^ l.A = 1 from (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]
    exact isIntegral_one

section Obj

variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {b : Base l B} {b' : Base l B'} {b'' : Base l B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}
  {o : Obj D l b s} {o' : Obj D l b' s'} {o'' : Obj D l b'' s''}

theorem obj_comp {f : S' ⟶ S} {f' : S'' ⟶ S'} (m' : ObjMap o'' o' f') (m : ObjMap o' o f) :
    Nonempty (ObjMap o'' o (f' ≫ f)) :=
  ⟨(((ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o' o'').2 f f' m).1 m').choose⟩

theorem obj_cancel {f : S' ⟶ S} {e : S'' ⟶ S} (m : ObjMap o' o f) (n : ObjMap o'' o e) (g : S'' ⟶ S')
    (he : g ≫ f = e) : Nonempty (ObjMap o'' o' g) := by
  subst he
  exact ⟨(((ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o' o'').2 f g m).2 n).choose⟩

theorem obj_pull_same (o : Obj D l b s) (f : S' ⟶ S) : ∃ o' : Obj D l b (f ≫ s), Nonempty (ObjMap o' o f) :=
  obj_pull E H D l _ _ b b (RingHom.id _) _ _ s _ f rfl rfl (by rw [spMap_id', Category.comp_id]) o

end Obj

variable {Xo₂ : Moduli D l₂} (Q : LevelQuot l Xo₂)

theorem exists_lowers {B : Type} [CommRing B] {b : Base l B} {T : Scheme.{0}} {t : T ⟶ Sp B} {o : Obj D l b t}
    {z : T ⟶ Q.X} (n : ObjMap o Q.univ z) (y : T ⟶ Xo₂.X) (hy : y ≫ Q.π = z) :
    ∃ mu : SABMap o.t Xo₂.univ.t y, Lowers l Xo₂.univ o.eta o.etaA y mu.φ := by
  obtain ⟨mu, hmu⟩ := sab_cancel Q.m n.toSABMap y hy
  refine ⟨mu, fun a => sec_cancel mu Q.m _ _ ?_, fun a => sec_cancel mu Q.m _ _ ?_⟩
  · rw [hmu, Q.eta, ← Category.assoc, hy]; exact n.eta a
  · rw [hmu, Q.etaA, ← Category.assoc, hy]; exact n.etaA a

theorem hom_unique {B : Type} [CommRing B] {b : Base l B} {T : Scheme.{0}} [IsReduced T] {t : T ⟶ Sp B}
    {o : Obj D l b t} {f f' : T ⟶ Q.X} (h : f ≫ Q.s = f' ≫ Q.s) (m : ObjMap o Q.univ f) (m' : ObjMap o Q.univ f') :
    f = f' := by
  have := isSeparated_of_qproj Q.qproj
  have := Q.fin
  have := Q.onto
  refine (hom_eq_iff_forall_isAlgClosed Q.s h).mpr fun K _ _ x => ?_
  obtain ⟨ox, ⟨n⟩⟩ := obj_pull_same o x
  obtain ⟨u⟩ := obj_comp n m
  obtain ⟨u'⟩ := obj_comp n m'
  obtain ⟨y, hy⟩ := exists_lift_geom Q.π (x ≫ f)
  obtain ⟨y', hy'⟩ := exists_lift_geom Q.π (x ≫ f')
  obtain ⟨mu, hmu⟩ := exists_lowers Q u y hy
  obtain ⟨mu', hmu'⟩ := exists_lowers Q u' y' hy'
  rw [← hy, ← hy']
  refine Q.fibre K y y' ox.t mu mu' ox.eta ox.etaA ?_ hmu hmu'
  rw [← Q.overK, ← Category.assoc, ← Category.assoc, hy, hy', Category.assoc, Category.assoc, h]

def baseUp : Base l (KA l₂) where
  unit := (baseKA l₂).unit
  ρ := Q.jK (baseKA l).ρ
  ρ_sq := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  ζ := Q.jK (baseKA l).ζ
  ζ_prim := (baseKA l).ζ_prim.map_of_injective Q.jK.injective

theorem baseKA_rho_coe (l : Level H) : (((baseKA l).ρ : KA l) : ℂ) = H.rt0 := rfl

theorem baseUp_rho_coe : (((baseUp Q).ρ : KA l₂) : ℂ) = (((baseKA l).ρ : KA l) : ℂ) := Q.jK_val (baseKA l).ρ

theorem baseUp_rho : (baseUp Q).ρ = (baseKA l₂).ρ :=
  Subtype.ext ((baseUp_rho_coe Q).trans ((baseKA_rho_coe l).trans (baseKA_rho_coe l₂).symm))

theorem baseUp_zeta (hd : l.A ∣ l₂.A) : (baseUp Q).ζ = (baseKA l₂).ζ ^ (l₂.A / l.A) := Subtype.ext (by
  rw [IntermediateField.coe_pow]
  exact (Q.jK_val _).trans (zeta_dvd l₂.A_pos hd))

theorem exists_cover (hL : Out.Laws) (hpq : 1 ≤ D.p + D.q) (hd : l.Dvd l₂) {S : Scheme.{0}} [IsReduced S]
    {s' : S ⟶ Sp (KA l)} (ob : Obj D l (baseKA l) s') :
    ∃ (S₂ : Scheme.{0}) (q : S₂ ⟶ S) (g : S₂ ⟶ Q.X) (s₂ : S₂ ⟶ Sp (KA l₂)) (o : Obj D l (baseUp Q) s₂),
      IsFinite q ∧ Etale q ∧ Surjective q ∧ g ≫ Q.s = q ≫ s' ∧ Nonempty (ObjMap o ob q) ∧
        Nonempty (ObjMap o Q.univ g) := by
  have := finiteDimensional_KA l₂
  obtain ⟨k1, k2, k3⟩ := finite_etale_onto_spMap Q.jK
  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseUp Q) Q.jK _ _ s' (pullback.snd s' (spMap Q.jK))
    (pullback.fst _ _) rfl rfl pullback.condition ob
  obtain ⟨S₂, p, o₂, m, hf, he, hs, ⟨hm₁, hm₂⟩, -⟩ := GlobalTheory.T.exists_finiteEtale_deeper_level_cover hL E H D l l₂ _ (baseUp Q) (baseKA l₂) _ _ o₁ hpq hd
    (baseUp_rho Q) (baseUp_zeta Q hd.2.2)
  have hr : IsReduced S₂ := isReduced_of_smooth_of_isReduced (p ≫ pullback.fst s' (spMap Q.jK))
  obtain ⟨f₂, ⟨hf₂, ⟨u⟩⟩, -⟩ := Xo₂.rep S₂ _ hr o₂
  let o := ObjLower.lower o₂ hd (baseUp_rho Q) (baseUp_zeta Q hd.2.2)
  let mo : ObjMap o o₁ p := ⟨m, hm₁, hm₂⟩
  obtain ⟨z, hz⟩ := sab_comp u.toSABMap Q.m rfl
  refine ⟨S₂, p ≫ pullback.fst _ _, f₂ ≫ Q.π, _, o, inferInstance, inferInstance, inferInstance, ?_,
    obj_comp mo n₁, ⟨⟨z, fun a => ?_, fun a => ?_⟩⟩⟩
  · rw [Category.assoc, Q.overK, ← Category.assoc, hf₂, Category.assoc, Category.assoc, pullback.condition]
  · show (o₂.eta a ^ (l₂.M / l.M)).left ≫ z.φ = _
    rw [hz, ← Category.assoc, sec_pow u.toSABMap _ _ (u.eta a), Category.assoc, Q.eta, Category.assoc]
  · show (o₂.etaA a ^ (l₂.A / l.A)).left ≫ z.φ = _
    rw [hz, ← Category.assoc, sec_pow u.toSABMap _ _ (u.etaA a), Category.assoc, Q.etaA, Category.assoc]

end GlobalTheory.LevelQuotRep

namespace GlobalTheory

open LevelQuotRep in

theorem levelQuot_represents : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo₂ : Moduli D l₂) (Q : LevelQuot l Xo₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (KA l)), IsReduced S → ∀ ob : Obj D l (baseKA l) s', ∃! f : S ⟶ Q.X, f ≫ Q.s = s' ∧ Nonempty (ObjMap ob Q.univ f) := by
  intro hL hL2 E _ _ _ H D l l₂ Xo₂ Q hpq hd S s' hS ob
  refine existsUnique_of_exists_of_unique ?_
    fun f f' ⟨h, ⟨m⟩⟩ ⟨h', ⟨m'⟩⟩ => hom_unique Q (h.trans h'.symm) m m'
  obtain ⟨S₂, q, g, s₂, o, hf, he, hs, hg, ⟨mq⟩, ⟨mg⟩⟩ := exists_cover Q hL hpq hd ob
  have key : pullback.fst q q ≫ g = pullback.snd q q ≫ g := by
    have : IsReduced (pullback q q) := isReduced_of_smooth_of_isReduced (pullback.fst q q ≫ q)
    obtain ⟨oR, ⟨n⟩⟩ := obj_pull_same o (pullback.fst q q)
    obtain ⟨n₁⟩ := obj_comp n mq
    obtain ⟨n'⟩ := obj_cancel mq n₁ (pullback.snd q q) pullback.condition.symm
    obtain ⟨u⟩ := obj_comp n mg
    obtain ⟨u'⟩ := obj_comp n' mg
    exact hom_unique Q (by rw [Category.assoc, Category.assoc, hg, pullback.condition_assoc]) u u'
  have hcoeq : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ S₂), g₁ ≫ q = g₂ ≫ q → g₁ ≫ g = g₂ ≫ g := fun g₁ g₂ h => by
    have := pullback.lift g₁ g₂ h ≫= key
    rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at this
  have hfac : q ≫ EffectiveEpi.desc q g hcoeq = g := EffectiveEpi.fac q g hcoeq
  refine ⟨EffectiveEpi.desc q g hcoeq, ?_, ?_⟩
  · rw [← cancel_epi q, ← Category.assoc, hfac, hg]
  · exact GlobalTheory.T.nonempty_objMap_of_finite_etale_surjective_cover hL hL2 E H D l _ _ _ _ _ _ _ _ _ _ _ _ Q.univ ob o q _ (Or.inl hS) hf he hs ⟨mq⟩
      (hfac.symm ▸ ⟨mg⟩)

end GlobalTheory
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelQuotient_represents_reduced : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo₂ : Moduli D l₂) (Q : LevelQuot l Xo₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (KA l)), IsReduced S → ∀ ob : Obj D l (baseKA l) s', ∃! f : S ⟶ Q.X, f ≫ Q.s = s' ∧ Nonempty (ObjMap ob Q.univ f) := by
  first | exact @GlobalTheory.levelQuot_represents | exact GlobalTheory.levelQuot_represents | (intros; apply GlobalTheory.levelQuot_represents <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.LevelQuotUnram

open GlobalTheory.TangentCrit (dualPt dualBase dualPt_dualBase dualPt_dualBase_assoc)

lemma subsingleton_sp_dual (k : Type) [Field k] : Subsingleton (Sp (DualNumber k)) := by
  refine ⟨fun a b => ?_⟩
  have key : ∀ a : PrimeSpectrum (DualNumber k), a.asIdeal = RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom := by
    intro a
    ext d
    constructor
    · intro hd
      by_contra h
      exact a.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hd
        (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (IsUnit.mk0 _ h)))
    · intro hd
      have h : d.fst = 0 := hd
      refine a.isPrime.mem_of_pow_mem 2 ?_
      have : d ^ 2 = 0 := by ext1 <;> simp [pow_two, h]
      rw [this]; exact a.asIdeal.zero_mem
  exact PrimeSpectrum.ext ((key a).trans (key b).symm)

lemma dualMap_cancel {k K : Type} [Field k] [Field K] (f : k →+* K) {X : Scheme.{0}}
    {g g' : Sp (DualNumber k) ⟶ X} (h : spMap (Chart.dualMapR f) ≫ g = spMap (Chart.dualMapR f) ≫ g') : g = g' := by
  have := subsingleton_sp_dual k
  refine TangentCrit.hom_ext_of_ker_inf (CommRingCat.ofHom (Chart.dualMapR f)) (CommRingCat.ofHom (Chart.dualMapR f))
    (fun z => ⟨IsLocalRing.closedPoint (DualNumber K), Subsingleton.elim _ _⟩) (fun d hd _ => ?_) h h
  have h₁ : f d.fst = 0 := by simpa [Chart.dualMapR] using congrArg TrivSqZeroExt.fst hd
  have h₂ : f d.snd = 0 := by simpa [Chart.dualMapR] using congrArg TrivSqZeroExt.snd hd
  exact TrivSqZeroExt.ext (f.injective (by simpa using h₁)) (f.injective (by simpa using h₂))

lemma constPt_dualMap {k K : Type} [Field k] [Field K] (f : k →+* K) {X : Scheme.{0}} (x : Sp (DualNumber k) ⟶ X) :
    constPt (spMap (Chart.dualMapR f) ≫ x) = spMap (Chart.dualMapR f) ≫ constPt x := by
  simp only [constPt, ← Category.assoc]
  congr 1
  simp only [← Spec.map_comp]
  congr 1
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

lemma exists_dual_lift {X Y : Scheme.{0}} (π : X ⟶ Y) [Smooth π] [IsAffineHom π] {k : Type} [Field k]
    (x : Sp (DualNumber k) ⟶ Y) (y : Sp k ⟶ X) (h : y ≫ π = dualPt k ≫ x) :
    ∃ x₂ : Sp (DualNumber k) ⟶ X, dualPt k ≫ x₂ = y ∧ x₂ ≫ π = x := by
  have := subsingleton_sp_dual k
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (x (IsLocalRing.closedPoint (DualNumber k)))) isOpen_univ
  have hx : Set.range x ⊆ U := by
    rintro _ ⟨z, rfl⟩
    rwa [Subsingleton.elim z (IsLocalRing.closedPoint (DualNumber k))]
  refine exists_lift_of_smooth_of_isAffineOpen π hU (hU.preimage π) le_rfl _ x y h hx ?_ ?_
  · rintro _ ⟨z, rfl⟩
    change π (y z) ∈ U
    rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
    exact hx ⟨_, rfl⟩
  · intro R A _ _ _ _ _ _ ρ hρ φ
    refine SmoothNilLift.exists_lift_of_nil ρ (fun c => ⟨TrivSqZeroExt.inl c, hρ _⟩) (fun d hd => ?_) φ
    have h : TrivSqZeroExt.fst d = 0 := (hρ d).symm.trans hd
    exact ⟨2, by ext1 <;> simp [pow_two, h]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

lemma sab_cast {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f g : S' ⟶ S} (m : SABMap t' t f) (h : f = g) :
    ∃ n : SABMap t' t g, n.φ = m.φ := by
  subst h; exact ⟨m, rfl⟩

lemma torsion_rigid {X : Scheme.{0}} {k : Type} [Field k] (t : SAB H (Sp (DualNumber k))) (t₂ : SAB H X)
    (y : Sp k ⟶ X) (ν : SABMap t t₂ (dualBase k ≫ y)) {n : ℕ} (hn : IsUnit (n : Γ(X, ⊤)))
    (σ : 𝟙_ (Over (Sp (DualNumber k))) ⟶ t.G) (τ : 𝟙_ (Over X) ⟶ t₂.G) (hσ : σ ^ n = 1) (hτ : τ ^ n = 1)
    (h : dualPt k ≫ σ.left ≫ ν.φ = y ≫ τ.left) : σ.left ≫ ν.φ = (dualBase k ≫ y) ≫ τ.left := by
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback ν.cart (𝟙 _) (dualBase k ≫ y) (Category.id_comp _).symm
  have h₁ : (e σ).left = σ.left ≫ ν.φ := he σ
  have h₂ : (toUnit (Over.mk (dualBase k ≫ y)) ≫ τ).left = (dualBase k ≫ y) ≫ τ.left := by simp
  rw [← h₁, ← h₂]
  congr 1
  refine GrpTangent.eq_of_tangentMap_injective y (mulN t₂.G n)
    (GrpTangent.tangentMap_pullback_mulN_bijective t₂.G hn y).1 _ _ (Over.OverMorphism.ext ?_) ?_
  · change dualPt k ≫ Over.Hom.left (e σ) = dualPt k ≫ Over.Hom.left (toUnit (Over.mk (dualBase k ≫ y)) ≫ τ)
    rw [h₁, h₂, h, Category.assoc, dualPt_dualBase_assoc]
  · rw [GrpTangent.comp_mulN, GrpTangent.comp_mulN, ← comp_pow, hτ, comp_one, ← map_pow]
    exact (congrArg e hσ).trans (map_one e)

variable {D : Datum H}

section
variable {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s)

lemma pow_eq_of_add {L Γ : Type} [AddCommGroup L] [Group Γ] (f : L → Γ) (hf : ∀ a c, f (a + c) = f a * f c)
    (n : ℕ) (a : L) : f a ^ n = f (n • a) := by
  induction n with
  | zero =>
    have := hf 0 0
    rw [add_zero] at this
    rw [pow_zero, zero_smul]
    exact (mul_left_cancel (a := f 0) (by rw [← this, _root_.mul_one])).symm
  | succ n ih => rw [pow_succ, ih, add_smul, one_smul, hf]

lemma natCast_mem_Mb (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have h := Ideal.mem_span_singleton_self (l.M : 𝓞 E)
  rw [← l.prod] at h
  exact Ideal.mul_le_left h

lemma nsmul_mem_Mb (l : Level H) (a : D.La) : l.M • a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul (natCast_mem_Mb l) Submodule.mem_top

lemma eta_pow (a : D.La) : o.eta a ^ l.M = 1 := by
  rw [pow_eq_of_add o.eta o.eta_add, o.eta_ker _ (nsmul_mem_Mb l a)]

lemma etaA_pow (a : D.La) : o.etaA a ^ l.A = 1 := by
  rw [pow_eq_of_add o.etaA o.etaA_add, o.etaA_ker]

include b s in
lemma isUnit_nat {n : ℕ} (hn : 0 < n) : IsUnit (n : Γ(S, ⊤)) := by
  simpa using (b.unit n hn).map ((Scheme.ΓSpecIso (.of B)).inv ≫ s.appTop).hom

end

theorem unram_of_isAlgClosed (hL : Out.Laws) {l l₂ : Level H} (Xo₂ : Moduli D l₂) (Q : LevelQuot l Xo₂)
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp (DualNumber k) ⟶ Q.X) (ob : Obj D l (baseKA l) (x ≫ Q.s))
    (m₁ : ObjMap ob Q.univ x) (m₂ : ObjMap ob Q.univ (constPt x)) : x = constPt x := by
  have := Q.fin
  have := Q.etale
  have := Q.onto
  obtain ⟨y, hy⟩ := GeomSurj.exists_lift_of_surjective Q.π (dualPt k ≫ x)
  obtain ⟨x₂, hx₂, hx⟩ := exists_dual_lift Q.π x y hy.symm
  have hc : constPt x₂ = dualBase k ≫ y := by rw [← hx₂]; rfl
  have hcπ : (dualBase k ≫ y) ≫ Q.π = constPt x := by rw [Category.assoc, ← hy]; rfl

  obtain ⟨o₀, ⟨r⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ (x ≫ Q.s)
    (dualPt k ≫ x ≫ Q.s) (dualPt k) rfl rfl (by simp [spMap]) ob
  have hr : r.toSABMap.φ ≫ m₁.toSABMap.φ = r.toSABMap.φ ≫ m₂.toSABMap.φ := by
    obtain ⟨n₁, hn₁⟩ := ObjMaps.exists_sab_comp m₁.toSABMap r.toSABMap
    obtain ⟨n₂, hn₂⟩ := ObjMaps.exists_sab_comp m₂.toSABMap r.toSABMap
    have e : dualPt k ≫ constPt x = dualPt k ≫ x := dualPt_dualBase_assoc k _
    obtain ⟨n₃, hn₃⟩ := sab_cast n₂ e
    rw [← hn₁, ← hn₂, ← hn₃]
    refine obj_rigid_closed hL E H D l _ _ _ _ _ _ _ _ Q.univ o₀ _ (Or.inl inferInstance) n₁ n₃
      fun a => ⟨_, rfl, ?_⟩
    rw [hn₃, hn₂, hn₁, reassoc_of% (r.eta a), reassoc_of% (r.eta a), m₁.eta, m₂.eta, reassoc_of% e]
  have hr' : ∀ {Z : Scheme.{0}} (z : Z ⟶ ob.t.G.left) (w : Z ⟶ Sp k), z ≫ ob.t.G.hom = w ≫ dualPt k →
      z ≫ m₁.toSABMap.φ = z ≫ m₂.toSABMap.φ := by
    intro Z z w hz
    rw [← r.cart.1.lift_fst z w hz, Category.assoc, Category.assoc]
    exact congrArg _ hr

  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H D l₂ _ _ (baseKA l₂) (baseKA l₂) (RingHom.id _) _ _ Xo₂.s
    (x₂ ≫ Xo₂.s) x₂ rfl rfl (by simp [spMap]) Xo₂.univ
  obtain ⟨a₁, ha₁⟩ := ObjMaps.exists_sab_comp Q.m n₁.toSABMap
  obtain ⟨a₂, ha₂⟩ := sab_cast a₁ (hx.trans (Category.id_comp x).symm)
  obtain ⟨u, hu⟩ := ObjMaps.exists_sab_cancel m₁.toSABMap a₂
  obtain ⟨a₃, ha₃⟩ := ObjMaps.exists_sab_comp m₂.toSABMap u
  obtain ⟨a₄, ha₄⟩ := sab_cast a₃ ((Category.id_comp _).trans hcπ.symm)
  obtain ⟨n₂, hn₂⟩ := ObjMaps.exists_sab_cancel Q.m a₄
  have e₁ : n₁.toSABMap.φ ≫ Q.m.φ = u.φ ≫ m₁.toSABMap.φ := by rw [← ha₁, ← ha₂, hu]
  have e₂ : n₂.φ ≫ Q.m.φ = u.φ ≫ m₂.toSABMap.φ := by rw [← hn₂, ha₄, ha₃]
  have key : ∀ σ : 𝟙_ (Over (Sp (DualNumber k))) ⟶ o₁.t.G,
      dualPt k ≫ σ.left ≫ n₂.φ = dualPt k ≫ σ.left ≫ n₁.toSABMap.φ := by
    intro σ
    have hσ : σ.left ≫ o₁.t.G.hom = 𝟙 _ := Over.w σ
    refine Q.m.cart.1.hom_ext ?_ ?_
    · have := hr' (dualPt k ≫ σ.left ≫ u.φ) (𝟙 _) (by
        have w := u.cart.1.w
        simp only [Category.assoc, Category.id_comp, Category.comp_id] at w ⊢
        rw [w, hσ]
        exact Category.comp_id _)
      simp only [Category.assoc] at this ⊢
      rw [e₁, e₂, this]
    · have w₁ := n₁.cart.1.w
      have w₂ := n₂.cart.1.w
      simp only [Category.assoc]
      rw [w₁, w₂, reassoc_of% hσ, reassoc_of% hσ, dualPt_dualBase_assoc, hx₂]
  obtain ⟨n₃, hn₃⟩ := sab_cast n₂ hc.symm
  have h₂ : x₂ = constPt x₂ := by
    refine Xo₂.unram k x₂ o₁ ⟨n₁⟩ ⟨{ toSABMap := n₃, eta := fun a => ?_, etaA := fun a => ?_ }⟩
    · change _ ≫ n₃.φ = _
      rw [hn₃, hc]
      refine torsion_rigid _ _ y n₂ (isUnit_nat (b := baseKA l₂) (s := Xo₂.s) (by have := l₂.three_le; omega))
        _ _ (eta_pow o₁ a) (eta_pow Xo₂.univ a) ?_
      rw [key, n₁.eta, reassoc_of% hx₂]
    · change _ ≫ n₃.φ = _
      rw [hn₃, hc]
      refine torsion_rigid _ _ y n₂ (isUnit_nat (b := baseKA l₂) (s := Xo₂.s) l₂.A_pos)
        _ _ (etaA_pow o₁ a) (etaA_pow Xo₂.univ a) ?_
      rw [key, n₁.etaA, reassoc_of% hx₂]
  rw [← hcπ, ← hc, ← h₂, hx]

end GlobalTheory.LevelQuotUnram

namespace GlobalTheory

theorem levelQuot_unram : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo₂ : Moduli D l₂) (Q : LevelQuot l Xo₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (k : Type) [Field k] (x : Sp (DualNumber k) ⟶ Q.X) (ob : Obj D l (baseKA l) (x ≫ Q.s)), Nonempty (ObjMap ob Q.univ x) → Nonempty (ObjMap ob Q.univ (constPt x)) → x = constPt x := by
  rintro hL - E _ _ _ H D l l₂ Xo₂ Q - - k _ x ob ⟨m₁⟩ ⟨m₂⟩
  let f : k →+* AlgebraicClosure k := algebraMap _ _
  refine LevelQuotUnram.dualMap_cancel f ?_
  rw [← LevelQuotUnram.constPt_dualMap]
  obtain ⟨o', ⟨r⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ (x ≫ Q.s)
    ((spMap (Chart.dualMapR f) ≫ x) ≫ Q.s) (spMap (Chart.dualMapR f)) rfl rfl (by simp [spMap]) ob
  obtain ⟨n₁, -⟩ := ObjComp.objMap_comp m₁ r
  obtain ⟨n₂, -⟩ := ObjComp.objMap_comp m₂ r
  exact LevelQuotUnram.unram_of_isAlgClosed hL Xo₂ Q _ _ o' n₁ (LevelQuotUnram.constPt_dualMap f x ▸ n₂)

end GlobalTheory
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelQuotient_unramified_dualNumberPoints : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo₂ : Moduli D l₂) (Q : LevelQuot l Xo₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (k : Type) [Field k] (x : Sp (DualNumber k) ⟶ Q.X) (ob : Obj D l (baseKA l) (x ≫ Q.s)), Nonempty (ObjMap ob Q.univ x) → Nonempty (ObjMap ob Q.univ (constPt x)) → x = constPt x := by
  atlas_forward_decl GlobalTheory.levelQuot_unram
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory.ZM

theorem moduli_of_deeper_level : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (Moduli D l₂) → Nonempty (Moduli D l) := by
  intro L L2 hT E _ _ _ H D l l₂ hD hl ⟨Xo₂⟩
  obtain ⟨Q⟩ := GlobalTheory.T.nonempty_levelQuot_of_level_dvd L L2 hT E H D l l₂ Xo₂ hD hl
  exact ⟨{ X := Q.X, s := Q.s, qproj := Q.qproj, smooth := Q.smooth, univ := Q.univ,
           rep := GlobalTheory.T.levelQuotient_represents_reduced L L2 E H D l l₂ Xo₂ Q hD hl,
           unram := GlobalTheory.T.levelQuotient_unramified_dualNumberPoints L L2 E H D l l₂ Xo₂ Q hD hl }⟩
end GlobalTheory.ZM
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_cmModuli_of_deeper_level : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (Moduli D l₂) → Nonempty (Moduli D l) := by
  atlas_forward_decl GlobalTheory.ZM.moduli_of_deeper_level
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem exists_prime_level :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H), ∃ n : ℕ, n.Prime ∧ Odd n ∧
      ∀ A₀ : ℕ, 0 < A₀ → ∃ l₀ l₂ : Level H, l₀.M = n ∧ l₀.A = A₀ ∧ l₀.Dvd l₂ ∧ l.Dvd l₂ := by
  intro E _ _ _ H l
  have hM1 : l.M ≠ 1 := by have := l.three_le; omega
  obtain ⟨n, hn, hnM⟩ := Nat.exists_prime_and_dvd hM1
  have hodd : Odd n := Odd.of_dvd_nat l.odd hnM
  have h3 : 3 ≤ n := by
    have h2 := hn.two_le
    rcases hodd with ⟨k, hk⟩
    omega
  refine ⟨n, hn, hodd, fun A₀ hA₀ => ?_⟩
  have hmap : (l.Mb ⊔ Ideal.span {(n : 𝓞 E)}).map (H.bar : 𝓞 E →+* 𝓞 E) =
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ⊔ Ideal.span {(n : 𝓞 E)} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast]
  have hMn : Ideal.span {(l.M : 𝓞 E)} ≤ Ideal.span {(n : 𝓞 E)} :=
    Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast hnM)
  refine ⟨⟨n, h3, hodd, l.Mb ⊔ Ideal.span {(n : 𝓞 E)}, ?_, ?_, ?_, A₀, hA₀⟩,
    ⟨l.M, l.three_le, l.odd, l.Mb, l.fromK, l.prod, l.coprime, Nat.lcm l.A A₀, Nat.lcm_pos l.A_pos hA₀⟩,
    rfl, rfl, ⟨hnM, le_sup_left, Nat.dvd_lcm_right _ _⟩, ⟨dvd_rfl, le_rfl, Nat.dvd_lcm_left _ _⟩⟩
  · apply le_antisymm
    · apply sup_le
      · refine l.fromK.le.trans (Ideal.span_mono ?_)
        intro a ha
        exact ⟨Ideal.mem_sup_left ha.1, ha.2⟩
      · refine Ideal.span_mono ?_
        intro a ha
        rw [Set.mem_singleton_iff] at ha
        subst ha
        exact ⟨Ideal.mem_sup_right (Ideal.mem_span_singleton_self _), natCast_mem _ _⟩
    · exact Ideal.span_le.2 fun a ha => ha.1
  · rw [hmap, Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup, l.prod]
    set N : Ideal (𝓞 E) := Ideal.span {(n : 𝓞 E)}
    apply le_antisymm
    · refine sup_le (sup_le hMn ?_) (sup_le ?_ ?_) <;>
        first | exact Ideal.mul_le_left | exact Ideal.mul_le_right
    · calc N = N * (l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) := by rw [l.coprime, Ideal.mul_top]
        _ = l.Mb * N ⊔ N * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [Ideal.mul_sup, mul_comm N l.Mb]
        _ ≤ _ := sup_le (le_sup_right.trans le_sup_left) (le_sup_left.trans le_sup_right)
  · rw [hmap, eq_top_iff, ← l.coprime]
    exact sup_le_sup le_sup_left le_sup_left

end GlobalTheory.ZM
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.exists_level_with_odd_prime_first_number : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H), ∃ n : ℕ, n.Prime ∧ Odd n ∧ ∀ A₀ : ℕ, 0 < A₀ → ∃ l₀ l₂ : Level H, l₀.M = n ∧ l₀.A = A₀ ∧ l₀.Dvd l₂ ∧ l.Dvd l₂ := by
  atlas_forward_decl GlobalTheory.ZM.exists_prime_level
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.LevelUp

theorem eq_constPt_of_formallyUnramified {k : Type} [Field k] {X Y : Scheme.{0}} (f : X ⟶ Y) [FormallyUnramified f]
    (x : Sp (DualNumber k) ⟶ X) (h : x ≫ f = Geo.Tor.constPt (x ≫ f)) : x = Geo.Tor.constPt x := by
  let π : CommRingCat.of (DualNumber k) ⟶ CommRingCat.of k := CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom
  have hπ : Function.Surjective π := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hn : IsNilpotent (RingHom.ker π.hom) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro a ha c hc
    have ha' : a.fst = 0 := ha
    have hc' : c.fst = 0 := hc
    rw [Ideal.mem_bot]
    ext <;> simp [ha', hc']
  have := IsClosedImmersion.spec_of_surjective π hπ
  refine FormallyUnramified.hom_ext (Spec.map π) (isNilpotent_ker_specMap π hn) f ?_
    (h.trans (by simp only [Geo.Tor.constPt, Category.assoc]))
  have e : Spec.map π ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  rw [Geo.Tor.constPt, ← Category.assoc, e, Category.id_comp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l₂ : Level H}

theorem finiteDimensional_KA (l : Level H) : FiniteDimensional ℚ (KA l) := by
  refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
  rcases hx with rfl | rfl
  · refine IsIntegral.of_pow two_pos ?_
    rw [H.sqrt_neg_disc_sq]
    exact (isIntegral_algebraMap (x := (H.d : ℚ))).neg
  · refine IsIntegral.of_pow l.A_pos ?_
    rw [show zeta l.A ^ l.A = 1 from (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]
    exact isIntegral_one

theorem formallyUnramified_spMap (j : KA l →+* KA l₂) : FormallyUnramified (spMap j) := by
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
  have := finiteDimensional_KA l₂
  have : Algebra.FormallyUnramified ℚ (KA l₂) := Algebra.FormallyUnramified.of_isSeparable ℚ (KA l₂)
  let _ : Algebra (KA l) (KA l₂) := j.toAlgebra
  exact Algebra.FormallyUnramified.of_restrictScalars ℚ (KA l) (KA l₂)

theorem exists_obj_of_eq {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s s' : S ⟶ Sp B} (e : s = s')
    (o : Obj D l b s) : ∃ o' : Obj D l b s', Nonempty (ObjMap o' o (𝟙 S)) := by
  subst e
  exact ⟨o, ⟨ObjComp.objMapId o⟩⟩

theorem nonempty_objMap_of_eq {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'}
    {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {o : Obj D l b s} {o' : Obj D l b' s'} {f g : S' ⟶ S}
    (e : f = g) (m : ObjMap o' o f) : Nonempty (ObjMap o' o g) := by
  subst e
  exact ⟨m⟩

theorem exists_objMap_lower {B : Type} [CommRing B] {b : Base l B} {b₂ : Base l₂ B} {S S₂ T : Scheme.{0}}
    {s : S ⟶ Sp B} {s₂ : S₂ ⟶ Sp B} {t : T ⟶ Sp B} {o : Obj D l b s} {o₂ : Obj D l₂ b₂ s₂} {o' : Obj D l₂ b₂ t}
    (h : l.Dvd l₂) (hρ : b.ρ = b₂.ρ) (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A)) {π : S₂ ⟶ S} (m : SABMap o₂.t o.t π)
    (h₁ : ∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (o.eta a).left)
    (h₂ : ∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)
    {g : T ⟶ S₂} (u : ObjMap o' o₂ g) :
    ∃ n : ObjMap (ObjLower.lower o' h hρ hζ) o (g ≫ π), n.toSABMap.φ = u.toSABMap.φ ≫ m.φ := by
  obtain ⟨n, hn⟩ := ObjMaps.exists_sab_comp m u.toSABMap
  have hn' : n.cm.F = u.cm.F ≫ m.cm.F := hn
  refine ⟨⟨n, fun a => ?_, fun a => ?_⟩, hn⟩
  · change (o'.eta a ^ (l₂.M / l.M)).left ≫ n.cm.F = _
    rw [hn']
    refine ObjComp.sec_comp (h₁ a) ?_
    rw [← ObjLower.map_nsmul_of_add _ o'.eta_add, ← ObjLower.map_nsmul_of_add _ o₂.eta_add]
    exact u.eta _
  · change (o'.etaA a ^ (l₂.A / l.A)).left ≫ n.cm.F = _
    rw [hn']
    refine ObjComp.sec_comp (h₂ a) ?_
    rw [← ObjLower.map_nsmul_of_add _ o'.etaA_add, ← ObjLower.map_nsmul_of_add _ o₂.etaA_add]
    exact u.etaA _

end GlobalTheory.LevelUp

namespace GlobalTheory

open LevelUp

theorem nonempty_moduli_of_dvd : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (Moduli D l) → Nonempty (Moduli D l₂) := by
  intro hL _ E _ _ _ H D l l₂ hpq hd ⟨Xo⟩
  have hA : l.A ∣ l₂.A := hd.2.2
  let j := levelFieldIncl hA
  let b := baseOfFinerLevel hA
  have hρ : b.ρ = (baseKA l₂).ρ := baseOfFinerLevel_rho hA
  have hζ : b.ζ = (baseKA l₂).ζ ^ (l₂.A / l.A) := baseOfFinerLevel_zeta hA
  have jρ : j (baseKA l).ρ = b.ρ := levelFieldIncl_rho hA
  have jζ : j (baseKA l).ζ = b.ζ := levelFieldIncl_zeta hA
  obtain ⟨o₁, ⟨m₀⟩⟩ := obj_pull E H D l _ _ (baseKA l) b j _ _ Xo.s (pullback.snd Xo.s (spMap j))
    (pullback.fst Xo.s (spMap j)) jρ jζ pullback.condition Xo.univ
  obtain ⟨S₂, π, o₂, m, hfin, het, -, ⟨h₁, h₂⟩, huniv⟩ :=
    GlobalTheory.T.exists_finiteEtale_deeper_level_cover hL E H D l l₂ _ b (baseKA l₂) _ _ o₁ hpq hd hρ hζ
  have hsm : SmoothOfRelativeDimension D.dim (pullback.snd Xo.s (spMap j)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth
  refine ⟨{ X := S₂, s := π ≫ pullback.snd Xo.s (spMap j), qproj := ?_, smooth := ?_, univ := o₂,
            rep := ?_, unram := ?_ }⟩
  · exact isQProjOver_comp_of_isFinite_noetherian _ _ _ _ _ hfin
      ((isQProjOver_baseChange_and_finite_restrict _ _ j _ Xo.s).1 Xo.qproj)
  · have : SmoothOfRelativeDimension (0 + D.dim) (π ≫ pullback.snd Xo.s (spMap j)) := inferInstance
    rwa [zero_add] at this
  · intro S t hS o
    obtain ⟨f₀, ⟨hf₀, ⟨n⟩⟩, hu₀⟩ := moduli_rep_of_base ObjMaps.id_comp_cancel E H D l Xo _ b j S t
      (ObjLower.lower o hd hρ hζ) hS jρ jζ
    obtain ⟨f, hf₁, hf₂⟩ : ∃ f : S ⟶ pullback Xo.s (spMap j), f ≫ pullback.fst _ _ = f₀ ∧ f ≫ pullback.snd _ _ = t :=
      ⟨pullback.lift f₀ t hf₀, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    subst hf₁ hf₂
    obtain ⟨m', -⟩ := ObjComp.objMap_cancel m₀ n
    obtain ⟨h, ⟨hh, u, -⟩, hu⟩ := huniv S f o m'.toSABMap ⟨m'.eta, m'.etaA⟩
    refine ⟨h, ⟨by rw [← Category.assoc, hh], ⟨u⟩⟩, ?_⟩
    rintro g ⟨hg, ⟨v⟩⟩
    obtain ⟨w, hw⟩ := exists_objMap_lower hd hρ hζ m h₁ h₂ v
    obtain ⟨w', -⟩ := ObjComp.objMap_comp m₀ w
    have e : g ≫ π = f := by
      refine pullback.hom_ext (hu₀ _ ⟨?_, ⟨w'⟩⟩) (by rw [Category.assoc, hg])
      rw [Category.assoc, pullback.condition, ← hg]
      simp only [Category.assoc]
    subst e
    refine hu g ⟨rfl, v, hw.symm.trans ?_⟩
    exact obj_rigid_closed hL E H D l _ _ b b _ _ _ _ o₁ (ObjLower.lower o hd hρ hζ) (g ≫ π) (Or.inl hS)
      w.toSABMap m'.toSABMap fun a => ⟨_, w.eta a, m'.eta a⟩
  · rintro k _ x o ⟨u⟩ ⟨u'⟩
    have hj := formallyUnramified_spMap j
    have hp : FormallyUnramified (pullback.fst Xo.s (spMap j)) :=
      (HasRingHomProperty.isStableUnderBaseChange (P := @FormallyUnramified.{0})
        RingHom.FormallyUnramified.isStableUnderBaseChange).of_isPullback (IsPullback.of_hasPullback _ _).flip hj
    have hr : FormallyUnramified (π ≫ pullback.fst Xo.s (spMap j)) :=
      MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance hp
    refine eq_constPt_of_formallyUnramified (π ≫ pullback.fst Xo.s (spMap j)) x ?_
    obtain ⟨w, -⟩ := exists_objMap_lower hd hρ hζ m h₁ h₂ u
    obtain ⟨w', -⟩ := exists_objMap_lower hd hρ hζ m h₁ h₂ u'
    have e : (x ≫ π ≫ pullback.snd Xo.s (spMap j)) ≫ spMap j = (x ≫ π ≫ pullback.fst Xo.s (spMap j)) ≫ Xo.s := by
      simp only [Category.assoc, pullback.condition]
    obtain ⟨o', ⟨i⟩⟩ := exists_obj_of_eq e (objRestrictBase j (ObjLower.lower o hd hρ hζ) jρ jζ)
    let i' : ObjMap o' (ObjLower.lower o hd hρ hζ) (𝟙 _) := ⟨i.toSABMap, i.eta, i.etaA⟩
    obtain ⟨n, -⟩ := ObjComp.objMap_comp (ObjComp.objMap_comp m₀ w).choose i'
    obtain ⟨n', -⟩ := ObjComp.objMap_comp (ObjComp.objMap_comp m₀ w').choose i'
    exact Xo.unram k _ o' (nonempty_objMap_of_eq (by simp only [Category.assoc, Category.id_comp]) n)
      (nonempty_objMap_of_eq (by simp only [Geo.Tor.constPt, Category.assoc, Category.id_comp]) n')

end GlobalTheory
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_moduli_of_level_dvd : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (Moduli D l) → Nonempty (Moduli D l₂) := by
  first | exact @GlobalTheory.nonempty_moduli_of_dvd | exact GlobalTheory.nonempty_moduli_of_dvd | (intros; apply GlobalTheory.nonempty_moduli_of_dvd <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem moduli_nonempty_all_levels : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → N1ab := by
  intro h1 h2 h3 h4 E _ _ _ H D l hD
  obtain ⟨n, hn, hodd, hl⟩ := GlobalTheory.T.exists_level_with_odd_prime_first_number E H l
  obtain ⟨j, hj⟩ := GlobalTheory.T.exists_moduli_prime_power_fullLevel h1 h2 h3 h4 E H D n hD hn hodd
  obtain ⟨l₀, l₂, hM, hA, h02, h2'⟩ := hl ((n ^ j) ^ 2) (pow_pos (pow_pos hn.pos j) 2)
  exact GlobalTheory.T.nonempty_cmModuli_of_deeper_level h1 h2 h3 E H D l l₂ hD h2'
    (GlobalTheory.T.nonempty_moduli_of_level_dvd h1 h2 E H D l₀ l₂ hD h02 (hj l₀ hM hA))

end GlobalTheory.ZM
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduliScheme_nonempty_at_every_level : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → N1ab := by
  atlas_forward_decl GlobalTheory.ZM.moduli_nonempty_all_levels
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.Moduli

theorem moduli_scheme_exists : N1ab :=
  GlobalTheory.T.moduliScheme_nonempty_at_every_level GlobalTheory.T.all_six_abelian_scheme_laws_hold.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.1 GlobalTheory.T.theorem_of_cube_polAbelianScheme GlobalTheory.T.theta_uniformisation_complex_abelian_varieties

end GlobalTheory.Moduli
end
