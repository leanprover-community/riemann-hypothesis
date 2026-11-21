import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Published.AbVarRed

variable (K L Ω : Type) [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra L Ω] [Algebra K Ω]
  [IsScalarTower K L Ω]

theorem spMap_algebraMap_tower :
    spMap (algebraMap K Ω) = spMap (algebraMap L Ω) ≫ spMap (algebraMap K L) := by
  rw [IsScalarTower.algebraMap_eq K L Ω]
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

variable {K L Ω} (A : Over (Sp K))

def baseChangePt (x : ptOver L Ω ⟶ (Over.pullback (spMap (algebraMap K L))).obj A) : ptOver K Ω ⟶ A :=
  Over.homMk (x.left ≫ pullback.fst A.hom (spMap (algebraMap K L))) (by
    show (x.left ≫ pullback.fst A.hom (spMap (algebraMap K L))) ≫ A.hom = spMap (algebraMap K Ω)
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have hx : x.left ≫ pullback.snd A.hom (spMap (algebraMap K L)) = spMap (algebraMap L Ω) := Over.w x
    rw [hx, spMap_algebraMap_tower K L Ω])

def baseChangePtInv (y : ptOver K Ω ⟶ A) : ptOver L Ω ⟶ (Over.pullback (spMap (algebraMap K L))).obj A :=
  Over.homMk (pullback.lift y.left (spMap (algebraMap L Ω)) (by
    have hy : y.left ≫ A.hom = spMap (algebraMap K Ω) := Over.w y
    rw [hy, spMap_algebraMap_tower K L Ω])) (pullback.lift_snd _ _ _)

def baseChangePtEquiv [GrpObj A] :
    (ptOver L Ω ⟶ (Over.pullback (spMap (algebraMap K L))).obj A) ≃* (ptOver K Ω ⟶ A) where
  toFun := baseChangePt A
  invFun := baseChangePtInv A
  left_inv x := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans (Over.w x).symm
  right_inv y := Over.OverMorphism.ext (pullback.lift_fst _ _ _)
  map_mul' x y := by
    have h := isGrpPullback_pullback A (spMap (algebraMap K L))
    apply Over.OverMorphism.ext
    refine Eq.symm <| (mul_left_congr (spMap_algebraMap_tower K L Ω) (baseChangePt A x) (baseChangePt A y)
      (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl).trans ?_
    exact (h.2 _ x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl).trans rfl

end GlobalTheory.Published.AbVarRed
end
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TateBaseChange

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise in
open IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in
private lemma baseChangePtEquiv_galPts (K L Ω : Type) [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A] (σ : Ω ≃ₐ[L] Ω)
    (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.ptOver L Ω ⟶ (Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K L))).obj A) :
    _root_.GlobalTheory.Published.AbVarRed.baseChangePtEquiv A (_root_.GlobalTheory.Published.AbVarRed.galPts _ σ x) =
      _root_.GlobalTheory.Published.AbVarRed.galPts A (σ.restrictScalars K) (_root_.GlobalTheory.Published.AbVarRed.baseChangePtEquiv A x) := by
  apply Over.OverMorphism.ext
  show (_root_.GlobalTheory.Published.AbVarRed.galPts _ σ x).left ≫ _ = (_root_.GlobalTheory.Published.AbVarRed.galPts A (σ.restrictScalars K) _).left
  rw [_root_.GlobalTheory.Published.AbVarRed.galPts_left, _root_.GlobalTheory.Published.AbVarRed.galPts_left, Category.assoc]
  rfl

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise in
open IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.TateBaseChange.galTate_baseChange_eq_one_iff : ∀ (K L Ω : Type) [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A] [IsCommMonObj A] [IsCommMonObj ((Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K L))).obj A)] (l : ℕ) [Fact l.Prime] (σ : Ω ≃ₐ[L] Ω), _root_.GlobalTheory.Published.AbVarRed.galTate ((Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K L))).obj A) l σ = 1 ↔ _root_.GlobalTheory.Published.AbVarRed.galTate A l (σ.restrictScalars K) = 1 := by
  intro K L Ω _ _ _ _ _ _ _ A _ _ _ l _ σ
  set e := _root_.GlobalTheory.Published.AbVarRed.baseChangePtEquiv (K := K) (L := L) (Ω := Ω) A
  have he := baseChangePtEquiv_galPts K L Ω A σ
  constructor
  · intro h
    refine LinearMap.ext fun s => _root_.GlobalTheory.HTLat.Tate.ext fun n => ?_
    rw [_root_.GlobalTheory.Published.AbVarRed.lev_galTate, Module.End.one_apply]
    have ht := congrArg (fun ρ : Module.End ℤ_[l] _ =>
      (ρ (_root_.GlobalTheory.HTLat.Tate.map l e.symm.toMonoidHom s)).lev n) h
    simp only [_root_.GlobalTheory.Published.AbVarRed.lev_galTate, Module.End.one_apply,
      _root_.GlobalTheory.HTLat.Tate.lev_map] at ht
    have := congrArg e ht
    rw [he] at this
    simpa [e] using this
  · intro h
    refine LinearMap.ext fun t => _root_.GlobalTheory.HTLat.Tate.ext fun n => ?_
    rw [_root_.GlobalTheory.Published.AbVarRed.lev_galTate, Module.End.one_apply]
    have hs := congrArg (fun ρ : Module.End ℤ_[l] _ =>
      (ρ (_root_.GlobalTheory.HTLat.Tate.map l e.toMonoidHom t)).lev n) h
    simp only [_root_.GlobalTheory.Published.AbVarRed.lev_galTate, Module.End.one_apply,
      _root_.GlobalTheory.HTLat.Tate.lev_map] at hs
    apply e.injective
    rw [he]
    exact hs

end GlobalTheory.TateBaseChange
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisRepresentationTateModule_baseChange_eq_one_iff : ∀ (K L Ω : Type) [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] [IsCommMonObj ((Over.pullback (spMap (algebraMap K L))).obj A)] (l : ℕ) [Fact l.Prime] (σ : Ω ≃ₐ[L] Ω), galTate ((Over.pullback (spMap (algebraMap K L))).obj A) l σ = 1 ↔ galTate A l (σ.restrictScalars K) = 1 := by
  atlas_forward_decl GlobalTheory.TateBaseChange.galTate_baseChange_eq_one_iff
end
