import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilPullNoncomm

open GlobalTheory.CommPairing

abbrev oneChart (X : Scheme.{0}) : LB X := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩

abbrev manyChart {X : Scheme.{0}} {κ : Type} (v : κ → Γ(X, ⊤)ˣ) : LB X :=
  ⟨κ, fun _ => ⊤, fun i j => res inf_le_left (v i * (v j)⁻¹)⟩

theorem oneChart_isLB (X : Scheme.{0}) : (oneChart X).IsLB where
  cover := top_le_iff.1 fun _ _ => TopologicalSpace.Opens.mem_iSup.2 ⟨PUnit.unit, trivial⟩
  g_self _ := map_one _
  cocycle _ _ _ := by
    show res _ 1 * res _ 1 = res _ 1
    simp only [map_one, _root_.mul_one]




theorem one_isGen {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    (⟨fun _ => 1⟩ : LB.Gen (LB.LinComb (oneChart X) φ ε)).IsGen :=
  isGen_of_gm _ fun y j j' _ _ => (map_one _).trans (Eq.symm ((congrArg₂ (· * ·)
    (Finset.prod_eq_one fun k _ => (congrArg (· ^ ε k) (map_one _)).trans (one_zpow _)) (map_one _)).trans
      (_root_.mul_one _)))

variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

theorem weilIs_oneChart (hu : ∀ u : Γ(G.left, ⊤)ˣ, ∃ a : Γ(S, ⊤)ˣ, u = pullU G.hom ⊤ a) {T : Over S} [IsIso T.hom]
    (k : ℤ) (x y : T ⟶ G) : WeilIs G (oneChart _) k x y 1 := by
  intro p
  refine ⟨⊤, trivial, ⟨⟨_, _, one_isGen _ _⟩, ⟨_, _, one_isGen _ _⟩, rfl, rfl⟩, fun θx θy h₁ h₂ => ?_⟩
  have hi : IsIso (overRes (⊤ : T.left.Opens)).hom := by
    show IsIso ((⊤ : T.left.Opens).ι ≫ T.hom)
    have : IsIso (⊤ : T.left.Opens).ι := inferInstanceAs (IsIso T.left.topIso.hom)
    infer_instance
  have e1 : unitRes (⊤ : T.left.Opens) 1 = 1 := map_one _
  rw [e1]
  clear e1 h₁ h₂
  generalize overRes (⊤ : T.left.Opens) = T' at *
  have hs : IsIso (snd T' G).left := inferInstanceAs (IsIso (pullback.snd T'.hom G.hom))
  have key : ∀ θ : ThetaGrp G (oneChart _) k T', ∃ a : Γ(S, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ G).left) (z : Z) (J),
      tval θ r z J = gm (r ≫ (T' ⊗ G).hom) z ⊤ a := by
    intro θ
    have le : ⊤ ≤ LB.wchart (oneChart G.left) ![(snd T' G).left, (translPt G θ.pt).left] (fun _ => PUnit.unit) :=
      fun _ _ => Set.mem_iInter.2 fun _ => trivial
    obtain ⟨a, ha⟩ := hu (pullU (inv (snd T' G).left) ⊤ (res le (θ.φ.s fun _ => PUnit.unit)))
    refine ⟨a, fun Z r z J => ?_⟩
    have h := congrArg (gm (r ≫ (snd T' G).left) z ⊤) ha
    have h₁ := gm_pull (r ≫ (snd T' G).left) (inv (snd T' G).left) z ⊤ trivial (res le (θ.φ.s fun _ => PUnit.unit))
    have h₂ := gm_pull (r ≫ (snd T' G).left) G.hom z ⊤ trivial a
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at h₁
    rw [Category.assoc, Over.w] at h₂
    exact (gm_res r z le trivial _).symm.trans (h₁.symm.trans (h.trans h₂))
  obtain ⟨a, ha⟩ := key θx
  obtain ⟨b, hb⟩ := key θy
  rw [commIsOf_iff (oneChart_isLB _)]
  intro Z r z J _
  rw [ha, ha, hb, hb, Category.assoc, Category.assoc, Over.w, Over.w, map_one, _root_.mul_one, mul_comm]



@[ext] structure Heis (R : Type) where

  a : R

  b : R

  c : R

instance (R : Type) [CommRing R] : Group (Heis R) where
  mul g h := ⟨g.a + h.a, g.b + h.b, g.c + h.c + g.a * h.b⟩
  one := ⟨0, 0, 0⟩
  inv g := ⟨-g.a, -g.b, g.a * g.b - g.c⟩
  mul_assoc g h k := Heis.ext (add_assoc _ _ _) (add_assoc _ _ _) (by
    show g.c + h.c + g.a * h.b + k.c + (g.a + h.a) * k.b = g.c + (h.c + k.c + h.a * k.b) + g.a * (h.b + k.b)
    ring)
  one_mul g := Heis.ext (zero_add _) (zero_add _) (by show 0 + g.c + 0 * g.b = g.c; ring)
  mul_one g := Heis.ext (add_zero _) (add_zero _) (by show g.c + 0 + g.a * 0 = g.c; ring)
  inv_mul_cancel g := Heis.ext (neg_add_cancel _) (neg_add_cancel _) (by
    show g.a * g.b - g.c + g.c + -g.a * g.b = 0; ring)

def Heis.map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') : Heis R →* Heis R' :=
  MonoidHom.mk' (fun g => ⟨f g.a, f g.b, f g.c⟩) fun g h => Heis.ext (map_add f _ _) (map_add f _ _) (by
    show f (g.c + h.c + g.a * h.b) = f g.c + f h.c + f g.a * f h.b
    rw [map_add, map_add, map_mul])

def heisFunctor (S : Scheme.{0}) : (Over S)ᵒᵖ ⥤ GrpCat.{0} where
  obj T := GrpCat.of (Heis Γ(T.unop.left, ⊤))
  map g := GrpCat.ofHom (Heis.map g.unop.left.appTop.hom)
  map_id T := GrpCat.hom_ext (MonoidHom.ext fun x => by
    have e : ∀ a, (𝟙 T : T ⟶ T).unop.left.appTop.hom a = a := fun a =>
      congrArg (fun q => q.hom a) (Scheme.Hom.id_appTop (X := T.unop.left))
    exact Heis.ext (e _) (e _) (e _))
  map_comp g g' := GrpCat.hom_ext (MonoidHom.ext fun x => rfl)

abbrev heisObj (S : Scheme.{0}) : Over S := Over.mk (𝔸(Fin 3; S) ↘ S)

def heisEquiv {S : Scheme.{0}} (T : Over S) : (T ⟶ heisObj S) ≃ Heis Γ(T.left, ⊤) where
  toFun x := ⟨x.left.appTop (AffineSpace.coord S 0), x.left.appTop (AffineSpace.coord S 1),
    x.left.appTop (AffineSpace.coord S 2)⟩
  invFun g := Over.homMk (AffineSpace.homOfVector T.hom ![g.a, g.b, g.c]) (AffineSpace.homOfVector_over _ _)
  left_inv x := Over.OverMorphism.ext (AffineSpace.hom_ext
    ((AffineSpace.homOfVector_over _ _).trans (Over.w x).symm) fun i => by
      refine (AffineSpace.homOfVector_appTop_coord _ _ i).trans ?_
      fin_cases i <;> rfl)
  right_inv g := Heis.ext (AffineSpace.homOfVector_appTop_coord _ _ _) (AffineSpace.homOfVector_appTop_coord _ _ _)
    (AffineSpace.homOfVector_appTop_coord _ _ _)

def heisRep (S : Scheme.{0}) : (heisFunctor S ⋙ forget _).RepresentableBy (heisObj S) where
  homEquiv {T} := heisEquiv T
  homEquiv_comp _ _ := rfl

instance (S : Scheme.{0}) : GrpObj (heisObj S) := GrpObj.ofRepresentableBy _ _ (heisRep S)




end GlobalTheory.WeilPullNoncomm

namespace GlobalTheory

open WeilPullNoncomm


end GlobalTheory
