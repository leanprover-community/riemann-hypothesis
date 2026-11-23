module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoinductionAugmentationCompDEqZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC
variable {R : Type} [CommRing R]

def homShEval (J X : Shv R) (M : ModuleCat.{1} (ULift.{1} R)) (f : X ⟶ (homSh J).obj (op M)) (m : M) : X ⟶ J :=
  ⟨{ app := fun U => ModuleCat.ofHom
        { toFun := fun x => (show M ⟶ J.obj.obj U from (f.hom.app U).hom x).hom m
          map_add' := fun x y => by
            rw [map_add (f.hom.app U).hom x y]; rfl
          map_smul' := fun r x => by
            rw [(f.hom.app U).hom.map_smul]; rfl }
     naturality := fun U V g => by
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
        have h := congrArg (fun k => (show M ⟶ J.obj.obj V from k).hom m)
          (congrArg (fun k => (ModuleCat.Hom.hom k) x) (f.hom.naturality g))
        exact h }⟩

def homShCurry (J X : Shv R) (M : ModuleCat.{1} (ULift.{1} R)) (f : X ⟶ (homSh J).obj (op M)) :
    M →ₗ[ULift.{1} R] (X ⟶ J) where
  toFun m := homShEval J X M f m
  map_add' m n := by
    apply Sheaf.hom_ext; ext U x
    exact (show M ⟶ J.obj.obj U from (f.hom.app U).hom x).hom.map_add m n
  map_smul' r m := by
    apply Sheaf.hom_ext; ext U x
    exact (show M ⟶ J.obj.obj U from (f.hom.app U).hom x).hom.map_smul r m

def homShUncurry (J X : Shv R) (M : ModuleCat.{1} (ULift.{1} R)) (l : M →ₗ[ULift.{1} R] (X ⟶ J)) :
    X ⟶ (homSh J).obj (op M) :=
  ⟨{ app := fun U => ModuleCat.ofHom
        { toFun := fun x => (show M ⟶ J.obj.obj U from ModuleCat.ofHom
            { toFun := fun m => ((l m).hom.app U).hom x
              map_add' := fun m n => by rw [map_add l m n]; rfl
              map_smul' := fun r m => by rw [l.map_smul]; rfl })
          map_add' := fun x y => by
            apply ModuleCat.hom_ext; apply LinearMap.ext; intro m
            exact ((l m).hom.app U).hom.map_add x y
          map_smul' := fun r x => by
            apply ModuleCat.hom_ext; apply LinearMap.ext; intro m
            exact ((l m).hom.app U).hom.map_smul r x }
     naturality := fun U V g => by
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
        apply ModuleCat.hom_ext; apply LinearMap.ext; intro m
        exact congrArg (fun k => (ModuleCat.Hom.hom k) x) ((l m).hom.naturality g) }⟩

def homShEquiv (J X : Shv R) (M : ModuleCat.{1} (ULift.{1} R)) :
    (X ⟶ (homSh J).obj (op M)) ≃ (M →ₗ[ULift.{1} R] (X ⟶ J)) where
  toFun := homShCurry J X M
  invFun := homShUncurry J X M
  left_inv f := by
    apply Sheaf.hom_ext; ext U x
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro m
    rfl
  right_inv l := by
    apply LinearMap.ext; intro m
    apply Sheaf.hom_ext; ext U x
    rfl

theorem homShEquiv_natural_left (J X : Shv R) (M N : ModuleCat.{1} (ULift.{1} R)) (p : M ⟶ N)
    (f : X ⟶ (homSh J).obj (op N)) :
    homShEquiv J X M (f ≫ (homSh J).map p.op) = (homShEquiv J X N f) ∘ₗ p.hom := by
  apply LinearMap.ext; intro m
  apply Sheaf.hom_ext; ext U x
  rfl

theorem homShEquiv_natural_right (J X Y : Shv R) (M : ModuleCat.{1} (ULift.{1} R)) (i : X ⟶ Y)
    (f : Y ⟶ (homSh J).obj (op M)) :
    homShEquiv J X M (i ≫ f) = (Linear.leftComp (ULift.{1} R) J i) ∘ₗ (homShEquiv J Y M f) := by
  apply LinearMap.ext; intro m
  apply Sheaf.hom_ext; ext U x
  rfl

theorem homSh_curry : ∀ (R : Type) [CommRing R] (J : Shv R), ∃ e : ∀ (X : Shv R) (M : ModuleCat.{1} (ULift.{1} R)), (X ⟶ (homSh J).obj (op M)) ≃ (M →ₗ[ULift.{1} R] (X ⟶ J)), (∀ (X : Shv R) (M N : ModuleCat.{1} (ULift.{1} R)) (p : M ⟶ N) (f : X ⟶ (homSh J).obj (op N)), e X M (f ≫ (homSh J).map p.op) = (e X N f) ∘ₗ p.hom) ∧ (∀ (X Y : Shv R) (M : ModuleCat.{1} (ULift.{1} R)) (i : X ⟶ Y) (f : Y ⟶ (homSh J).obj (op M)), e X M (i ≫ f) = (Linear.leftComp (ULift.{1} R) J i) ∘ₗ (e Y M f)) :=
  fun _ _ J => ⟨homShEquiv J, homShEquiv_natural_left J, fun X Y M i f => homShEquiv_natural_right J X Y M i f⟩

end GlobalTheory.EtC
