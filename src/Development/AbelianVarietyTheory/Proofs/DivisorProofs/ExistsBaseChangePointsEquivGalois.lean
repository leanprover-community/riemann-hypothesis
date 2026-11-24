module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

@[expose] public section

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
