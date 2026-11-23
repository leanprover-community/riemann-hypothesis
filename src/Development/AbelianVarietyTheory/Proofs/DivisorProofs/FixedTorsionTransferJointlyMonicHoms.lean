module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TorsionTransfer

theorem pow_left_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b)
    (x : Over.mk a ⟶ G) (x' : Over.mk b ⟶ G) (hx : x.left = x'.left) (m : ℕ) :
    (x ^ m).left = (x' ^ m).left := by
  subst h
  rw [Over.OverMorphism.ext hx]

private theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) : spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

private theorem fixed_of_jointlyMonic_over {S S' : Scheme.{0}} (f : S' ⟶ S)
    (T : Over S') (b : T.left ⟶ S) (hb : T.hom ≫ f = b)
    (s : T.left ⟶ T.left) (hs : s ≫ T.hom = T.hom)
    (G : Over S) [GrpObj G] (H : Over S') [GrpObj H]
    (r : Fin 8 → (H ⟶ (Over.pullback f).obj G)) (hr : ∀ k, IsMonHom (r k))
    (hmono : ∀ (x y : T ⟶ H), (∀ k, x ≫ r k = y ≫ r k) → x = y)
    (m : ℕ) (hfix : ∀ y : Over.mk b ⟶ G, y ^ m = 1 → s ≫ y.left = y.left)
    (x : T ⟶ H) (hx : x ^ m = 1) : s ≫ x.left = x.left := by
  subst b
  let P := (Over.pullback f).obj G
  let push : (T ⟶ P) →* (Over.mk (T.hom ≫ f) ⟶ G) :=
    pushHom (isGrpPullback_pullback G f) T
  let x' : T ⟶ H := Over.homMk (s ≫ x.left) <|
    (Category.assoc s x.left H.hom).trans ((congrArg (s ≫ ·) (Over.w x)).trans hs)
  have key : ∀ k, x' ≫ r k = x ≫ r k := by
    intro k
    have hk := hr k
    let post : (T ⟶ H) →* (T ⟶ P) :=
      MonoidHom.mk' (fun u => u ≫ r k) fun u v => MonObj.mul_comp u v (r k)
    let z : T ⟶ P := x ≫ r k
    have hzm : z ^ m = 1 :=
      (map_pow post x m).symm.trans ((congrArg (fun u => post u) hx).trans (map_one post))
    let y := push z
    have hym : y ^ m = 1 :=
      (map_pow push z m).symm.trans ((congrArg (fun u => push u) hzm).trans (map_one push))
    apply Over.OverMorphism.ext
    change (s ≫ x.left) ≫ (r k).left = z.left
    refine (Category.assoc s x.left (r k).left).trans ?_
    apply pullback.hom_ext
    · exact (Category.assoc s z.left (pullback.fst G.hom f)).trans (hfix y hym)
    · have hz : z.left ≫ pullback.snd G.hom f = T.hom := Over.w z
      exact (Category.assoc s z.left (pullback.snd G.hom f)).trans
        ((congrArg (s ≫ ·) hz).trans (hs.trans hz.symm))
  exact congrArg (fun u : T ⟶ H => u.left) (hmono x' x key)

theorem fixed_of_jointlyMonic : ∀ (V W : Type) [CommRing V] [IsDomain V] [CommRing W] [IsDomain W] (io : V →+* W) (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra (FractionRing W) F], (∀ v, algebraMap (FractionRing W) F (algebraMap W _ (io v)) = algebraMap (FractionRing V) F (algebraMap V _ v)) → ∀ (G : Over (Sp V)) [GrpObj G] (H : Over (Sp W)) [GrpObj H] (r : Fin 8 → (H ⟶ (Over.pullback (spMap io)).obj G)), (∀ k, IsMonHom (r k)) → (∀ (T : Over (Sp W)) (x y : T ⟶ H), (∀ k, x ≫ r k = y ≫ r k) → x = y) → ∀ σ : F ≃+* F, (∀ w : W, σ (algebraMap (FractionRing W) F (algebraMap W _ w)) = algebraMap (FractionRing W) F (algebraMap W _ w)) → ∀ m : ℕ, (∀ y : TF (R := V) F ⟶ G, y ^ m = 1 → spMap σ.toRingHom ≫ y.left = y.left) → ∀ x : TF (R := W) F ⟶ H, x ^ m = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  intro V W _ _ _ _ io F _ _ _ hF G _ H _ r hr hmono σ hσ m hfix x hx
  let w₁ := algebraMap W (FractionRing W)
  let w₂ := algebraMap (FractionRing W) F
  let v₁ := algebraMap V (FractionRing V)
  let v₂ := algebraMap (FractionRing V) F
  have hT : spMap σ.toRingHom ≫ (TF (R := W) F).hom = (TF (R := W) F).hom := by
    have e : σ.toRingHom.comp (w₂.comp w₁) = w₂.comp w₁ := RingHom.ext hσ
    change spMap σ.toRingHom ≫ spMap w₂ ≫ spMap w₁ = spMap w₂ ≫ spMap w₁
    simp only [spMap_comp, e]
  have hV : (TF (R := W) F).hom ≫ spMap io = (TF (R := V) F).hom := by
    have e : (w₂.comp w₁).comp io = v₂.comp v₁ := RingHom.ext hF
    change (spMap w₂ ≫ spMap w₁) ≫ spMap io = spMap v₂ ≫ spMap v₁
    simp only [spMap_comp, e]
  exact fixed_of_jointlyMonic_over (spMap io) (TF (R := W) F) (TF (R := V) F).hom hV
    (spMap σ.toRingHom) hT G H r hr (hmono _) m hfix x hx

end GlobalTheory.TorsionTransfer
