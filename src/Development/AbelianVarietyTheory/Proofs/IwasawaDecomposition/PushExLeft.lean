module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ShFam.Hor.LogCh

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) {g : ℕ}
  {ty : Fin g → (E →+* ℂ)} {σ₀ : KA l →+* ℂ} (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n)
  (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X)

def liftEx (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (z : Fin g → ℂ) : Sp ℂ ⟶ Z.oF.t.G.left :=
  Z.m0.toSABMap.cart.1.lift (Fu.ex i P z).left y (by rw [Over.w (Fu.ex i P z), ← hu]; rfl)

def pushEx (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p) (z : Fin g → ℂ) : Over.mk p ⟶ Z.t.G :=
  Over.homMk (liftEx Z Fu y i P hu z ≫ Z.m.φ) (by
    show (liftEx Z Fu y i P hu z ≫ Z.m.φ) ≫ Z.t.G.hom = p
    rw [Category.assoc, Z.m.cart.1.w, ← Category.assoc, liftEx, IsPullback.lift_snd, ← hp])

theorem liftEx_fst (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (z : Fin g → ℂ) : liftEx Z Fu y i P hu z ≫ Z.m0.toSABMap.φ = (Fu.ex i P z).left :=
  IsPullback.lift_fst _ _ _ _

theorem liftEx_snd (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (z : Fin g → ℂ) : liftEx Z Fu y i P hu z ≫ Z.oF.t.G.hom = y :=
  IsPullback.lift_snd _ _ _ _

theorem pushEx_left (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p) (z : Fin g → ℂ) :
    (pushEx Z Fu y i P p hu hp z).left = liftEx Z Fu y i P hu z ≫ Z.m.φ := rfl

end GlobalTheory.ShFam.Hor.LogCh
