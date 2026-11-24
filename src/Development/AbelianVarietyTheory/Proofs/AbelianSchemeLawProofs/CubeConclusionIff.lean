module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (gm gm_res gm_pull unit_ext exists_chart gm_cocycle gm_self)

namespace GlobalTheory.GtCubeCompare

section General

variable {X Y Z : Scheme.{0}}

variable {A B : LB X}

def gw (w : LB.Iso A B) (f : Y ⟶ X) (y : Y) (p : B.ι) (q : A.ι) : (Y.presheaf.stalk y)ˣ :=
  gm f y (B.U p ⊓ A.U q) (w.s (p, q))

theorem gm_linCombIso (w : LB.Iso A B) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (p : K → B.ι) (q : K → A.ι) (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ LB.wchart B φ p ⊓ LB.wchart A φ q) :
    gm r z (LB.wchart B φ p ⊓ LB.wchart A φ q) ((LB.linCombIso w φ ε).s (p, q)) =
      ∏ a, gw w (r ≫ φ a) z (p a) (q a) ^ ε a := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun a _ =>
    (map_zpow _ _ _).trans (congrArg (· ^ ε a) ?_))
  have hm : (φ a) (r z) ∈ B.U (p a) ⊓ A.U (q a) :=
    ⟨LB.wchart_le B φ p a hz.1, LB.wchart_le A φ q a hz.2⟩
  exact (gm_res r z _ hz _).trans (gm_pull r (φ a) z (B.U (p a) ⊓ A.U (q a)) hm _)

def PM (w : LB.Iso A B) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb A φ ε)) (b : LB.Gen (LB.LinComb B φ ε)) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → B.ι) (q : K → A.ι),
    r z ∈ LB.wchart B φ p → r z ∈ LB.wchart A φ q →
    gm r z (LB.wchart B φ p) (b.s p) =
      (∏ k, gw w (r ≫ φ k) z (p k) (q k) ^ ε k) * gm r z (LB.wchart A φ q) (a.s q)

theorem maps_iff_pm (w : LB.Iso A B) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb A φ ε)) (b : LB.Gen (LB.LinComb B φ ε)) :
    LB.Gen.Maps (LB.linCombIso w φ ε) a b ↔ PM w φ ε a b := by
  constructor
  · intro H Z r z p q hp hq
    have hm : r z ∈ LB.wchart B φ p ⊓ LB.wchart A φ q := ⟨hp, hq⟩
    have := congrArg (gm r z (LB.wchart B φ p ⊓ LB.wchart A φ q)) (H (p, q))
    rw [← gm_linCombIso w φ ε p q r z hm]
    exact (gm_res r z _ hm _).symm.trans
      (this.trans ((map_mul _ _ _).trans (congrArg _ (gm_res r z _ hm _))))
  · rintro H ⟨p, q⟩
    apply unit_ext
    intro x hx
    have := H _ (𝟙 Y) x p q hx.1 hx.2
    rw [← gm_linCombIso w φ ε p q (𝟙 Y) x hx] at this
    exact (gm_res _ x _ hx _).trans
      (this.trans ((map_mul _ _ _).trans (congrArg _ (gm_res _ x _ hx _))).symm)

variable {w : LB.Iso A B} {K K' : Type} [Fintype K] [Fintype K']

end General

section Group

variable {S S' : Scheme.{0}}

end Group

end GlobalTheory.GtCubeCompare

end
