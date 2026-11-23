module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalTrivTranslateOrderTwo
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_even_cubicalTriv_translate_order_two : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (X : Type) [AddCommGroup X]
    (Q : GlobalTheory.UU.TQ G X) (P₁ : GlobalTheory.UU.CP G), Nonempty (Q.Desc P₁) → ∀ a : 𝟙_ (Over S) ⟶ G, a ^ 2 = 1 →
    ∀ P : GlobalTheory.UU.CP G, P.L.L = P₁.L.L.pull ((toUnit G ≫ a) * 𝟙 G).left →
    (∀ (T : Over S) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P₁.L.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val P₁.sym ((toUnit T ≫ a) * x).left z J * (val P₁.sym (toUnit T ≫ a).left z J)⁻¹) →
    (∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → P₁.L.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV P₁.c z J x y ((toUnit T ≫ a) * u) * (cubV P₁.c z J x y (toUnit T ≫ a))⁻¹) →
    ∃ σ : GlobalTheory.UU.CubTriv P.c Q.i, σ.Even := by
  first | exact @GlobalTheory.TranslateEvenTriv.exists_even_cubTriv | exact GlobalTheory.TranslateEvenTriv.exists_even_cubTriv | (intros; apply GlobalTheory.TranslateEvenTriv.exists_even_cubTriv <;> assumption)
