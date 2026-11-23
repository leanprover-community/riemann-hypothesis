module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsionImports
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitTheta

theorem grpPullback_mul_section {B B' : Scheme.{0}} {G : Over B} {G' : Over B'} [GrpObj G] [GrpObj G']
    {f : B' ⟶ B} {φ : G'.left ⟶ G.left} (H : IsGrpPullback G' G f φ) (x y : baseOver B' ⟶ G')
    (h h' : baseOver B ⟶ G) (hx : x.left ≫ φ = f ≫ h.left) (hy : y.left ≫ φ = f ≫ h'.left) :
    (x * y).left ≫ φ = f ≫ (h * h').left := by
  let U : Over.mk ((baseOver B').hom ≫ f) ⟶ baseOver B := Over.homMk f (by simp)
  have e := H.2 (baseOver B') x y (U ≫ h) (U ≫ h') hx.symm hy.symm
  rw [← MonObj.comp_mul] at e
  exact e.symm

theorem extends_mul (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ)
    [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (a b : S.Gam) (h h' : baseOver (Sp u.V) ⟶ u.G)
    (ha : Extends u a h) (hb : Extends u b h') : Extends u (a + b) (h * h') := by
  obtain ⟨x, x1, x2, x3⟩ := ha
  obtain ⟨y, y1, y2, y3⟩ := hb
  have := u.U.gen_hom
  let X : baseOver (Sp (FractionRing u.V)) ⟶ (Over.pullback (jK u.V)).obj u.G := Over.homMk x x2
  let Y : baseOver (Sp (FractionRing u.V)) ⟶ (Over.pullback (jK u.V)).obj u.G := Over.homMk y y2
  refine ⟨(X * Y).left, ?_, Over.w (X * Y), ?_⟩
  · exact grpPullback_mul_section (isGrpPullback_pullback u.G (jK u.V)) X Y h h' x1 y1
  · rw [ρ.pt_add]
    exact grpPullback_mul_section
      (((isGrpPullback_of_iso u.U.gen).comp u.cart).congr (Category.id_comp _) rfl) X Y _ _ x3 y3

end GlobalTheory.UnitTheta
