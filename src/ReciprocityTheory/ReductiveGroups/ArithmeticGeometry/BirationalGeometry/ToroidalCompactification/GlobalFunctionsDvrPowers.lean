module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegProd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrPowers

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

def pullPowIso {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) :
    ∀ n : ℕ, (Over.pullback f).obj (powObj G n) ≅ powObj ((Over.pullback f).obj G) n
  | 0 => (Functor.Monoidal.εIso (Over.pullback f)).symm
  | n + 1 => (Functor.Monoidal.μIso (Over.pullback f) G (powObj G n)).symm ≪≫
      whiskerLeftIso ((Over.pullback f).obj G) (pullPowIso f G n)

theorem bijective_of_iso {S' : Scheme.{0}} {A B : Over S'} (e : A ≅ B)
    (h : Function.Bijective B.hom.appTop.hom) : Function.Bijective A.hom.appTop.hom := by
  have hw : A.hom = e.hom.left ≫ B.hom := (Over.w e.hom).symm
  rw [hw, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
  refine Function.Bijective.comp ?_ h
  refine Function.bijective_iff_has_inverse.2 ⟨(e.inv.left.appTop).hom, fun x => ?_, fun x => ?_⟩
  · show (e.hom.left.appTop ≫ e.inv.left.appTop).hom x = x
    rw [← Scheme.Hom.comp_appTop, ← Over.comp_left, e.inv_hom_id]
    simp
  · show (e.inv.left.appTop ≫ e.hom.left.appTop).hom x = x
    rw [← Scheme.Hom.comp_appTop, ← Over.comp_left, e.hom_inv_id]
    simp

theorem pull_powObj_globalFns (hGF : ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt) {S S' : Scheme.{0}} (f : S' ⟶ S)
    (G : Over S) [GrpObj G] (hG : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G)
    [IsProper ((Over.pullback f).obj G).hom] (n : ℕ) :
    Function.Bijective ((Over.pullback f).obj (powObj G n)).hom.appTop.hom := by
  exact bijective_of_iso (pullPowIso f G n)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.globalFns_powObj hGF ((Over.pullback f).obj G)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback (f := f) (G := G) hG) n)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrPowers
