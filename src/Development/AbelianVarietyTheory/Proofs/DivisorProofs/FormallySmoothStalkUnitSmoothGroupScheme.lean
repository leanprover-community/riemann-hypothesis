module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem stalk_formallySmooth_of_smooth : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s)) (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s) (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)), StalkData G s π ε m → π.FormallySmooth := by
  intro S G _ hG s π ε m h
  have hstr := h.str
  clear h
  revert π hstr
  have hs : G.hom.base (unitSec G s) = s := by
    rw [← Scheme.Hom.comp_apply, unitSec, sec_hom]
    rfl
  generalize unitSec G s = p at hs ⊢
  subst hs
  intro π hstr
  have e : Spec.map (CommRingCat.ofHom π) = Spec.map (G.hom.stalkMap p) :=
    (cancel_mono (S.fromSpecStalk (G.hom.base p))).1 (by
      rw [hstr, Scheme.SpecMap_stalkMap_fromSpecStalk])
  have e' : π = (G.hom.stalkMap p).hom := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  rw [e']
  exact Scheme.Hom.mem_smoothLocus.mp (G.hom.smoothLocus_eq_top.ge (Set.mem_univ p))

end GlobalTheory.Nef
