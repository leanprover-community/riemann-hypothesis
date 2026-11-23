module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocZeroTranslDiffComp
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

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CechPic GlobalTheory.TripleProd

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowBalanceProbe

section Group

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem eq_one_of_cls {L : LB A.left} (hL : L.IsLB) (hK : KTriv A L) {T : Over S} (p : T ⟶ A) (d : Pic T.left)
    (h : pull ((fst T A ≫ p) * snd T A).left (cls L hL) - pull (snd T A).left (cls L hL) =
      pull (fst T A).left d) : p = 1 := by
  refine KerPow.eq_one_of_locGen hK p ((KerPow.locGen_iff _ _ _).1 ?_)
  refine (locZero_iff (fst T A).left (N := Out.translDiff A L p) (LB.isLB_linComb hL _ _)).2 ?_
  rw [cls_translDiff hL, h]
  exact locZero_base _ _

variable {A' : Over S} [GrpObj A'] [IsCommMonObj A']

end Group

variable {R : Type} [CommRing R] [IsDomain R]

end GlobalTheory.PowBalanceProbe
