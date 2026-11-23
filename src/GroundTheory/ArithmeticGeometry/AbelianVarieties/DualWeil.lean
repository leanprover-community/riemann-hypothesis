module

public import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenyPoints
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField

universe u

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] {E E' E'' : WeierstrassCurve F}
  [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]

namespace Isogeny

variable (φ : Isogeny E E')

end Isogeny

section Hom

noncomputable def homPt (Q : isogHom E E') : E.toAffine.Point →+ E'.toAffine.Point :=
  open Classical in if h : Q = 0 then 0 else (isogOfHom Q h).pointHom

theorem map_translate_hom (Q : isogHom E E') (R : E.toAffine.Point) :
    Point.map (translate E R) Q.1 = Q.1 + constMap E' E.toAffine.FunctionField (homPt Q R) := by
  by_cases h : Q = 0
  · subst h
    rw [homPt, dite_eq_left rfl, AddMonoidHom.zero_apply, map_zero, add_zero, ZeroMemClass.coe_zero,
      map_zero]
  · rw [homPt, dite_eq_right h]
    exact (isogOfHom Q h).map_translate R

theorem homPt_eq_of (Q : isogHom E E') {R : E.toAffine.Point} {c : E'.toAffine.Point}
    (h : Point.map (translate E R) Q.1 = Q.1 + constMap E' E.toAffine.FunctionField c) :
    homPt Q R = c := by
  rw [map_translate_hom, add_right_inj] at h
  exact constMap_injective _ _ h

theorem homPt_zero : homPt (0 : isogHom E E') = 0 := by rw [homPt, dif_pos rfl]

theorem homPt_toHom (φ : Isogeny E E') : homPt φ.toHom = φ.pointHom := by
  ext R
  apply homPt_eq_of
  exact φ.map_translate R

end Hom

end GroundTheory.Arith.Abelian
