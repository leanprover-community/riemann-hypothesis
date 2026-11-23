module

public import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedPicardClassZeroOfLocallyZeroStatement
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem AddCls.pull_unit_eq_zero {S : Scheme.{0}} {A T Z : Over S} [GrpObj A] {c : Pic (A ⊗ T).left}
    (h : AddCls A c) (t : Z ⟶ T) : CechPic.pull (lift (1 : Z ⟶ A) t).left c = 0 := by
  have h1 := h Z 1 1 t
  rw [_root_.mul_one] at h1
  exact left_eq_add.1 h1

theorem addF_separated : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → (∀ (T : Over S) (y y' : (addF A).obj (op T)), (∀ p : T.left, ∃ (Z : Over S) (z : Z ⟶ T), IsOpenImmersion z.left ∧ p ∈ Set.range z.left ∧ (addF A).map z.op y = (addF A).map z.op y') → y = y') := by
  intro S A _ hA T y y' h
  refine Subtype.ext (sub_eq_zero.1 (GlobalTheory.T.rigidified_picard_class_zero_of_locally_zero S A T hA (y.1 - y'.1) ?_ fun p ↦ ?_))
  · rw [map_sub, y.2.pull_unit_eq_zero, y'.2.pull_unit_eq_zero, sub_zero]
  · obtain ⟨Z, z, hz, hp, e⟩ := h p
    refine ⟨Z, z, hz, hp, ?_⟩
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val e

end GlobalTheory.PicGlue
