module

public import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyTrivialOfIsoPull
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem bijective_app_iso_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) (V : Z.Opens)
    (h : Function.Bijective (g.app V).hom) : Function.Bijective ((f ≫ g).app V).hom := by
  have : IsIso (g.app V) := (ConcreteCategory.isIso_iff_bijective _).2 h
  have : IsIso (f.app (g ⁻¹ᵁ V)) := inferInstance
  have : IsIso ((f ≫ g).app V) := by
    rw [Scheme.Hom.comp_app]; exact IsIso.comp_isIso' ‹_› ‹_›
  exact ConcreteCategory.bijective_of_isIso _

theorem fnBij_snd : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A], IsAbelianScheme A → FnBij (snd A T).left := by
  intro S A T _ hA V
  have e : (snd A T).left = (β_ A T).hom.left ≫ (fst T A).left := by
    rw [← Over.comp_left, braiding_hom_fst]
  have : IsIso (β_ A T).hom.left := inferInstanceAs (IsIso ((Over.forget S).map (β_ A T).hom))
  rw [e]
  exact bijective_app_iso_comp _ _ V
    (GlobalTheory.CubeLawCompare.bijective_app_fst GlobalTheory.SemiRigid.globalFns hA T V)

end GlobalTheory.PicGlue
