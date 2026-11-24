module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatCoverAdditiveFamilyEqLambda
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_flatCover_additiveFamily_eq_lambda : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∀ (T : Over (Sp R)) (N : LB (A ⊗ T).left) (hN : Fam A N), ∃ (H : Over (Sp R)) (h : H ⟶ T) (x : H ⟶ A), Flat h.left ∧ Surjective h.left ∧ QuasiCompact h.left ∧ (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (y : Y ⟶ H), evc hN.isLB a (y ≫ h) = GlobalTheory.CechPic.pull (a * (y ≫ x)).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) - GlobalTheory.CechPic.pull (y ≫ x).left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL)) := by
  first | exact @GlobalTheory.DualCover.exists_cover | exact GlobalTheory.DualCover.exists_cover | (intros; apply GlobalTheory.DualCover.exists_cover <;> assumption)
