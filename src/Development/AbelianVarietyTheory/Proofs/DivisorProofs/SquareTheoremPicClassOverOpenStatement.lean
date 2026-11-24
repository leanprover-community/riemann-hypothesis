module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTheoremPicClassOverOpen
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
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.square_theorem_pic_class_over_open : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (c : Pic (A.hom ⁻¹ᵁ U).toScheme) (Y : Over S) (l : (Y ⟶ A) → (Y.left ⟶ (A.hom ⁻¹ᵁ U).toScheme)), (∀ y, Y.hom y ∈ U) → (∀ p, l p ≫ (A.hom ⁻¹ᵁ U).ι = p.left) → ∀ x a : Y ⟶ A, GlobalTheory.CechPic.pull (l (x * a)) c + GlobalTheory.CechPic.pull (l (x * a⁻¹)) c = 2 • GlobalTheory.CechPic.pull (l (x)) c + GlobalTheory.CechPic.pull (l (a)) c + GlobalTheory.CechPic.pull (l (a⁻¹)) c - 2 • GlobalTheory.CechPic.pull (l ((1 : Y ⟶ A))) c := by
  first | exact @GlobalTheory.SquareOpen.pull_mul_add_pull_mul_inv_of_opens | exact GlobalTheory.SquareOpen.pull_mul_add_pull_mul_inv_of_opens | (intros; apply GlobalTheory.SquareOpen.pull_mul_add_pull_mul_inv_of_opens <;> assumption)
