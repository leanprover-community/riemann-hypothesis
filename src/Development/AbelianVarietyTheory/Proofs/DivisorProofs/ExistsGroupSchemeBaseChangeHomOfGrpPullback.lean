module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomProdPow

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj

namespace GlobalTheory.GrpBC

theorem exists_baseChange_hom : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G A : Over S) [GrpObj G] [GrpObj A] (G' A' : Over S') [GrpObj G'] [GrpObj A'] (φG : G'.left ⟶ G.left) (φA : A'.left ⟶ A.left) (p : G ⟶ A), IsGrpPullback G' G f φG → IsGrpPullback A' A f φA → IsMonHom p → ∃ p' : G' ⟶ A', IsMonHom p' ∧ p'.left ≫ φA = φG ≫ p.left := by
  intro S S' f G A _ _ G' A' _ _ φG φA p hG hA hp
  have w : (φG ≫ p.left) ≫ A.hom = G'.hom ≫ f := by
    rw [Category.assoc, Over.w p, hG.1.w]
  have hq1 : hA.1.lift (φG ≫ p.left) G'.hom w ≫ φA = φG ≫ p.left := hA.1.lift_fst _ _ _
  have hq2 : hA.1.lift (φG ≫ p.left) G'.hom w ≫ A'.hom = G'.hom := hA.1.lift_snd _ _ _
  let p' : G' ⟶ A' := Over.homMk (hA.1.lift (φG ≫ p.left) G'.hom w) hq2
  have hp' : p'.left ≫ φA = φG ≫ p.left := hq1
  have isMonHom_of_mul_comp (e : G' ⟶ A')
      (mul : ∀ (T : Over S') (x y : T ⟶ G'), (x * y) ≫ e = (x ≫ e) * (y ≫ e)) :
      IsMonHom e := by
    have hone : (1 : 𝟙_ (Over S') ⟶ G') ≫ e = 1 := by
      have h1 := mul (𝟙_ (Over S')) 1 1
      rw [_root_.mul_one] at h1
      exact _root_.left_eq_mul.mp h1
    refine ⟨?_, ?_⟩
    · simpa [Hom.one_def] using hone
    · have h2 := mul (G' ⊗ G') (fst G' G') (snd G' G')
      simpa [Hom.mul_def] using h2
  refine ⟨p', isMonHom_of_mul_comp p' fun T x y => ?_, hp'⟩
  apply Over.OverMorphism.ext
  apply hA.1.hom_ext
  · have e1 := hG.2 T x y (pushPt hG.1.w x) (pushPt hG.1.w y) rfl rfl
    have e2 := hA.2 T (x ≫ p') (y ≫ p') (pushPt hG.1.w x ≫ p) (pushPt hG.1.w y ≫ p)
      (by simp only [Over.comp_left, pushPt, Over.homMk_left, Category.assoc, hp'])
      (by simp only [Over.comp_left, pushPt, Over.homMk_left, Category.assoc, hp'])
    have e3 : (pushPt hG.1.w x ≫ p * pushPt hG.1.w y ≫ p).left = (x * y).left ≫ φG ≫ p.left := by
      rw [← MonObj.mul_comp, Over.comp_left, e1, Category.assoc]
    rw [← e2, e3, Over.comp_left, Category.assoc, hp']
  · rw [Over.w, Over.w]

end GlobalTheory.GrpBC
