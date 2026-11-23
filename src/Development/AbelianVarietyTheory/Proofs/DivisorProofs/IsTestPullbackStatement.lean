module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTestPullback
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

theorem _root_.GlobalTheory.T.exists_isTest_comp_isPullD_of_isTest : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (T T' : Scheme.{0}) (t : T ⟶ Sp Rg) (h : T' ⟶ T) (A₁ B₁ : Over T) [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left) (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁), IsTest A B L M t A₁ B₁ φA₁ φB₁ Φ₁ → ∃ (A₂ : Over T') (_ : GrpObj A₂) (B₂ : Over T') (_ : GrpObj B₂) (φA₂ : A₂.left ⟶ A.left) (φB₂ : B₂.left ⟶ B.left) (Φ₂ : A₂ ⟶ B₂), IsTest A B L M (h ≫ t) A₂ B₂ φA₂ φB₂ Φ₂ ∧ IsPullD φA₁ φB₁ Φ₁ φA₂ φB₂ Φ₂ h := by
  first | (exact @GlobalTheory.HomFixMat.isTest_pullback) | (exact GlobalTheory.HomFixMat.isTest_pullback) | (intros; apply GlobalTheory.HomFixMat.isTest_pullback  <;> assumption)
