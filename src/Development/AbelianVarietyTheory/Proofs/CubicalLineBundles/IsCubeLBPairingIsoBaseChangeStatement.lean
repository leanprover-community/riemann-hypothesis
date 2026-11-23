module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsCubeLBPairingIsoBaseChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.isCubeLBPairingIso_baseChange : ∀ (S S' : Scheme.{0}) (s : S' ⟶ S) (X Y A B : Over S) (X' Y' A' B' : Over S') [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B'] (x : X'.left ⟶ X.left) (y : Y'.left ⟶ Y.left) (a : A'.left ⟶ A.left) (b : B'.left ⟶ B.left),
  x ≫ X.hom = X'.hom ≫ s → y ≫ Y.hom = Y'.hom ≫ s → IsGrpPullback A' A s a → IsGrpPullback B' B s b → ∀ (L : LB A.left) (M : LB B.left) (L' : LB A'.left) (M' : LB B'.left), L.IsLB → M.IsLB → L'.IsLB → M'.IsLB → LBIso (L.pull a) L' → LBIso (M.pull b) M' →
  ∀ (f₁ : X ⟶ A) (f₂ : Y ⟶ A) (g₁ : X ⟶ B) (g₂ : Y ⟶ B) (f₁' : X' ⟶ A') (f₂' : Y' ⟶ A') (g₁' : X' ⟶ B') (g₂' : Y' ⟶ B'),
  f₁'.left ≫ a = x ≫ f₁.left → f₂'.left ≫ a = y ≫ f₂.left → g₁'.left ≫ b = x ≫ g₁.left → g₂'.left ≫ b = y ≫ g₂.left → LamEq L f₁ f₂ M g₁ g₂ → LamEq L' f₁' f₂' M' g₁' g₂' := by
  first | exact @GlobalTheory.CM.lamEq_baseChange | exact GlobalTheory.CM.lamEq_baseChange | (intros; apply GlobalTheory.CM.lamEq_baseChange <;> assumption)
