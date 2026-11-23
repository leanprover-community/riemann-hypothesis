module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubePointsFstEqPartialSumsGrpPullback
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two


theorem _root_.GlobalTheory.T.cubePoints_fst_eq_partialSums_grpPullback : ∀ {S₀ S : Scheme.{0}} (B₀ : Over S₀) [GrpObj B₀] [IsCommMonObj B₀] (B : Over S) [GrpObj B] [IsCommMonObj B] (f : S₀ ⟶ S) (β : B₀.left ⟶ B.left) (β₂ : (G2 B₀).left ⟶ (G2 B).left), IsGrpPullback B₀ B f β → IsSquare β β₂ → ∀ (Y : Over S₀) (x y : Y ⟶ B₀) (x' y' : Y ⟶ (Over.pullback f).obj B), x'.left ≫ pullback.fst B.hom f = x.left ≫ β → y'.left ≫ pullback.fst B.hom f = y.left ≫ β → ∀ k : Fin 4, lamPts x' y' k ≫ pullback.fst B.hom f = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) ((![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) k)).left := by
  first | exact @GlobalTheory.PairPts.lamPts_fst_eq_psum | exact GlobalTheory.PairPts.lamPts_fst_eq_psum | (intros; apply GlobalTheory.PairPts.lamPts_fst_eq_psum <;> assumption)
