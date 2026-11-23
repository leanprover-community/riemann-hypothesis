module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdealThickeningImmersionOfIsPullbackSquareZero
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
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isIdealThickeningImmersion_of_isPullback_square_zero_quotient : ∀ (R C : Type) [CommRing R] [CommRing C] (σ : R →+* C) (J : Ideal R), J ^ 2 = ⊥ → ∀ (X X₀ : Scheme.{0}) (s : X ⟶ Sp C) (s₀ : X₀ ⟶ Sp (R ⧸ J)) (i : X₀ ⟶ X), IsPullback i s₀ (s ≫ spMap σ) (spMap (Ideal.Quotient.mk J)) → IsThick (J.map σ) s i := by
  first | exact @GlobalTheory.LBLift.isThick_of_isPullback_quotient | exact GlobalTheory.LBLift.isThick_of_isPullback_quotient | (intros; apply GlobalTheory.LBLift.isThick_of_isPullback_quotient <;> assumption)
