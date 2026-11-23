module

public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLevelIffAut
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaCharLevelOneAndHolomorphicParameter
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta


theorem _root_.GlobalTheory.T.thetaChar_level_one_and_holomorphic_parameter : ∀ (g : ℕ) (a b : Fin g → ℂ), charHalf g a b → (∀ p ∈ Key.phDom g, IsLevel (per p) a b 1 (thetaChar (per p) a b)) ∧ (∀ (al : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) (k n : Fin 4 → Fin g → ℤ) (y : Fin 4 → Fin g → ℂ), DifferentiableOn ℂ (fun p => simTheta (per p) a b al m k n y) (Key.phDom g)) ∧ ∀ (k n : Fin g → ℤ) (z : Fin g → ℂ), Differentiable ℂ (fun p : Fin g → Fin g → ℂ => aut (per p) a b k n z) := by
  first | exact @GlobalTheory.SimilTheta.level_one_and_holomorphic | exact GlobalTheory.SimilTheta.level_one_and_holomorphic | (intros; apply GlobalTheory.SimilTheta.level_one_and_holomorphic <;> assumption)
