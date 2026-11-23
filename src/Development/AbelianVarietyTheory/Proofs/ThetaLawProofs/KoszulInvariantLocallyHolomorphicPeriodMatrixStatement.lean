module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KoszulInvariantLocallyHolomorphicPeriodMatrix
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.koszulInvariant_locally_holomorphic_periodMatrix : Out.Laws → ThetaUnifAV → ∀ (g : ℕ) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (a b : Fin g → ℂ) (p₀ : (Fin g → Fin g → ℂ)) (x₀ : KeyIn ℂ) (h₀ : x₀.P.g = g) (u₀ : HolUnif x₀.P.A x₀.P.L g) (s₀ : Fin x₀.P.g → RR x₀ n) (κ₀ : ℂˣ), charHalf g a b → admitted g n l l' al → p₀ ∈ Key.phDom g → Wit x₀ h₀ u₀ (per p₀) a b → KaVal x₀ n l l' al s₀ κ₀ → ∃ (W : Set (Fin g → Fin g → ℂ)) (V : (Fin g → Fin g → ℂ) → ℂ), IsOpen W ∧ p₀ ∈ W ∧ W ⊆ Key.phDom g ∧ DifferentiableOn ℂ V W ∧ ∀ p ∈ W, ∀ (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g), Wit x h u (per p) a b → ∃ (s : Fin x.P.g → RR x n) (κ : ℂˣ), KaVal x n l l' al s κ ∧ (κ : ℂ) = V p := by
  first | exact @GlobalTheory.KeyKa.KaHol.kaVal_locally_holomorphic | exact GlobalTheory.KeyKa.KaHol.kaVal_locally_holomorphic | (intros; apply GlobalTheory.KeyKa.KaHol.kaVal_locally_holomorphic <;> assumption)
