module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarChainRuleHolomorphicPullback
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

theorem _root_.GlobalTheory.T.del_dbar_chainRule_holomorphicPullback : ∀ (m n : ℕ) (τ : V m → V n) (U : Set (V m)) (β : V n → Alt n) (v : V m), IsOpen U → v ∈ U → DifferentiableOn ℂ τ U →
    (∀ S, DifferentiableAt ℝ (fun y => (bas n).repr (β y) S) (τ v)) →
    delAt (fun x => pull (fderiv ℂ τ x) (β (τ x))) v = pull (fderiv ℂ τ v) (delAt β (τ v)) ∧
    dbarAt (fun x => pull (fderiv ℂ τ x) (β (τ x))) v = pull (fderiv ℂ τ v) (dbarAt β (τ v)) := by
  first | exact @GlobalTheory.CxForm.PullChain.delAt_dbarAt_pull_comp | exact GlobalTheory.CxForm.PullChain.delAt_dbarAt_pull_comp | (intros; apply GlobalTheory.CxForm.PullChain.delAt_dbarAt_pull_comp <;> assumption)
