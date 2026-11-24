module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFormsMulClosed
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option autoImplicit false

noncomputable section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.CxForm.FormMul

theorem leibniz_of_comm : ∀ (n : ℕ) (F G : V n → Alt n) (v : V n) (F' : Alt n),
    (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) →
    (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) →
    ((∀ a, dz a * F v = F' * dz a) → delAt (fun x => F x * G x) v = delAt F v * G v + F' * delAt G v) ∧
    ((∀ a, dzb a * F v = F' * dzb a) → dbarAt (fun x => F x * G x) v = dbarAt F v * G v + F' * dbarAt G v) := by
  intro n F G v F' hF hG
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold delAt
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_mul (T := fun f => del f v (coordVec a))
      (fun f hf => by rw [del_sum (fun p _ => hf p), ContinuousLinearMap.sum_apply])
      (fun f g hf hg => del_mul hf hg _) (fun c => by rw [del_const]; rfl) hF hG]
    simp only [mul_add, ← mul_assoc, h]
  · unfold dbarAt
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_mul (T := fun f => dbar f v (coordVec a))
      (fun f hf => by rw [dbar_sum (fun p _ => hf p), ContinuousLinearMap.sum_apply])
      (fun f g hf hg => dbar_mul hf hg _) (fun c => by rw [dbar_const]; rfl) hF hG]
    simp only [mul_add, ← mul_assoc, h]

end GlobalTheory.CxForm.FormMul
