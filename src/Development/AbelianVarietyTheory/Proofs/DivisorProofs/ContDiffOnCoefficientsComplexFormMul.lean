module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.CxForm

theorem bas_repr_mul (n : ℕ) (x y : Alt n) (S : Finset (Fin (n + n))) :
    (bas n).repr (x * y) S =
      ∑ T, ∑ U, (bas n).repr x T * (bas n).repr y U * (bas n).repr (bas n T * bas n U) S := by
  conv_lhs => rw [← (bas n).sum_repr x, ← (bas n).sum_repr y]

  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul, Finsupp.coe_finsetSum,
  Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact Finset.sum_comm

theorem contDiff_coeff_mul : ∀ (n m : ℕ) (F G : V m → Alt n),
    (∀ s : Set (V m), (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (F v) S) s) →
      (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (G v) S) s) →
      ∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (F v * G v) S) s) ∧
    (∀ v : V m, (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v) →
      (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) →
      ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x * G x) S) v) := by
  intro n m F G
  refine ⟨fun s hF hG S => ?_, fun v hF hG S => ?_⟩
  · rw [show (fun v => (bas n).repr (F v * G v) S) = _ from funext fun v => bas_repr_mul n (F v) (G v) S]
    exact ContDiffOn.sum fun T _ => ContDiffOn.sum fun U _ => ((hF T).mul (hG U)).mul contDiffOn_const
  · rw [show (fun x => (bas n).repr (F x * G x) S) = _ from funext fun x => bas_repr_mul n (F x) (G x) S]
    exact DifferentiableAt.fun_sum fun T _ => DifferentiableAt.fun_sum fun U _ =>
      ((hF T).fun_mul (hG U)).fun_mul (differentiableAt_const _)

end GlobalTheory.CxForm
