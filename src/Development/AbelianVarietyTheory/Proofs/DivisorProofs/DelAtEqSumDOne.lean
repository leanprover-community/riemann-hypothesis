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

open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexOrder ContDiff ComplexConjugate

noncomputable section

namespace GlobalTheory.CxForm.DelForm

variable {n : ℕ}

def dOne (f : V n → ℂ) (v : V n) : Alt n := ∑ a, del f v (coordVec a) • dz a

theorem delAt_eq_sum_dOne (β : V n → Alt n) (u : V n) :
    delAt β u = ∑ T, dOne (fun x => (bas n).repr (β x) T) u * bas n T := by
  simp only [delAt, coefwise, dOne, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  exact Finset.sum_comm

theorem delAt_congr {F G : V n → Alt n} {v : V n} (h : F =ᶠ[𝓝 v] G) : delAt F v = delAt G v := by
  unfold delAt coefwise
  refine Finset.sum_congr rfl fun a _ => congrArg _ (Finset.sum_congr rfl fun S _ => ?_)
  have e : del (fun x => (bas n).repr (F x) S) v = del (fun x => (bas n).repr (G x) S) v :=
    del_congr (h.fun_comp fun y => (bas n).repr y S)
  simp only [e]

end GlobalTheory.CxForm.DelForm
