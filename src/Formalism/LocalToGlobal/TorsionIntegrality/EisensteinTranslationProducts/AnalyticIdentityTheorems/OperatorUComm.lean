module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaZeroLogDerivative
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

namespace OperatorUThetaLemmas

lemma conj_herm (L : PeriodPair) (x y : ℂ) : conj (herm L x y) = herm L y x := by
  simp only [Formalism.L2.Th1.F.herm, map_div₀, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring

lemma herm_sub_herm (L : PeriodPair) (x y : ℂ) :
    herm L x y - herm L y x = 2 * Complex.I * (altE L x y : ℂ) := by
  rw [← conj_herm L x y, Complex.sub_conj]
  simp only [Formalism.L2.Th1.F.altE]
  push_cast
  ring

lemma herm_add_left (L : PeriodPair) (x y w : ℂ) :
    herm L (x + y) w = herm L x w + herm L y w := by
  simp only [Formalism.L2.Th1.F.herm]
  ring

lemma herm_add_right (L : PeriodPair) (w x y : ℂ) :
    herm L w (x + y) = herm L w x + herm L w y := by
  simp only [Formalism.L2.Th1.F.herm, map_add (f := _)]
  ring

lemma altE_swap (L : PeriodPair) (x y : ℂ) : altE L y x = -altE L x y := by
  simp only [Formalism.L2.Th1.F.altE]
  rw [← conj_herm L x y, Complex.conj_im]

end OperatorUThetaLemmas

open OperatorUThetaLemmas

private theorem mul_exp_mul_exp_eq_exp_mul_of_add_eq (f a b c d : ℂ) (h : a + b = c + d) :
    f * Complex.exp a * Complex.exp b = Complex.exp c * (f * Complex.exp d) := by
  rw [mul_assoc, ← Complex.exp_add, h, Complex.exp_add]
  ring

theorem operator_u_mul : OpUMul := by
  intro L x y F z
  simp only [opU]
  rw [add_assoc z x y]
  apply mul_exp_mul_exp_eq_exp_mul_of_add_eq
  simp only [Formalism.L2.Th1.F.OperatorUThetaLemmas.herm_add_left, Formalism.L2.Th1.F.OperatorUThetaLemmas.herm_add_right]
  linear_combination (-(Real.pi : ℂ) / 2) * Formalism.L2.Th1.F.OperatorUThetaLemmas.herm_sub_herm L x y

theorem operator_u_comm : OpUComm := by
  intro L F z
  refine ⟨by simp [opU, herm], fun x y => ?_⟩
  rw [operator_u_mul L x y F z, operator_u_mul L y x F z, add_comm y x,
    Formalism.L2.Th1.F.OperatorUThetaLemmas.altE_swap L x y, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

end Formalism.L2.Th1.F
