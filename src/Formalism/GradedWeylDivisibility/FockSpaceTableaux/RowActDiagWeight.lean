module

public import Formalism.GradedWeylDivisibility.StatementD
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem row_action_diagonal_weight : RowActDiagWeight := by
  intro R _ k n t μ f hf
  have hX : (rowAct R (n := n) (Matrix.diagonal t)) = aeval fun v : Fin k × Fin n => C (t v.1) * X v := by
    unfold rowAct
    congr 1
    funext v
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  have hwt : ∀ (d : Fin k × Fin n →₀ ℕ) (a : Fin k), Finsupp.weight (rowW k n) d a = ∑ s, d (a, s) := by
    intro d a
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
      Fintype.sum_prod_type]
    simp only [rowW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]

  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : Finsupp.weight (rowW k n) d = μ := hf (mem_support_iff.mp hd)
  have hp : (d.prod fun v e => t v.1 ^ e) = ∏ a, t a ^ μ a := by
    rw [← hw, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [hwt]
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum]
  rw [hX, aeval_monomial, ← hp, smul_eq_C_mul, monomial_eq]
  simp only [mul_pow, Finsupp.prod_mul, map_finsuppProd, map_pow, MvPolynomial.algebraMap_eq]
  ring

end Formalism.GradedWeylDivisibility
