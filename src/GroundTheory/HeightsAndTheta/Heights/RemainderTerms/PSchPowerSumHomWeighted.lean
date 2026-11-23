module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

theorem psum_isHomogeneous_alt (N j : ℕ) : (psum (Fin N) ℚ j).IsHomogeneous j :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i j

theorem SchPowerSumHomWeighted.proof : SchPowerSumHomWeighted.Statement := by
  intro N d S hS

  rw [S.as_sum, map_sum]
  refine IsHomogeneous.sum _ _ _ fun e he => ?_
  have hw : Finsupp.weight (fun i : Fin N => (i : ℕ) + 1) e = d :=
    hS (mem_support_iff.mp he)
  rw [powerSumHom, aeval_monomial, Finsupp.prod, algebraMap_eq]
  have hprod : (∏ i ∈ e.support, psum (Fin N) ℚ ((i : ℕ) + 1) ^ e i).IsHomogeneous
      (∑ i ∈ e.support, ((i : ℕ) + 1) * e i) :=
    IsHomogeneous.prod _ _ _ fun i _ => (psum_isHomogeneous_alt N ((i : ℕ) + 1)).pow (e i)
  have hsum : ∑ i ∈ e.support, ((i : ℕ) + 1) * e i = d := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
  rw [hsum] at hprod
  exact hprod.C_mul _

end GroundTheory.Heights₂.Heights.RestTerms
