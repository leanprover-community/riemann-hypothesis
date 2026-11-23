module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
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

noncomputable section

theorem HomogeneousComponentMul.proof : HomogeneousComponentMul.Statement := by
  intro σ R _ p a m d hp
  have hterm : ∀ i, homogeneousComponent d (p * homogeneousComponent i a) =
      if d = m + i then p * homogeneousComponent i a else 0 := fun i =>
    homogeneousComponent_of_mem
      ((mem_homogeneousSubmodule _ _).mpr (hp.mul (homogeneousComponent_isHomogeneous i a)))

  conv_lhs => rw [← sum_homogeneousComponent a, Finset.mul_sum, map_sum]
  simp_rw [hterm]
  split_ifs with hmd
  · have hcongr : ∀ i ∈ range (a.totalDegree + 1),
        (if d = m + i then p * homogeneousComponent i a else 0) =
          if d - m = i then p * homogeneousComponent i a else 0 := by
      intro i _
      congr 1
      exact propext ⟨fun h => by omega, fun h => by omega⟩
    rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq]
    split_ifs with hmem
    · rfl
    · rw [Finset.mem_range, not_lt] at hmem
      rw [homogeneousComponent_eq_zero (d - m) a (by omega), mul_zero]
  · exact Finset.sum_eq_zero fun i _ => if_neg (by omega)

end

end GroundTheory.Heights₂.Heights.RestTerms
