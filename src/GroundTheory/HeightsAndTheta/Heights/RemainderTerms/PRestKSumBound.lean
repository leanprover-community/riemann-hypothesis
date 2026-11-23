module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsElem
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Elementary
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

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Finset

noncomputable section

theorem RestKSumBound.proof : RestKSumBound.Statement := by
  intro p X N hp hX hXp
  obtain ⟨hsum, htsum, hexp⟩ := ExponentialTail.intersectionNumber_baseChange p X hp hX hXp
  set g : ℕ → ℝ := fun j => 2 * (p ^ (j + 2))⁻¹ * X ^ (j + 1) / ((j + 2).factorial : ℝ) with hg
  have hIcc : Finset.Icc 2 N = Finset.Ico 2 (N + 1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have hre : ∑ k ∈ Finset.Icc 2 N, 2 * (p ^ k)⁻¹ * X ^ (k - 1) / (k.factorial : ℝ) =
      ∑ j ∈ Finset.range (N + 1 - 2), g j := by
    rw [hIcc, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hg]
    simp only
    rw [show 2 + j = j + 2 from Nat.add_comm 2 j, show j + 2 - 1 = j + 1 by omega]
  have hnn : ∀ j, 0 ≤ g j := fun j => by rw [hg]; positivity
  rw [hre]
  calc ∑ j ∈ Finset.range (N + 1 - 2), g j ≤ ∑' j, g j :=
        hsum.sum_le_tsum _ fun j _ => hnn j
    _ ≤ Real.exp (3 / 8) * X / p ^ 2 := htsum
    _ ≤ 1.5 * X / p ^ 2 := hexp

end

end RestTerms

end GroundTheory.Heights₂.Heights
