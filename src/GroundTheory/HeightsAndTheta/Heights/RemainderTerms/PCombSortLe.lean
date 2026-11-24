module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Equiv

theorem CombSortLe.proof : CombSortLe.Statement := by
  intro m u l σ hl hul hu k
  obtain ⟨j, hjk, hkj⟩ : ∃ j : Fin m, j ≤ k ∧ k ≤ σ j := by
    by_contra h
    push Not at h
    have hcard : (Iic k).card ≤ (Iio k).card := by
      refine card_le_card_of_injOn σ ?_ σ.injective.injOn
      intro j hj
      simp only [coe_Iic, coe_Iio, Set.mem_Iic, Set.mem_Iio] at hj ⊢
      exact h j hj
    rw [Fin.card_Iic, Fin.card_Iio] at hcard
    omega
  calc u (σ k) ≤ u (σ j) := hu hjk
    _ ≤ l (σ j) := hul _
    _ ≤ l k := hl hkj

end GroundTheory.Heights₂.Heights.RestTerms
