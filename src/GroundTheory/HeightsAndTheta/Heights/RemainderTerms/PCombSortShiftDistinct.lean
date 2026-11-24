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

open Equiv

theorem CombSortShiftDistinct.proof : CombSortShiftDistinct.Statement := by
  intro m l hl q hq i j hij hqi hqj σ τ heq
  have hr := congrArg Set.range heq
  rw [σ.surjective.range_comp, τ.surjective.range_comp] at hr
  have hmem : l i ∈ Set.range (Function.update l j (l j - q)) :=
    ⟨i, by rw [Function.update_of_ne hij]⟩
  rw [← hr] at hmem
  obtain ⟨k, hk⟩ := hmem
  by_cases hki : k = i
  · subst hki
    rw [Function.update_self] at hk
    omega
  · rw [Function.update_of_ne hki] at hk
    exact hki (hl hk)

end GroundTheory.Heights₂.Heights.RestTerms
