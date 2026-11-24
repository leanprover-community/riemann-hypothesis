module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
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

namespace GroundTheory.Heights₂.Heights.NumbersDVR

theorem EventualValueFacts.proof : EventualValueFacts.Statement := by
  intro K f c s
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hex : ∃ c, ∀ᶠ m in Filter.atTop, f m = c := ⟨c, h⟩
    rw [eventualValue, dite_eq_left hex]
    obtain ⟨m, hm1, hm2⟩ := (hex.choose_spec.and h).exists
    exact hm1.symm.trans hm2
  · have ht : Filter.Tendsto (fun m : K → ℤ => m - s) Filter.atTop Filter.atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro b
      refine ⟨b + s, fun a ha => ?_⟩
      simpa using sub_le_sub_right ha s
    exact ht.eventually h

end GroundTheory.Heights₂.Heights.NumbersDVR
