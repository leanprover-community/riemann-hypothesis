module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

def placesRing {L : Type*} [Field L] [NumberField L] (S : Set (FinitePlace L)) : Subring L where
  carrier := {x | ∀ w ∈ S, w x ≤ 1}
  zero_mem' := fun w _ ↦ by simp
  one_mem' := fun w _ ↦ by simp
  add_mem' := fun hx hy w hw ↦ (FinitePlace.add_le w _ _).trans (max_le (hx w hw) (hy w hw))
  neg_mem' := fun hx w hw ↦ by simpa [map_neg_eq_map] using hx w hw
  mul_mem' := fun hx hy w hw ↦ by
    rw [map_mul]
    exact mul_le_one₀ (hx w hw) (apply_nonneg w _) (hy w hw)

theorem mem_placesRing {L : Type*} [Field L] [NumberField L] (S : Set (FinitePlace L)) (x : L) :
    x ∈ placesRing S ↔ ∀ w ∈ S, w x ≤ 1 := Iff.rfl

end GroundTheory.Heights₂.Heights
