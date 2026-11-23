module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

open scoped IntermediateField Algebra TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

theorem UpperTheory.Reformulated.B.ExistsCoordinate.exists_coord :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    [inst_2 : NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {y : E},
    y ∈ ℚ[(↑H.rt : E)] →
      ∃ (u : ℚ) (v : ℚ),
        y =
          (↑u : E) +
            (↑v : E) *
              (↑H.rt :
                E) := by
  intro E _ _ _ H y hy
  have hsq : (H.rt : E) * (H.rt : E) = -(H.d : E) := by
    have h := congrArg (fun z : NumberField.RingOfIntegers E => (z : E)) H.rt_sq
    simpa [sq] using h
  induction hy using Algebra.adjoin_induction with
  | mem x hx => exact ⟨0, 1, by rw [Set.mem_singleton_iff.mp hx]; simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨⟨a, b, rfl⟩, c, e, rfl⟩ := And.intro hx hz
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul x z _ _ hx hz =>
    obtain ⟨⟨a, b, rfl⟩, c, e, rfl⟩ := And.intro hx hz
    exact ⟨a * c - b * e * H.d, a * e + b * c, by push_cast; linear_combination (b * e : E) * hsq⟩
