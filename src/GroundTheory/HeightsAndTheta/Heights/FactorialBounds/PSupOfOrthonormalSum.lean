module

public import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Statements
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Finset

theorem SupOfOrthonormalSum.proof : SupOfOrthonormalSum.Statement := by
  intro V _ _ ι _ b p hb c

  have h1 : p (∑ i, c i • b i) ≤ ∑ i, ‖c i‖ := by
    refine (Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_smul_eq_mul]
    calc ‖c i‖ * p (b i) ≤ ‖c i‖ * 1 := mul_le_mul_of_nonneg_left (hb i) (norm_nonneg _)
      _ = ‖c i‖ := mul_one _

  have h2 : (∑ i, ‖c i‖) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖c i‖ ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset ι) (fun _ => (1 : ℝ))
      (fun i => ‖c i‖)
    simpa [Finset.card_univ] using hcs
  have h3 : ∑ i, ‖c i‖ ≤ √(Fintype.card ι : ℝ) * √(∑ i, ‖c i‖ ^ 2) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
    exact Real.le_sqrt_of_sq_le h2
  exact h1.trans h3

end GroundTheory.Heights₂.Heights
