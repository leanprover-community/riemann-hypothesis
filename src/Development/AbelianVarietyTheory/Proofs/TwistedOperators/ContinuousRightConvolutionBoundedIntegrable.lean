module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
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

open MeasureTheory

namespace GlobalTheory

theorem conv_right_continuous {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
    (m : Measure H) (α : H → ℂ) (hα : Integrable α m) (φ : G → ℂ) (hφ : Continuous φ)
    (B : ℝ) (hB : ∀ g, ‖φ g‖ ≤ B) :
    Continuous (fun x => ∫ h, α h * φ (x * (h : G)) ∂m) := by
  refine continuous_of_dominated (bound := fun h => B * ‖α h‖) ?_ ?_ ?_ ?_
  · intro x
    refine hα.aestronglyMeasurable.mul ?_
    exact (hφ.comp (continuous_const.mul continuous_subtype_val)).aestronglyMeasurable
  · intro x
    refine Filter.Eventually.of_forall (fun h => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  · exact hα.norm.const_mul B
  · refine Filter.Eventually.of_forall (fun h => ?_)
    exact continuous_const.mul (hφ.comp (continuous_id.mul continuous_const))

end GlobalTheory
