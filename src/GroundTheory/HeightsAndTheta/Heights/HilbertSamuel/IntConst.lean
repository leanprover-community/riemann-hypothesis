module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEuclideanSections
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

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory

noncomputable section

def L2GramLattice.Statement : Prop :=
  ∀ (E : Type) [AddCommGroup E] [Module.Free ℤ E] [Module.Finite ℤ E] (X : Type) [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (w : E →+ (X → ℂ)),
    (∀ s, AEStronglyMeasurable (w s) μ) → (∀ s, ∃ C : ℝ, ∀ᵐ z ∂μ, ‖w s z‖ ≤ C) →
    (∀ (r : ℕ) (x : Fin r → E), LinearIndependent ℤ x → ∀ c : Fin r → ℝ,
      (∀ᵐ z ∂μ, ∑ i, (c i : ℂ) * w (x i) z = 0) → c = 0) →
    ∃ φ : E →+ EuclideanSpace ℝ (Fin (Module.finrank ℤ E)),
      Function.Injective φ ∧ DiscreteTopology (imageLattice φ) ∧
      (∀ [DiscreteTopology (imageLattice φ)], IsZLattice ℝ (imageLattice φ)) ∧
      ∀ s, ‖φ s‖ = Real.sqrt (∫ z, ‖w s z‖ ^ 2 ∂μ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
