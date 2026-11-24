module

public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
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

namespace GroundTheory.Heights₂.Heights.Targets

open NumberField

def NumberFieldBoxCount.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (B : AddSubgroup F), B.FG →
    (∀ x : F, ∃ n : ℕ, 0 < n ∧ (n : F) * x ∈ B) →
    ∃ C : ℝ, ∀ L : AddSubgroup F, L.FG → (∀ x : F, ∃ n : ℕ, 0 < n ∧ (n : F) * x ∈ L) →
      ∀ ρ : (F →+* ℂ) → ℝ, (∀ σ, 0 < ρ σ) → (∀ σ, ρ (ComplexEmbedding.conjugate σ) = ρ σ) →
        ∑ σ : F →+* ℂ, Real.log (ρ σ) + Real.log (genIndex L B) - C ≤
          Real.log (Nat.card {x : L // ∀ σ : F →+* ℂ, ‖σ (x : F)‖ ≤ ρ σ})

end GroundTheory.Heights₂.Heights.Targets
