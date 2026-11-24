module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelSecM
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
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RelTorsionBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (R : Subalgebra ℤ Ω), IsNoetherianRing R → ∀ (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k),
    (∀ k, y ⟨k, c0 k⟩ ≠ 0) → ∀ k0 : K, ∃ n₁ : ℕ, ∀ b : K → ℕ, (∀ k, n₁ ≤ b k) →
      ∀ f ∈ relSecM R y (b + Pi.single k0 1),
        (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ D : ℕ, ∃ g ∈ relSecM R y (b + fun _ => D),
          (∏ k, y ⟨k, c k⟩) ^ D * f = y ⟨k0, c0 k0⟩ * g) →
        ∃ g ∈ relSecM R y b, f = y ⟨k0, c0 k0⟩ * g

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
