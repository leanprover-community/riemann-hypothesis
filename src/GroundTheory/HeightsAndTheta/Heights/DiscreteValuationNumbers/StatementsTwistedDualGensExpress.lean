module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def TwistedDualGensExpress.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (ϖ : R) (Ω : Type) [Field Ω] [Algebra R Ω]
    (K : Type) [Fintype K] (ι : K → Type) (y : (Σ k, ι k) → Ω)
    (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B B' : ChartBundle R (segreVec y) N E),
    SameGenericFibre ϖ B B' →
    ∀ (a a' : K → ℤ) (M M' : ℕ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a φ → IsTwistedDualGens y B' a' φ' →
    ∀ c, segreVec y c ≠ 0 → ∀ m, ∃ (n : ℕ) (r : Fin M → Ω),
      (∀ l, r l ∈ chartRing R (segreVec y) c) ∧
      algebraMap R Ω ϖ ^ n • φ' m = ∑ l, (r l * ∏ k, y ⟨k, c k⟩ ^ (a' k - a k)) • φ l

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
