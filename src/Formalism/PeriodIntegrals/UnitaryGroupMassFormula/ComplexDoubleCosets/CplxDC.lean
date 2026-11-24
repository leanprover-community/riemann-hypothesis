module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable

namespace PI.PoincareSeriesInner.W

universe u

def CplxDC : Prop :=
  ∀ (G : Type u) [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (Γ S S' : Subgroup G) [Countable Γ], S ≤ Γ → S' ≤ Γ →
  ∀ (D D' : Set G), IsRightTransversal Γ S D → IsRightTransversal Γ S' D' →
  ∀ (R : Set G), IsDoubleTransversal Γ S S' R →
  ∀ (Fs : G → Set G), (∀ r ∈ R, IsFundamentalDomain (stab S S' r) (Fs r) μ) →
  ∀ (FΓ : Set G), IsFundamentalDomain Γ FΓ μ →
  ∀ (φ ψ : G → ℂ), Measurable φ → Measurable ψ →
    (∀ s ∈ S, ∀ y : G, φ (s * y) = φ y) → (∀ s ∈ S', ∀ y : G, ψ (s * y) = ψ y) →
    (∀ x : G, ∑' δ : D, ‖φ ((δ : G) * x)‖ₑ ≠ ⊤) →
    (∀ x : G, ∑' δ' : D', ‖ψ ((δ' : G) * x)‖ₑ ≠ ⊤) →
    (∫⁻ x in FΓ, (∑' δ : D, ‖φ ((δ : G) * x)‖ₑ) * (∑' δ' : D', ‖ψ ((δ' : G) * x)‖ₑ) ∂μ) ≠ ⊤ →
    IntegrableOn (fun x => poinc D φ x * poinc D' ψ x) FΓ μ ∧
    (∫ x in FΓ, poinc D φ x * poinc D' ψ x ∂μ)
      = ∑' r : R, ∫ x in Fs r, φ x * ψ ((r : G)⁻¹ * x) ∂μ

end PI.PoincareSeriesInner.W
