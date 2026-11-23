module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
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
import Mathlib.Tactic.Linter.Style
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

open Topology

namespace GlobalTheory.CompanionTheory.CompactOperators

theorem isCompactOperator_of_scaled_isometric_intertwiner
    {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : H →L[ℂ] H) (B : K →L[ℂ] K) (Φ : H →L[ℂ] K) (c : ℝ) (hc : 0 < c)
    (hΦ : ∀ x, ‖Φ x‖ = c * ‖x‖) (hAB : Φ ∘L A = B ∘L Φ) (hB : IsCompactOperator B) :
    IsCompactOperator A := by
  have hcn : (0 : ℝ) ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hanti : AntilipschitzWith (Real.toNNReal c⁻¹) Φ := by
    refine Φ.antilipschitz_of_bound fun x => ?_
    rw [Real.coe_toNNReal _ hcn, hΦ, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  have hemb : IsClosedEmbedding Φ := hanti.isClosedEmbedding Φ.uniformContinuous
  obtain ⟨S, hS, hSn⟩ := hB
  refine ⟨Φ ⁻¹' S, hemb.isCompact_preimage hS, ?_⟩
  have hpre : A ⁻¹' (Φ ⁻¹' S) = Φ ⁻¹' (B ⁻¹' S) := by
    ext x
    show Φ (A x) ∈ S ↔ B (Φ x) ∈ S
    rw [show Φ (A x) = B (Φ x) from ContinuousLinearMap.ext_iff.mp hAB x]
  rw [hpre]
  exact Φ.continuous.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hSn)

end GlobalTheory.CompanionTheory.CompactOperators
