module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CoordinateRatioValueAtPointStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem transPt_block_base : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z₁ : (Σ k, ι' k) → ℂ) (z₀ : (Σ k, ι k) → ℂ) (kb : NonPluckerBlocks M.blk), z₁ ∈ mcPts (mCoordIdeal y') → SameOrbit (basePart M.blk z₀) (basePart M'.blk z₁ ∘ Cv.v) → ∃ (e : Φ') (s : ι kb.1 → Φ') (t : ℂ), e ≠ 0 ∧ t ≠ 0 ∧ ∀ i, transPt Cv ⟨kb.1, i⟩ = e * s i ∧ IsValueAt y' (s i) z₁ (t * z₀ ⟨kb.1, i⟩) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv z₁ z₀ kb hz hO
  obtain ⟨c₀, hc₀, e₀⟩ := hO
  obtain ⟨c, hc⟩ := hz.1 (Cv.κ kb).1
  obtain ⟨hy, hv⟩ := GlobalTheory.T.coordinate_ratio_value_at_point K' ι' Φ' y' z₁ (Cv.κ kb).1 c hz hc
  have hw : ∀ i : ι kb.1, ∃ m : ι' (Cv.κ kb).1, Cv.v ⟨kb, i⟩ = ⟨Cv.κ kb, m⟩ := fun i => by
    have h1 := Cv.block.2.2.1 ⟨kb, i⟩
    rcases hq : Cv.v ⟨kb, i⟩ with ⟨k, m⟩
    rw [hq] at h1
    obtain rfl : k = Cv.κ kb := h1
    exact ⟨m, rfl⟩
  choose w hw using hw
  refine ⟨y' ⟨(Cv.κ kb).1, c⟩, fun i => y' ⟨(Cv.κ kb).1, w i⟩ / y' ⟨(Cv.κ kb).1, c⟩,
    (c₀ kb * z₁ ⟨(Cv.κ kb).1, c⟩)⁻¹, hy, inv_ne_zero (mul_ne_zero (hc₀ kb) hc), fun i => ⟨?_, ?_⟩⟩
  · rw [mul_div_cancel₀ _ hy]
    have h1 := transPt_base Cv (⟨kb, i⟩ : Σ k, baseIdx ι M.blk k)
    rw [← Cv.x_eq, hw i, ← M'.y_base] at h1
    exact h1
  · have h2 : z₀ ⟨kb.1, i⟩ = c₀ kb * z₁ ⟨(Cv.κ kb).1, w i⟩ := by
      have h3 := congrFun e₀ (⟨kb, i⟩ : Σ k, baseIdx ι M.blk k)
      simp only [Function.comp, hw i] at h3
      exact h3
    have h4 : (c₀ kb * z₁ ⟨(Cv.κ kb).1, c⟩)⁻¹ * z₀ ⟨kb.1, i⟩ =
        (z₁ ⟨(Cv.κ kb).1, c⟩)⁻¹ * z₁ ⟨(Cv.κ kb).1, w i⟩ := by
      rw [h2]
      have := hc₀ kb
      field_simp
    rw [h4]
    exact hv (w i)

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
