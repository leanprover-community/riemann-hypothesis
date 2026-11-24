module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section propG

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem eventually_ne_cocompact (c : ℂ) : ∀ᶠ x in cocompact ℂ, x ≠ c := by
  filter_upwards [(isCompact_singleton : IsCompact ({c} : Set ℂ)).compl_mem_cocompact] with x hx
  simpa using hx

theorem eventually_rate_cocompact (σ : ℂ) (C δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x in cocompact ℂ, C * ‖x + σ‖⁻¹ ≤ δ := by
  have h0 : Tendsto (fun x : ℂ => ‖x‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
  have h := h0.eventually_ge_atTop (‖σ‖ + |C| / δ + 1)
  filter_upwards [h] with x hx
  have h1 : |C| / δ + 1 ≤ ‖x + σ‖ := by
    have := norm_sub_norm_le x (-σ)
    rw [norm_neg, sub_neg_eq_add] at this
    linarith
  have hpos : 0 < ‖x + σ‖ := lt_of_lt_of_le (by positivity) h1
  rw [← div_eq_mul_inv, div_le_iff₀ hpos]
  have h2 : |C| = δ * (|C| / δ) := by
    first
    | (field_simp; ring)
    | field_simp
  calc C ≤ |C| := le_abs_self C
    _ = δ * (|C| / δ) := h2
    _ ≤ δ * ‖x + σ‖ := by
        apply mul_le_mul_of_nonneg_left _ hδ.le
        linarith

theorem integral_sq_sub_le {μ : Measure ℂ} {u a : ℂ → H} {ab : ℂ → ℝ} (hu : MemLp u 2 μ) (ha : MemLp a 2 μ)
    (hab : MemLp ab 2 μ) (hd : ∀ᵐ D ∂μ, ‖a D‖ ≤ ab D) :
    ∫ D, ‖u D - a D‖ ^ 2 ∂μ ≤ 2 * ∫ D, ‖u D‖ ^ 2 ∂μ + 2 * ∫ D, ab D ^ 2 ∂μ := by
  have i1 : Integrable (fun D => ‖u D - a D‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hu.sub ha).aestronglyMeasurable).1 (hu.sub ha)
  have i2 : Integrable (fun D => ‖u D‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  have i3 : Integrable (fun D => ab D ^ 2) μ := (memLp_two_iff_integrable_sq hab.aestronglyMeasurable).1 hab
  calc ∫ D, ‖u D - a D‖ ^ 2 ∂μ ≤ ∫ D, (2 * ‖u D‖ ^ 2 + 2 * ab D ^ 2) ∂μ := by
        refine integral_mono_ae i1 ((i2.const_mul 2).add (i3.const_mul 2)) ?_
        filter_upwards [hd] with D hD
        have h1 : ‖u D - a D‖ ≤ ‖u D‖ + ‖a D‖ := norm_sub_le _ _
        have h2 : 0 ≤ ‖a D‖ := norm_nonneg _
        have h3 : 0 ≤ ‖u D - a D‖ := norm_nonneg _
        have e1 : ‖u D - a D‖ ^ 2 ≤ (‖u D‖ + ‖a D‖) ^ 2 := pow_le_pow_left₀ h3 h1 2
        have e2 : ‖a D‖ ^ 2 ≤ ab D ^ 2 := pow_le_pow_left₀ h2 hD 2
        nlinarith [sq_nonneg (‖u D‖ - ‖a D‖)]
    _ = 2 * ∫ D, ‖u D‖ ^ 2 ∂μ + 2 * ∫ D, ab D ^ 2 ∂μ := by
        rw [integral_add (i2.const_mul 2) (i3.const_mul 2), integral_const_mul, integral_const_mul]

variable {ι : Type} {μ : Measure ℂ} {Y : Finset ι} {U A : ι × ℂ → ℂ → H} {N : ℂ → ι → ι → ℂ}

end propG

end

end Formalism.FourierDecayAlt.P.PBK
