module

public import Formalism.LandauZeroFreeBounds.NoZeroComplexOf
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ExistsLocalZeroExpansionOfBound
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Formalism.ZeroFreeRegion.FinalZFR
public import Formalism.ZeroFreeRegion.LogDerivRegion
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LGrowth
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LRight
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.TrivReal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Lemma
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaGrowth
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaInvBound

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LocalZeroExpansionWithMultiplicity, Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LocalZerosOf, Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.NoZeroComplexOf, Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Positivity, Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.RealLargeTOf, Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.RealSmallTOf, Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.EulerFactorLogDerivBound, Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ZetaLogDerivLandauBound, Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.TrivLogDeriv, Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.TwoRealOf, Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ZFRDirichletOf, Formalism.LandauZeroFreeBounds.NoZeroComplex

-- ===== clump member: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LocalZeroExpansionWithMultiplicity =====
-- clump-header: {"m": "Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LocalZeroExpansionWithMultiplicity", "h": "module\n\npublic import Formalism.LandauZeroFreeBounds.NoZeroComplexOf\npublic import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ExistsLocalZeroExpansionOfBound\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem localZeroExpansionWithMultiplicity : LandauLocal2 := by
  intro f z₀ r M hr hM hf hfz₀ hbound
  obtain ⟨Z, m, h1, h2, h3, -, h5, h6⟩ := exists_localZeroExpansion_of_bound f z₀ r M hr hM hf hfz₀ hbound
  exact ⟨Z, m, h1, h2, h3, h5, h6⟩

end Formalism.ZeroFreeDirichlet
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LocalZeroExpansionWithMultiplicity =====

-- ===== clump member: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LocalZerosOf =====
-- clump-header: {"m": "Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LocalZerosOf", "h": "module\n\npublic import Formalism.LandauZeroFreeBounds.NoZeroComplexOf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\npublic import Mathlib.NumberTheory.LSeries.Nonvanishing\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma re_sub_le_re_of_mem_closedBall {z₀ w : ℂ} {r : ℝ} (hw : w ∈ Metric.closedBall z₀ r) : z₀.re - r ≤ w.re := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hw
  have h1 := Complex.abs_re_le_norm (w - z₀)
  have h2 := neg_abs_le (w - z₀).re
  rw [Complex.sub_re] at h1 h2
  linarith

lemma norm_le_norm_add_of_mem_closedBall {z₀ w : ℂ} {r : ℝ} (hw : w ∈ Metric.closedBall z₀ r) : ‖w‖ ≤ ‖z₀‖ + r := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hw
  calc ‖w‖ = ‖z₀ + (w - z₀)‖ := by rw [add_sub_cancel]
    _ ≤ ‖z₀‖ + ‖w - z₀‖ := norm_add_le _ _
    _ ≤ ‖z₀‖ + r := by linarith

lemma norm_center_le (t : ℝ) : ‖(11 / 10 : ℂ) + t * I‖ ≤ 11 / 10 + |t| := by
  have h1 : ‖(11 / 10 : ℂ)‖ = 11 / 10 := by
    rw [show (11 / 10 : ℂ) = ((11 / 10 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num)]
  have h2 : ‖(t : ℂ) * I‖ = |t| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  calc ‖(11 / 10 : ℂ) + t * I‖ ≤ ‖(11 / 10 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
    _ = 11 / 10 + |t| := by rw [h1, h2]

lemma re_sum_div_sub (Z : Finset ℂ) (m : ℂ → ℕ) (z : ℂ) :
    (∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)).re = ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / (z - ρ)).re := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [div_eq_mul_one_div, show ((m ρ : ℕ) : ℂ) = ((m ρ : ℝ) : ℂ) by norm_cast, Complex.re_ofReal_mul]

lemma log_le_div_log_two_mul (C₁ L : ℝ) (hC₁ : 1 ≤ C₁) (hL : Real.log 2 ≤ L) :
    Real.log (22 * C₁) ≤ Real.log (22 * C₁) / Real.log 2 * L := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : 0 ≤ Real.log (22 * C₁) := Real.log_nonneg (by linarith)
  rw [div_mul_eq_mul_div, le_div_iff₀ h2]
  exact mul_le_mul_of_nonneg_left hL ha

theorem localZeroSumBoundOfBounds : LocalZerosOf := by
  intro hLan hGr hInv
  obtain ⟨C, hC⟩ := hGr
  set C₁ : ℝ := max C 1 with hC₁def
  have hC₁ : 1 ≤ C₁ := le_max_right _ _
  have hCC : C ≤ C₁ := le_max_left _ _
  refine ⟨120 * (1 + Real.log (22 * C₁) / Real.log 2), ?_⟩
  intro q _ χ hχ t
  set z₀ : ℂ := (11 / 10 : ℂ) + t * I with hz₀
  have hz₀re : z₀.re = 11 / 10 := by
    rw [hz₀, Complex.add_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero, add_zero]
    norm_num
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have ht0 : 0 ≤ |t| := abs_nonneg t
  set M : ℝ := 22 * C₁ * q * (|t| + 2) with hM
  have hM1 : 1 ≤ M := by
    have h1 : 1 ≤ C₁ * q := by nlinarith
    nlinarith
  have hdiff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) (Metric.closedBall z₀ (3 / 5)) :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
  have hnz : ∀ s : ℂ, 1 < s.re → DirichletCharacter.LFunction χ s ≠ 0 := fun s hs =>
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs.le
  have hf0 : DirichletCharacter.LFunction χ z₀ ≠ 0 := hnz z₀ (by rw [hz₀re]; norm_num)
  have hlow : 1 / 11 ≤ ‖DirichletCharacter.LFunction χ z₀‖ := by
    have h := hInv q χ z₀ (by rw [hz₀re]; norm_num)
    rw [hz₀re, show (11 / 10 : ℝ) / (11 / 10 - 1) = 11 by norm_num] at h
    have hpos : 0 < ‖DirichletCharacter.LFunction χ z₀‖ := norm_pos_iff.2 hf0
    rw [inv_le_comm₀ hpos (by norm_num)] at h
    calc (1 / 11 : ℝ) = (11 : ℝ)⁻¹ := by norm_num
      _ ≤ _ := h
  have hbound : ∀ z ∈ Metric.closedBall z₀ (3 / 5),
      ‖DirichletCharacter.LFunction χ z‖ ≤ M * ‖DirichletCharacter.LFunction χ z₀‖ := by
    intro z hz
    have hre : 1 / 2 ≤ z.re := by
      have := re_sub_le_re_of_mem_closedBall hz
      rw [hz₀re] at this
      linarith
    have h1 := hC q χ hχ z hre
    have hn : ‖z‖ ≤ 11 / 10 + |t| + 3 / 5 := by
      have := norm_le_norm_add_of_mem_closedBall hz
      have := norm_center_le t
      linarith
    have hq0 : (0 : ℝ) ≤ q := by linarith
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
    calc ‖DirichletCharacter.LFunction χ z‖ ≤ C * q * (1 + ‖z‖) := h1
      _ ≤ C₁ * q * (1 + ‖z‖) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hq0) (by linarith)
      _ ≤ C₁ * q * (2 * (|t| + 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by linarith) hq0)
      _ = M * (1 / 11) := by rw [hM]; ring
      _ ≤ M * ‖DirichletCharacter.LFunction χ z₀‖ := mul_le_mul_of_nonneg_left hlow (by linarith)
  obtain ⟨Z, m, hZ, hm1, hm2, -, happrox⟩ :=
    hLan (DirichletCharacter.LFunction χ) z₀ (3 / 5) M (by norm_num) hM1 hdiff hf0 hbound
  refine ⟨Z, m, ?_, hm1, hm2, ?_⟩
  · intro ρ
    rw [hZ ρ, show (3 / 5 : ℝ) / 3 = 1 / 5 by norm_num]
  · intro σ hσ1 hσ2
    set s : ℂ := (σ : ℂ) + t * I with hs
    have hsre : s.re = σ := by
      rw [hs, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero, add_zero]
    have hsball : s ∈ Metric.closedBall z₀ ((3 / 5) / 6) := by
      rw [Metric.mem_closedBall, dist_eq_norm, show (3 / 5 : ℝ) / 6 = 1 / 10 by norm_num]
      have hd : s - z₀ = ((σ - 11 / 10 : ℝ) : ℂ) := by
        rw [hs, hz₀]
        push_cast
        ring
      rw [hd, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hfs : DirichletCharacter.LFunction χ s ≠ 0 := hnz s (by rw [hsre]; exact hσ1)
    have hA := happrox s hsball hfs
    have hpos1 : 0 < 22 * C₁ := by linarith
    have hpos2 : 0 < (q : ℝ) * (|t| + 2) := by positivity
    have hL : Real.log 2 ≤ Real.log ((q : ℝ) * (|t| + 2)) :=
      Real.log_le_log (by norm_num) (by nlinarith)
    have hlogM : Real.log M ≤
        (1 + Real.log (22 * C₁) / Real.log 2) * Real.log ((q : ℝ) * (|t| + 2)) := by
      have hMe : M = (22 * C₁) * ((q : ℝ) * (|t| + 2)) := by rw [hM]; ring
      rw [hMe, Real.log_mul hpos1.ne' hpos2.ne']
      have := log_le_div_log_two_mul C₁ _ hC₁ hL
      nlinarith
    have hre := Complex.abs_re_le_norm
      (deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
        ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ))
    have hre' := neg_abs_le
      (deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
        ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)).re
    rw [Complex.sub_re, re_sum_div_sub] at hre hre'
    have h72 : 72 * Real.log M / (3 / 5) = 120 * Real.log M := by ring
    rw [h72] at hA
    have hneg : (negLD χ s).re =
        -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s).re := by
      rw [negLD, Complex.neg_re]
    rw [hneg]
    nlinarith

end Formalism.ZeroFreeDirichlet
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LocalZerosOf =====

-- ===== clump member: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.NoZeroComplexOf =====
-- clump-header: {"m": "Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.NoZeroComplexOf", "h": "module\n\npublic import Formalism.LandauZeroFreeBounds.NoZeroComplexOf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\npublic import Mathlib.NumberTheory.LSeries.Nonvanishing\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma re_one_div_sub_zero_pos_ter {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ)
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (σ t : ℝ) (hσ : 1 < σ) :
    0 < (1 / ((σ : ℂ) + t * I - ρ)).re := by
  have hre : ρ.re < 1 := by
    by_contra h
    push_neg at h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h hρ
  have hwre : ((σ : ℂ) + t * I - ρ).re = σ - ρ.re := by simp
  have hwpos : 0 < ((σ : ℂ) + t * I - ρ).re := by rw [hwre]; linarith
  have hw0 : (σ : ℂ) + t * I - ρ ≠ 0 := fun h => by rw [h] at hwpos; simp at hwpos
  rw [one_div, Complex.inv_re]
  exact div_pos hwpos (Complex.normSq_pos.mpr hw0)

lemma sum_mult_re_one_div_sub_zeros_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (Z : Finset ℂ)
    (m : ℂ → ℕ) (hZ : ∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0) (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + t * I - ρ)).re := by
  exact Finset.sum_nonneg fun ρ hρ =>
    mul_nonneg (Nat.cast_nonneg _) (re_one_div_sub_zero_pos_ter χ hχ ρ (hZ ρ hρ) σ t hσ).le



theorem zeroFreeNonRealCharOfBounds : NoZeroComplexOf := by
  unfold NoZeroComplexOf LocalZeros LLogDerivRight Positivity NoZeroComplex InRegion
  intro hLZ hLD hPos
  obtain ⟨C0, hC0⟩ := hLZ
  obtain ⟨C1, hC1nn, hC1⟩ := hLD
  set K : ℝ := |C0| with hK
  have hKnn : 0 ≤ K := abs_nonneg _
  set A : ℝ := 6 * K + 5 * C1 + 1 with hA
  have hApos : 0 < A := by rw [hA]; linarith
  set δ : ℝ := min (1 / 10) (1 / (2 * A)) with hδ
  have hδpos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 10 := min_le_left _ _
  have hδ2 : δ ≤ 1 / (2 * A) := min_le_right _ _
  refine ⟨δ / 8, by positivity, ?_⟩
  intro q _ χ s hχ2 hreg hzero
  have hχ : χ ≠ 1 := fun h => hχ2 (by rw [h, one_pow])
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set ℓ := Real.log ((q : ℝ) * (|s.im| + 2)) with hℓ
  have hlog2 : Real.log 2 ≤ ℓ :=
    Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg s.im])
  have hl2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith
  have hℓ69 : (0.69 : ℝ) < ℓ := lt_of_lt_of_le hl2 hlog2
  have hℓpos : 0 < ℓ := by linarith
  have hβ1 : s.re < 1 := by
    by_contra h
    push_neg at h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h hzero
  have hsmall : δ / 8 / ℓ ≤ 1 / 10 := by
    rw [div_le_iff₀ hℓpos]
    linarith
  have hβ9 : 9 / 10 ≤ s.re := by linarith
  set σ : ℝ := 1 + δ / ℓ with hσ
  have hvpos : 0 < δ / ℓ := div_pos hδpos hℓpos
  have hσ1 : 1 < σ := by linarith
  have hσ2 : σ ≤ 6 / 5 := by
    have : δ / ℓ ≤ 1 / 5 := by
      rw [div_le_iff₀ hℓpos]
      linarith
    linarith
  set u : ℝ := 1 / δ with hu

  have b0 : (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ)).re ≤ ℓ * u + C1 := by
    have h1 := hC1 q 1 (σ : ℂ) (by simpa using hσ1)
    have h2 := Complex.re_le_norm (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ))
    have h3 : 1 / ((σ : ℂ).re - 1) = ℓ * u := by
      rw [Complex.ofReal_re, hσ, hu, add_sub_cancel_left, one_div_div, div_eq_mul_one_div]
    rw [h3] at h1
    linarith

  obtain ⟨Z, m, hZ, hm1, -, hbd⟩ := hC0 q χ hχ s.im
  have hsZ : s ∈ Z := by
    refine (hZ s).mpr ⟨?_, hzero⟩
    have e : s - ((11 / 10 : ℂ) + s.im * I) = ((s.re - 11 / 10 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [mem_closedBall_iff_norm, e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hterm : 1 / (σ - s.re) ≤ (m s : ℝ) * (1 / ((σ : ℂ) + s.im * I - s)).re := by
    have e : (σ : ℂ) + s.im * I - s = ((σ - s.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    have e2 : (1 / ((σ - s.re : ℝ) : ℂ)).re = 1 / (σ - s.re) := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
    rw [e, e2]
    have hm : (1 : ℝ) ≤ (m s : ℝ) := by exact_mod_cast hm1 s hsZ
    have hpos : 0 < 1 / (σ - s.re) := by apply div_pos one_pos; linarith
    nlinarith
  have hsum : (m s : ℝ) * (1 / ((σ : ℂ) + s.im * I - s)).re ≤
      ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + s.im * I - ρ)).re :=
    Finset.single_le_sum (f := fun ρ => (m ρ : ℝ) * (1 / ((σ : ℂ) + s.im * I - ρ)).re)
      (fun ρ hρ => mul_nonneg (Nat.cast_nonneg _)
        (re_one_div_sub_zero_pos_ter χ hχ ρ ((hZ ρ).mp hρ).2 σ s.im hσ1).le) hsZ
  have hgap : σ - s.re ≤ (9 / 8) * (δ / ℓ) := by
    have : δ / 8 / ℓ = (δ / ℓ) / 8 := by ring
    rw [hσ]
    linarith
  have hgappos : 0 < σ - s.re := by linarith
  have hinv : (8 / 9) * (ℓ * u) ≤ 1 / (σ - s.re) := by
    have h1 := one_div_le_one_div_of_le hgappos hgap
    have h2 : 1 / ((9 / 8) * (δ / ℓ)) = (8 / 9) * (ℓ * u) := by
      rw [hu]
      field_simp
    linarith
  have b1 : (negLD χ ((σ : ℂ) + s.im * I)).re ≤ K * ℓ - (8 / 9) * (ℓ * u) := by
    have h1 := hbd σ hσ1 hσ2
    rw [← hℓ] at h1
    have h2 : C0 * ℓ ≤ K * ℓ := mul_le_mul_of_nonneg_right (le_abs_self C0) hℓpos.le
    linarith

  obtain ⟨Z2, m2, hZ2, -, -, hbd2⟩ := hC0 q (χ ^ 2) hχ2 (2 * s.im)
  have hL2 : Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ 2 * ℓ := by
    have ha := abs_nonneg s.im
    have h1 : Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ Real.log (((q : ℝ) * (|s.im| + 2)) ^ 2) := by
      apply Real.log_le_log
      · rw [abs_mul, abs_two]
        positivity
      · rw [abs_mul, abs_two]
        nlinarith [mul_le_mul_of_nonneg_right hq (sq_nonneg (|s.im| + 2))]
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hL2nn : 0 ≤ Real.log ((q : ℝ) * (|2 * s.im| + 2)) :=
    Real.log_nonneg (by nlinarith [abs_nonneg (2 * s.im)])
  have b2 : (negLD (χ ^ 2) ((σ : ℂ) + 2 * s.im * I)).re ≤ 2 * (K * ℓ) := by
    have h1 := hbd2 σ hσ1 hσ2
    push_cast at h1
    have h2 := sum_mult_re_one_div_sub_zeros_nonneg (χ ^ 2) hχ2 Z2 m2 (fun ρ hρ => ((hZ2 ρ).mp hρ).2) σ (2 * s.im) hσ1
    push_cast at h2
    have h3 : C0 * Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ K * Real.log ((q : ℝ) * (|2 * s.im| + 2)) :=
      mul_le_mul_of_nonneg_right (le_abs_self C0) hL2nn
    have h4 : K * Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ K * (2 * ℓ) :=
      mul_le_mul_of_nonneg_left hL2 hKnn
    have h5 : K * (2 * ℓ) = 2 * (K * ℓ) := by ring
    linarith

  have hP := (hPos q σ hσ1).1 χ s.im
  have hu2 : 2 * A ≤ u := by
    have h1 := one_div_le_one_div_of_le hδpos hδ2
    rw [one_div_one_div] at h1
    exact h1
  have cu : 12 * (K * ℓ) + 10 * (C1 * ℓ) + 2 * ℓ ≤ ℓ * u := by
    have h1 := mul_le_mul_of_nonneg_left hu2 hℓpos.le
    have e : ℓ * (2 * A) = 12 * (K * ℓ) + 10 * (C1 * ℓ) + 2 * ℓ := by rw [hA]; ring
    linarith
  have c1 : 3 * C1 ≤ 5 * (C1 * ℓ) := by
    have := mul_le_mul_of_nonneg_left hℓ69.le hC1nn
    linarith
  have hKl : 0 ≤ K * ℓ := mul_nonneg hKnn hℓpos.le
  have hCl : 0 ≤ C1 * ℓ := mul_nonneg hC1nn hℓpos.le
  linarith

end Formalism.ZeroFreeDirichlet
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.NoZeroComplexOf =====

-- ===== clump member: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Positivity =====
-- clump-header: {"m": "Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Positivity", "h": "module\n\npublic import Formalism.LandauZeroFreeBounds.NoZeroComplexOf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Complex LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma negLogDeriv_eq_LSeries {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) : negLD χ s = LSeries (↗χ * ↗Λ) s := by
  unfold negLD
  rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs,
    DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  ring

lemma hasSum_re_term {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) : HasSum (fun n ↦ (term (↗χ * ↗Λ) s n).re) (negLD χ s).re := by
  rw [negLogDeriv_eq_LSeries χ hs]
  exact Complex.hasSum_re (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs).hasSum

lemma term_ofReal_add_mul_I {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ u : ℝ) (n : ℕ) :
    term (↗χ * ↗Λ) ((σ : ℂ) + u * I) n =
      ((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ) * (χ n / (n : ℂ) ^ ((u : ℂ) * I)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_def]
  · have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [LSeries.term_def, if_neg hn, Complex.cpow_add _ _ hn']
    push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    simp only [Pi.mul_apply]
    rw [div_mul_div_comm]
    ring

lemma term_ofReal {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ : ℝ) (n : ℕ) :
    term (↗χ * ↗Λ) (σ : ℂ) n = ((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ) * χ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_def]
  · rw [LSeries.term_def, if_neg hn]
    push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    simp only [Pi.mul_apply]
    ring

lemma vonMangoldt_div_rpow_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ Λ n / (n : ℝ) ^ σ :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ)

lemma term_three_four_one_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ t : ℝ) (n : ℕ) :
    0 ≤ 3 * (term (↗(1 : DirichletCharacter ℂ q) * ↗Λ) (σ : ℂ) n).re
      + 4 * (term (↗χ * ↗Λ) ((σ : ℂ) + t * I) n).re
      + (term (↗(χ ^ 2) * ↗Λ) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_def]
  have ha := vonMangoldt_div_rpow_nonneg σ n
  rw [term_ofReal, term_ofReal_add_mul_I, term_ofReal_add_mul_I]
  by_cases hu : IsUnit (n : ZMod q)
  · have h1 : (1 : DirichletCharacter ℂ q) n = 1 := MulChar.one_apply hu
    have h2 : (χ ^ 2) n = (χ n) ^ 2 := MulChar.pow_apply' χ two_ne_zero _
    have hχ1 : ‖χ n‖ = 1 := by
      have := DirichletCharacter.unit_norm_eq_one χ hu.unit
      rwa [IsUnit.unit_spec] at this
    have hc : ‖(n : ℂ) ^ ((t : ℂ) * I)‖ = 1 := by
      rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp
    have hc2 : (n : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) = ((n : ℂ) ^ ((t : ℂ) * I)) ^ 2 := by
      rw [← Complex.cpow_nat_mul]
      push_cast
      ring_nf
    set w := χ n / (n : ℂ) ^ ((t : ℂ) * I) with hw_def
    have hw : ‖w‖ = 1 := by rw [hw_def, norm_div, hχ1, hc, div_one]
    have hw2 : (χ ^ 2) n / (n : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) = w ^ 2 := by
      rw [h2, hc2, div_pow]
    rw [h1, hw2]
    have hn1 : w.re * w.re + w.im * w.im = 1 := by
      rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hw]
      norm_num
    have hre : (w ^ 2).re = 2 * w.re ^ 2 - 1 := by
      rw [sq, Complex.mul_re]
      nlinarith [hn1]
    rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul, hre, Complex.one_re]
    nlinarith [mul_nonneg ha (sq_nonneg (1 + w.re))]
  · have h1 : (1 : DirichletCharacter ℂ q) n = 0 := MulChar.map_nonunit _ hu
    have h2 : χ n = 0 := MulChar.map_nonunit _ hu
    have h3 : (χ ^ 2) n = 0 := MulChar.map_nonunit _ hu
    simp [h1, h2, h3]

lemma eq_one_or_eq_neg_one_of_sq_eq_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1)
    {n : ℕ} (hu : IsUnit (n : ZMod q)) : χ n = 1 ∨ χ n = -1 := by
  have h : χ n * χ n = 1 := by
    rw [← pow_two, ← MulChar.pow_apply' χ two_ne_zero, hχ, MulChar.one_apply hu]
  exact mul_self_eq_one_iff.mp h

lemma term_one_add_real_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1)
    (σ : ℝ) (n : ℕ) :
    0 ≤ (term (↗(1 : DirichletCharacter ℂ q) * ↗Λ) (σ : ℂ) n).re
      + (term (↗χ * ↗Λ) (σ : ℂ) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_def]
  have ha := vonMangoldt_div_rpow_nonneg σ n
  rw [term_ofReal, term_ofReal]
  by_cases hu : IsUnit (n : ZMod q)
  · rw [MulChar.one_apply hu]
    rcases eq_one_or_eq_neg_one_of_sq_eq_one χ hχ hu with h | h <;> rw [h] <;>
      simp only [Complex.re_ofReal_mul, Complex.one_re, Complex.neg_re] <;> linarith
  · rw [MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu]
    simp

lemma term_two_real_nonneg {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1) (σ : ℝ) (n : ℕ) :
    0 ≤ (term (↗(1 : DirichletCharacter ℂ q) * ↗Λ) (σ : ℂ) n).re
      + (term (↗χ₁ * ↗Λ) (σ : ℂ) n).re + (term (↗χ₂ * ↗Λ) (σ : ℂ) n).re
      + (term (↗(χ₁ * χ₂) * ↗Λ) (σ : ℂ) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_def]
  have ha := vonMangoldt_div_rpow_nonneg σ n
  rw [term_ofReal, term_ofReal, term_ofReal,
    term_ofReal, MulChar.mul_apply]
  by_cases hu : IsUnit (n : ZMod q)
  · rw [MulChar.one_apply hu]
    rcases eq_one_or_eq_neg_one_of_sq_eq_one χ₁ h₁ hu with h | h <;>
      rcases eq_one_or_eq_neg_one_of_sq_eq_one χ₂ h₂ hu with h' | h' <;> rw [h, h'] <;>
      generalize Λ n / (n : ℝ) ^ σ = a at ha ⊢ <;>
      simp <;> linarith
  · rw [MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu]
    simp

theorem negLogDerivPositivity : Positivity := by
  intro q _ σ hσ
  have hs1 : 1 < ((σ : ℂ)).re := by simpa using hσ
  have H1 : ∀ χ : DirichletCharacter ℂ q, HasSum (fun n ↦ (term (↗χ * ↗Λ) (σ : ℂ) n).re)
      (negLD χ (σ : ℂ)).re := fun χ => hasSum_re_term χ hs1
  refine ⟨fun χ t => ?_, fun χ hχ => ?_, fun χ₁ χ₂ h₁ h₂ => ?_⟩
  · have hs2 : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
    have hs3 : 1 < ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I).re := by simpa using hσ
    have HS := (((H1 1).mul_left 3).add ((hasSum_re_term χ hs2).mul_left 4)).add
      (hasSum_re_term (χ ^ 2) hs3)
    have e : ((σ : ℂ) + 2 * t * I) = (σ : ℂ) + ((2 * t : ℝ) : ℂ) * I := by push_cast; ring
    rw [e]
    exact HasSum.nonneg (fun n => term_three_four_one_nonneg χ σ t n) HS
  · exact HasSum.nonneg (fun n => term_one_add_real_nonneg χ hχ σ n) ((H1 1).add (H1 χ))
  · exact HasSum.nonneg (fun n => term_two_real_nonneg χ₁ χ₂ h₁ h₂ σ n)
      ((((H1 1).add (H1 χ₁)).add (H1 χ₂)).add (H1 (χ₁ * χ₂)))

end Formalism.ZeroFreeDirichlet
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Positivity =====

-- ===== clump member: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.RealLargeTOf =====
-- clump-header: {"m": "Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.RealLargeTOf", "h": "module\n\npublic import Formalism.LandauZeroFreeBounds.NoZeroComplexOf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\npublic import Mathlib.NumberTheory.LSeries.Nonvanishing\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma re_one_div_sub_zero_pos {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ)
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (σ t : ℝ) (hσ : 1 < σ) :
    0 < (1 / ((σ : ℂ) + t * I - ρ)).re := by
  have hre : ρ.re < 1 := by
    by_contra hc
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (Or.inl hχ) (not_lt.mp hc) hρ
  have hwre : ((σ : ℂ) + t * I - ρ).re = σ - ρ.re := by simp
  have hw0 : (σ : ℂ) + t * I - ρ ≠ 0 := fun h => by
    have h' : ((σ : ℂ) + t * I - ρ).re = 0 := by rw [h, Complex.zero_re]
    linarith
  rw [one_div, Complex.inv_re]
  exact div_pos (by rw [hwre]; linarith) (Complex.normSq_pos.mpr hw0)

lemma re_one_div_ofReal_add_mul_I (x y : ℝ) :
    (1 / ((x : ℂ) + y * I)).re = x / (x ^ 2 + y ^ 2) := by
  rw [one_div, Complex.inv_re, Complex.normSq_add_mul_I]
  simp

lemma two_le_mul_abs_add_two (q : ℕ) [NeZero q] (t : ℝ) : 2 ≤ (q : ℝ) * (|t| + 2) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  nlinarith [abs_nonneg t]

lemma log_mul_abs_two_mul_le (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log ((q : ℝ) * (|2 * t| + 2)) ≤ 2 * Real.log ((q : ℝ) * (|t| + 2)) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have ht := abs_nonneg t
  have e : 2 * Real.log ((q : ℝ) * (|t| + 2)) = Real.log (((q : ℝ) * (|t| + 2)) ^ 2) := by
    rw [Real.log_pow]
    norm_num
  rw [abs_mul, abs_two, e]
  apply Real.log_le_log (by positivity)
  have h1 : (q : ℝ) * (2 * |t| + 2) ≤ (q : ℝ) * (|t| + 2) ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have h2 : (q : ℝ) * (|t| + 2) ^ 2 ≤ ((q : ℝ) * (|t| + 2)) ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  linarith

theorem realCharZeroFreeLargeHeightOfBounds : RealLargeTOf := by
  intro hLZ hLD hPos hTriv δ hδ
  obtain ⟨C₁, hC₁⟩ := hLZ
  obtain ⟨C₂, hC₂0, hC₂⟩ := hLD
  obtain ⟨C₃, hC₃⟩ := hTriv
  have hM₁ : 0 ≤ max C₁ 0 := le_max_right _ _
  have hM₃ : 0 ≤ max C₃ 0 := le_max_right _ _
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 4 * max C₁ 0 + 2 * max C₃ 0 + 6 * C₂ := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = min (δ / 2) (min (1 / 10) (1 / (4 * K + 1))) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; exact lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have ha1 : a ≤ δ / 2 := by rw [ha]; exact min_le_left _ _
  have ha2 : a ≤ 1 / 10 := by rw [ha]; exact (min_le_right _ _).trans (min_le_left _ _)
  have ha3 : a ≤ 1 / (4 * K + 1) := by rw [ha]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hKa : K * a ≤ 1 / 4 := by
    rw [le_div_iff₀ (by positivity)] at ha3
    nlinarith
  have hδa : a ^ 2 / (4 * δ ^ 2) ≤ 1 / 16 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨a / 8, by positivity, ?_⟩
  intro q _ χ s hχ2 hχ1 hδt hreg hzero
  have hreg' : 1 - a / 8 / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re := hreg
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log ((q : ℝ) * (|s.im| + 2)) := ⟨_, rfl⟩
  rw [← hLdef] at hreg' hδt
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hL : 1 / 2 < L := by
    rw [hLdef]
    exact lt_of_lt_of_le hlog2 (Real.log_le_log (by norm_num) (two_le_mul_abs_add_two q s.im))
  have hLpos : 0 < L := by linarith
  have hβ1 : s.re < 1 := by
    by_contra hc
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (Or.inl hχ1) (not_lt.mp hc)
      hzero
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = 1 + a / L := ⟨_, rfl⟩
  have haL : 0 < a / L := div_pos ha0 hLpos
  have haL5 : a / L ≤ 1 / 5 := by
    rw [div_le_iff₀ hLpos]
    linarith
  have hσ1 : 1 < σ := by linarith
  have hσ65 : σ ≤ 6 / 5 := by linarith
  have ha8 : a / 8 / L = (a / L) / 8 := by ring
  have hσβ : σ - s.re ≤ 9 / 8 * (a / L) := by linarith
  have hσβpos : 0 < σ - s.re := by linarith
  obtain ⟨Z, m, hZ, hm1, -, hbd⟩ := hC₁ q χ hχ1 s.im
  have hsZ : s ∈ Z := by
    rw [hZ]
    refine ⟨?_, hzero⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hd : s - ((11 / 10 : ℂ) + s.im * I) = ((s.re - 11 / 10 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [hd, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have : a / L / 8 ≤ 1 / 40 := by linarith
    constructor <;> linarith
  have hterm : ∀ ρ ∈ Z, 0 ≤ (m ρ : ℝ) * (1 / ((σ : ℂ) + s.im * I - ρ)).re := fun ρ hρ =>
    mul_nonneg (Nat.cast_nonneg _)
      (re_one_div_sub_zero_pos χ hχ1 ρ ((hZ ρ).mp hρ).2 σ s.im hσ1).le
  have hs_term : (1 / ((σ : ℂ) + s.im * I - s)).re = 1 / (σ - s.re) := by
    have hd : (σ : ℂ) + s.im * I - s = ((σ - s.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [hd, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  have hsum : 1 / (σ - s.re) ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + s.im * I - ρ)).re := by
    refine le_trans ?_ (Finset.single_le_sum hterm hsZ)
    rw [hs_term]
    have h1 : (1 : ℝ) ≤ m s := by exact_mod_cast hm1 s hsZ
    have h0 : 0 ≤ 1 / (σ - s.re) := by positivity
    nlinarith
  have hu : 8 / 9 * (L / a) ≤ 1 / (σ - s.re) := by
    have h1 := one_div_le_one_div_of_le hσβpos hσβ
    have e : 1 / (9 / 8 * (a / L)) = 8 / 9 * (L / a) := by field_simp
    rw [e] at h1
    exact h1
  have hP := (hPos q σ hσ1).1 χ s.im
  rw [hχ2] at hP
  have h1 : (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ)).re ≤ L / a + C₂ := by
    have h := hC₂ q 1 (σ : ℂ) (by simpa using hσ1)
    have e : 1 / ((σ : ℂ).re - 1) = L / a := by
      rw [Complex.ofReal_re, hσ, add_sub_cancel_left, one_div_div]
    rw [e] at h
    exact (Complex.re_le_norm _).trans h
  have h2 := hbd σ hσ1 hσ65
  rw [← hLdef] at h2
  have h3 := hC₃ q σ (2 * s.im) hσ1 (by linarith)
  have hpole := re_one_div_ofReal_add_mul_I (σ - 1) (2 * s.im)
  push_cast at h3 hpole
  rw [hpole] at h3
  have ht2 : δ ^ 2 / L ^ 2 ≤ s.im ^ 2 := by
    have h0 : 0 ≤ δ / L := by positivity
    have h := pow_le_pow_left₀ h0 hδt 2
    rwa [div_pow, sq_abs] at h
  have hσ1' : σ - 1 = a / L := by rw [hσ]; ring
  have hpb : (σ - 1) / ((σ - 1) ^ 2 + (2 * s.im) ^ 2) ≤ a * L / (4 * δ ^ 2) := by
    rw [hσ1']
    have hden : 0 < (a / L) ^ 2 + (2 * s.im) ^ 2 := by positivity
    rw [div_le_iff₀ hden]
    have e : a / L = a * L / (4 * δ ^ 2) * (4 * (δ ^ 2 / L ^ 2)) := by field_simp
    have hc : 0 ≤ a * L / (4 * δ ^ 2) := by positivity
    calc a / L = a * L / (4 * δ ^ 2) * (4 * (δ ^ 2 / L ^ 2)) := e
      _ ≤ a * L / (4 * δ ^ 2) * ((a / L) ^ 2 + (2 * s.im) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hc
        nlinarith [sq_nonneg (a / L)]
  have hX0 : 0 ≤ Real.log ((q : ℝ) * (|2 * s.im| + 2)) :=
    Real.log_nonneg (by have := two_le_mul_abs_add_two q (2 * s.im); linarith)
  have hX : Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ 2 * L := by
    rw [hLdef]; exact log_mul_abs_two_mul_le q s.im
  have hC3X : C₃ * Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ max C₃ 0 * (2 * L) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hX0).trans (mul_le_mul_of_nonneg_left hX hM₃)
  have hC1L : C₁ * L ≤ max C₁ 0 * L := mul_le_mul_of_nonneg_right (le_max_left _ _) hLpos.le
  have hw : 0 < L / a := div_pos hLpos ha0
  have hKL : K * L ≤ L / a / 4 := by
    calc K * L = K * a * (L / a) := by field_simp
      _ ≤ 1 / 4 * (L / a) := mul_le_mul_of_nonneg_right hKa hw.le
      _ = L / a / 4 := by ring
  have hKL' : K * L = 4 * max C₁ 0 * L + 2 * max C₃ 0 * L + 6 * C₂ * L := by rw [hK]; ring
  have hPw : a * L / (4 * δ ^ 2) ≤ L / a / 16 := by
    calc a * L / (4 * δ ^ 2) = a ^ 2 / (4 * δ ^ 2) * (L / a) := by field_simp
      _ ≤ 1 / 16 * (L / a) := mul_le_mul_of_nonneg_right hδa hw.le
      _ = L / a / 16 := by ring
  have hC2 : 3 * C₂ ≤ 6 * C₂ * L := by
    have h := mul_nonneg hC₂0 (show (0 : ℝ) ≤ 2 * L - 1 by linarith)
    linarith
  linarith [h1, h2, h3, hpb, hC3X, hC1L, hsum, hu, hKL, hKL', hPw, hC2, hP]

end Formalism.ZeroFreeDirichlet
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.RealLargeTOf =====

-- ===== clump member: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.RealSmallTOf =====
-- clump-header: {"m": "Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.RealSmallTOf", "h": "module\n\npublic import Formalism.LandauZeroFreeBounds.NoZeroComplexOf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\npublic import Mathlib.NumberTheory.LSeries.Nonvanishing\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma re_one_div_sub_zero_pos' {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ)
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (σ : ℝ) (hσ : 1 < σ) :
    0 < (1 / ((σ : ℂ) - ρ)).re := by
  have hre : ρ.re < 1 := by
    by_contra h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (not_lt.mp h) hρ
  have hz : ((σ : ℂ) - ρ).re = σ - ρ.re := by simp
  have hpos : 0 < ((σ : ℂ) - ρ).re := by rw [hz]; linarith
  have hne : ((σ : ℂ) - ρ) ≠ 0 := by
    intro h; rw [h] at hpos; simp at hpos
  rw [one_div, Complex.inv_re]
  exact div_pos hpos (Complex.normSq_pos.mpr hne)

lemma re_one_div_ofReal_sub (σ : ℝ) (ρ : ℂ) :
    (1 / ((σ : ℂ) - ρ)).re = (σ - ρ.re) / ((σ - ρ.re) ^ 2 + ρ.im ^ 2) := by
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma mul_le_div_sq_add_sq (T X G : ℝ) (hT : 0 < T) (h1 : 1 ≤ T * X) (h2 : T * X ≤ 11 / 10)
    (h3 : |T * G| ≤ 1 / 10) : 4 / 5 * T ≤ X / (X ^ 2 + G ^ 2) := by
  have hX : 0 < X := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  have hv : (T * G) ^ 2 ≤ 1 / 100 := by
    have := sq_abs (T * G)
    nlinarith [abs_nonneg (T * G)]
  have key : T * (4 / 5 * T * (X ^ 2 + G ^ 2)) ≤ T * X := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ T * X) (by linarith : 0 ≤ 11 / 10 - T * X)]
  have := le_of_mul_le_mul_left key hT
  rw [le_div_iff₀ (add_pos_of_pos_of_nonneg (pow_pos hX 2) (sq_nonneg G))]
  exact this

theorem realCharZeroSmallHeightOfBounds : RealSmallTOf := by
  intro hLZ hLD hPos hConj
  obtain ⟨C, hC⟩ := hLZ
  obtain ⟨C₀, hC₀, hLD⟩ := hLD
  set Cp : ℝ := max C 0 with hCp
  have hCp0 : 0 ≤ Cp := le_max_right _ _
  have hCCp : C ≤ Cp := le_max_left _ _
  set K : ℝ := 2 * C₀ + Cp with hK
  have hK0 : 0 ≤ K := by rw [hK]; linarith
  set W : ℝ := 10 * (K + 1) with hW
  have hW10 : 10 ≤ W := by rw [hW]; linarith
  have hWpos : 0 < W := by linarith
  refine ⟨1 / (10 * W), 1 / (10 * W), by positivity, by positivity, ?_⟩
  intro q _ χ hχ2 hχ
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)

  obtain ⟨Z, m, hZ, hm1, hm2, hb⟩ := hC q χ hχ 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at hZ hb
  set L₀ := Real.log ((q : ℝ) * 2) with hL₀
  have hlog2 := Real.log_two_gt_d9
  have hL₀2 : Real.log 2 ≤ L₀ := Real.log_le_log (by norm_num) (by nlinarith)
  have hL₀h : 1 / 2 < L₀ := by norm_num at hlog2; linarith
  have hL₀pos : 0 < L₀ := by linarith
  set T : ℝ := W * L₀ with hT
  have hTpos : 0 < T := mul_pos hWpos hL₀pos
  have hT5 : 5 ≤ T := by rw [hT]; nlinarith
  have hTe : T = 10 * (K * L₀) + 10 * L₀ := by rw [hT, hW]; ring
  have hKL : K * L₀ = 2 * (C₀ * L₀) + Cp * L₀ := by rw [hK]; ring
  set σ : ℝ := 1 + 1 / T with hσ
  have hσ1 : 1 < σ := by
    have : 0 < 1 / T := by positivity
    linarith
  have hσ2 : σ ≤ 6 / 5 := by
    have : 1 / T ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) hT5
    linarith

  have hF1 : ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re ≤ (11 * K + 10) * L₀ := by
    have hP := (hPos q σ hσ1).2.1 χ hχ2
    have h0 : (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ)).re ≤ T + C₀ := by
      have h := hLD q 1 (σ : ℂ) (by simpa using hσ1)
      have e : 1 / ((σ : ℂ).re - 1) = T := by
        rw [Complex.ofReal_re, hσ, add_sub_cancel_left, one_div_one_div]
      rw [e] at h
      exact (Complex.re_le_norm _).trans h
    have h1 := hb σ hσ1 hσ2
    have h2 : C * L₀ ≤ Cp * L₀ := mul_le_mul_of_nonneg_right hCCp hL₀pos.le
    have h3 : C₀ ≤ 2 * (C₀ * L₀) := by nlinarith
    have h4 : (11 * K + 10) * L₀ = 11 * (K * L₀) + 10 * L₀ := by ring
    rw [h4]
    linarith

  have hnn : ∀ ρ ∈ Z, 0 ≤ (m ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re := fun ρ hρ =>
    mul_nonneg (Nat.cast_nonneg _) (re_one_div_sub_zero_pos' χ hχ ρ ((hZ ρ).mp hρ).2 σ hσ1).le

  have hcons : ∀ ρ : ℂ, |ρ.im| < 1 / (10 * W) / Real.log ((q : ℝ) * (|ρ.im| + 2)) →
      InRegion (1 / (10 * W)) q ρ → DirichletCharacter.LFunction χ ρ = 0 →
      ρ ∈ Z ∧ 4 / 5 * T ≤ (1 / ((σ : ℂ) - ρ)).re := by
    intro ρ hi hr hz
    unfold InRegion at hr
    obtain ⟨Lρ, hLρdef⟩ : ∃ x : ℝ, x = Real.log ((q : ℝ) * (|ρ.im| + 2)) := ⟨_, rfl⟩
    rw [← hLρdef] at hi hr
    have hLρ : L₀ ≤ Lρ := by
      rw [hLρdef, hL₀]
      exact Real.log_le_log (by positivity) (by nlinarith [abs_nonneg ρ.im])
    have hdiv : 1 / (10 * W) / Lρ ≤ 1 / (10 * T) := by
      have := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 1 / (10 * W)) hL₀pos hLρ
      have e : 1 / (10 * W) / L₀ = 1 / (10 * T) := by rw [hT, div_div, mul_assoc]
      linarith
    have hβ1 : ρ.re < 1 := by
      by_contra h
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (not_lt.mp h) hz
    have hβ : 1 - 1 / (10 * T) ≤ ρ.re := by linarith
    have hγ : |ρ.im| ≤ 1 / (10 * T) := by linarith
    have hsmall : 1 / (10 * T) ≤ 1 / 50 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    have hTT : T * (1 / (10 * T)) = 1 / 10 := by field_simp
    refine ⟨(hZ ρ).mpr ⟨?_, hz⟩, ?_⟩
    · rw [Metric.mem_closedBall, Complex.dist_eq]
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      have e0 : (11 / 10 : ℂ) = ((11 / 10 : ℝ) : ℂ) := by push_cast; rfl
      rw [e0, Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
      have : |ρ.re - 11 / 10| ≤ 1 / 10 + 1 / (10 * T) := by
        rw [abs_le]; constructor <;> linarith
      linarith
    · rw [re_one_div_ofReal_sub]
      have hTσ : T * (σ - ρ.re) = T * (1 - ρ.re) + 1 := by
        rw [hσ]; field_simp; ring
      have hA : 0 < T * (1 - ρ.re) := mul_pos hTpos (by linarith)
      have hB : T * (1 - ρ.re) ≤ T * (1 / (10 * T)) :=
        mul_le_mul_of_nonneg_left (by linarith) hTpos.le
      apply mul_le_div_sq_add_sq T (σ - ρ.re) ρ.im hTpos
      · rw [hTσ]; linarith
      · rw [hTσ]; linarith
      · rw [abs_mul, abs_of_pos hTpos]
        have := mul_le_mul_of_nonneg_left hγ hTpos.le
        linarith
  have hbig : (11 * K + 10) * L₀ < 8 / 5 * T := by
    have : 0 ≤ K * L₀ := mul_nonneg hK0 hL₀pos.le
    nlinarith

  have htwo : ∀ ρ₁ ρ₂ : ℂ,
      (|ρ₁.im| < 1 / (10 * W) / Real.log ((q : ℝ) * (|ρ₁.im| + 2)) ∧
        InRegion (1 / (10 * W)) q ρ₁ ∧ DirichletCharacter.LFunction χ ρ₁ = 0) →
      (|ρ₂.im| < 1 / (10 * W) / Real.log ((q : ℝ) * (|ρ₂.im| + 2)) ∧
        InRegion (1 / (10 * W)) q ρ₂ ∧ DirichletCharacter.LFunction χ ρ₂ = 0) →
      ρ₁ ≠ ρ₂ → False := by
    rintro ρ₁ ρ₂ ⟨a1, b1, c1⟩ ⟨a2, b2, c2⟩ hne
    obtain ⟨h1Z, h1r⟩ := hcons ρ₁ a1 b1 c1
    obtain ⟨h2Z, h2r⟩ := hcons ρ₂ a2 b2 c2
    have hsub : ({ρ₁, ρ₂} : Finset ℂ) ⊆ Z := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h1Z
      · exact h2Z
    have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ρ hρ _ => hnn ρ hρ)
    rw [Finset.sum_pair hne] at hs
    have hm1' : (1 : ℝ) ≤ m ρ₁ := by exact_mod_cast hm1 ρ₁ h1Z
    have hm2' : (1 : ℝ) ≤ m ρ₂ := by exact_mod_cast hm1 ρ₂ h2Z
    have hr1 : 0 ≤ (1 / ((σ : ℂ) - ρ₁)).re := by linarith
    have hr2 : 0 ≤ (1 / ((σ : ℂ) - ρ₂)).re := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hm1') hr1, mul_nonneg (sub_nonneg.mpr hm2') hr2]

  have hdouble : ∀ ρ : ℂ, |ρ.im| < 1 / (10 * W) / Real.log ((q : ℝ) * (|ρ.im| + 2)) →
      InRegion (1 / (10 * W)) q ρ → DirichletCharacter.LFunction χ ρ = 0 →
      deriv (DirichletCharacter.LFunction χ) ρ = 0 → False := by
    intro ρ a b c hd
    obtain ⟨hρZ, hρr⟩ := hcons ρ a b c
    have hs := Finset.single_le_sum hnn hρZ
    have hm : (2 : ℝ) ≤ m ρ := by exact_mod_cast hm2 ρ hρZ hd
    have hr : 0 ≤ (1 / ((σ : ℂ) - ρ)).re := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hm) hr]
  intro s s' hs hs' hrs hrs' hz hz'
  have hsim : s.im = 0 := by
    by_contra hne
    refine htwo s (starRingEnd ℂ s) ⟨hs, hrs, hz⟩ ⟨?_, ?_, ?_⟩ ?_
    · simpa [Complex.conj_im, abs_neg] using hs
    · unfold InRegion at hrs ⊢
      simpa [Complex.conj_re, Complex.conj_im, abs_neg] using hrs
    · rw [hConj q χ hχ2 hχ s, hz, map_zero]
    · intro h
      apply hne
      have := congrArg Complex.im h
      rw [Complex.conj_im] at this
      linarith
  refine ⟨hsim, fun hd => hdouble s hs hrs hz hd, ?_⟩
  by_contra hne
  exact htwo s' s ⟨hs', hrs', hz'⟩ ⟨hs, hrs, hz⟩ hne

end Formalism.ZeroFreeDirichlet
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.RealSmallTOf =====

-- ===== clump member: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.EulerFactorLogDerivBound =====
-- clump-header: {"m": "Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.EulerFactorLogDerivBound", "h": "module\n\npublic import Formalism.LandauZeroFreeBounds.NoZeroComplexOf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Complex Filter Topology

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma euler_factor_logDeriv_bound (p : ℕ) (hp : p.Prime) (s : ℂ) (hs : 1 < s.re) :
    (1 - (p : ℂ) ^ (-s)) ≠ 0 ∧ DifferentiableAt ℂ (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s ∧
    ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ ≤ Real.log p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hw : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  have hx : (p : ℝ) ^ (-s.re) ≤ 1 / 2 := by
    have h1 : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    rw [Real.rpow_neg_one] at h1
    have h2 : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have hx0 : 0 ≤ (p : ℝ) ^ (-s.re) := Real.rpow_nonneg (by linarith) _
  have hden : 1 / 2 ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))
    rw [norm_one, hw] at this
    linarith
  have hne : (1 - (p : ℂ) ^ (-s)) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hden
    linarith
  have hder : HasDerivAt (fun z : ℂ => 1 - (p : ℂ) ^ (-z))
      ((p : ℂ) ^ (-s) * Complex.log p) s := by
    have h1 : HasDerivAt (fun z : ℂ => (p : ℂ) ^ (-z)) ((p : ℂ) ^ (-s) * Complex.log p * (-1)) s :=
      (hasDerivAt_id s).neg.const_cpow (Or.inl hp0)
    have h2 := (hasDerivAt_const s (1 : ℂ)).sub h1
    exact h2.congr_deriv (by ring)
  refine ⟨hne, hder.differentiableAt, ?_⟩
  have hL : 0 ≤ Real.log p := Real.log_nonneg hp1
  have hlog : Complex.log (p : ℂ) = ((Real.log p : ℝ) : ℂ) := Complex.natCast_log.symm
  rw [logDeriv_apply, hder.deriv, norm_div, norm_mul, hw, hlog, Complex.norm_of_nonneg hL]
  have hdpos : 0 < ‖1 - (p : ℂ) ^ (-s)‖ := by linarith
  rw [div_le_iff₀ hdpos]
  have hxd : (p : ℝ) ^ (-s.re) ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hxd hL]

lemma re_negLogDeriv_le (q : ℕ) [NeZero q] (s : ℂ) (hs : 1 < s.re) :
    (negLD (1 : DirichletCharacter ℂ q) s).re ≤
      (-(deriv riemannZeta s / riemannZeta s)).re + Real.log q := by
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at hs
  have hfac : ∀ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s)) ≠ 0 ∧
      DifferentiableAt ℂ (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s ∧
      ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ ≤ Real.log p :=
    fun p hp => euler_factor_logDeriv_bound p (Nat.prime_of_mem_primeFactors hp) s hs
  have heq : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) =ᶠ[𝓝 s]
      fun z => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz
    exact DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q)
      (Set.mem_compl_singleton_iff.mp hz)
  have hPne : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp => (hfac p hp).1
  have hPd : DifferentiableAt ℂ (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s :=
    DifferentiableAt.fun_finsetProd fun p hp => (hfac p hp).2.1
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hζd : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hmul : logDeriv (fun z => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z) s =
      logDeriv (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s +
        logDeriv riemannZeta s :=
    logDeriv_mul (f := fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z)))
      (g := riemannZeta) s hPne hζ hPd hζd
  have hprod : logDeriv (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s =
      ∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s :=
    by
      have hfun : (∏ p ∈ q.primeFactors, fun z : ℂ => 1 - (p : ℂ) ^ (-z)) =
          fun z => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z)) := by
        funext z
        exact Finset.prod_apply (s := q.primeFactors)
          (g := fun (p : ℕ) (z : ℂ) => 1 - (p : ℂ) ^ (-z)) (a := z)
      rw [← hfun]
      exact logDeriv_prod (f := fun (p : ℕ) (z : ℂ) => 1 - (p : ℂ) ^ (-z))
        (fun p hp => (hfac p hp).1) (fun p hp => (hfac p hp).2.1)
  have hneg : negLD (1 : DirichletCharacter ℂ q) s =
      -(logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s) := rfl
  have hS : ‖∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ ≤
      Real.log q := by
    calc ‖∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖
        ≤ ∑ p ∈ q.primeFactors, ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ :=
          norm_sum_le _ _
      _ ≤ ∑ p ∈ q.primeFactors, Real.log p := Finset.sum_le_sum fun p hp => (hfac p hp).2.2
      _ = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
          rw [Real.log_prod]
          intro p hp
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
      _ ≤ Real.log q := by
          apply Real.log_le_log
          · exact Finset.prod_pos fun p hp => by
              exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
          · rw [← Nat.cast_prod]
            exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q))
              (Nat.prod_primeFactors_dvd q)
  have hre := RCLike.abs_re_le_norm
    (∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s)
  have hre' := neg_abs_le
    (∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s).re
  rw [hneg, (logDeriv_congr_nhds heq).eq_of_nhds, hmul, hprod, logDeriv_apply]
  simp only [Complex.neg_re, Complex.add_re]
  simp only [RCLike.re_to_complex] at hre
  linarith

end Formalism.ZeroFreeDirichlet
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.EulerFactorLogDerivBound =====

-- ===== clump member: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ZetaLogDerivLandauBound =====
-- clump-header: {"m": "Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ZetaLogDerivLandauBound", "h": "module\n\npublic import Mathlib.Analysis.CStarAlgebra.Classes\npublic import Mathlib.NumberTheory.LSeries.RiemannZeta\npublic import Formalism.ZeroFreeRegion.FinalZFR\npublic import Formalism.ZeroFreeRegion.LogDerivRegion\nimport Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaGrowth\nimport Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaInvBound\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Complex Filter Topology

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma re_one_div_nonneg {w : ℂ} (h : 0 ≤ w.re) : 0 ≤ (1 / w).re := by
  rw [one_div, Complex.inv_re]
  exact div_nonneg h (Complex.normSq_nonneg w)

private lemma re_natCast_div_nonneg (k : ℕ) {w : ℂ} (hw : 0 ≤ w.re) : 0 ≤ ((k : ℂ) / w).re := by
  have e : (k : ℂ) / w = ((k : ℝ) : ℂ) * (1 / w) := by push_cast; ring
  rw [e, Complex.re_ofReal_mul]
  exact mul_nonneg (Nat.cast_nonneg k) (re_one_div_nonneg hw)

private lemma re_ge_and_norm_zeta_le_of_near_eleven_tenths {t : ℝ} (ht : 2 < |t|) {z : ℂ}
    (hz : ‖z - (((11 / 10 : ℝ) : ℂ) + t * I)‖ ≤ 3 / 5) :
    1 / 2 ≤ z.re ∧ z ≠ 1 ∧ ‖riemannZeta z‖ ≤ 6 * (|t| + 2) := by
  have h1 := Complex.abs_re_le_norm (z - (((11 / 10 : ℝ) : ℂ) + t * I))
  have h2 := Complex.abs_im_le_norm (z - (((11 / 10 : ℝ) : ℂ) + t * I))
  have er : (z - (((11 / 10 : ℝ) : ℂ) + t * I)).re = z.re - 11 / 10 := by simp
  have ei : (z - (((11 / 10 : ℝ) : ℂ) + t * I)).im = z.im - t := by simp
  rw [er] at h1
  rw [ei] at h2
  have hre := abs_le.mp (h1.trans hz)
  have h2' := h2.trans hz
  have him1 : |t| - |z.im| ≤ |z.im - t| := by rw [abs_sub_comm]; exact abs_sub_abs_le_abs_sub t z.im
  have him2 : |z.im| - |t| ≤ |z.im - t| := abs_sub_abs_le_abs_sub z.im t
  have hzre : 1 / 2 ≤ z.re := by linarith [hre.1]
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at h2'
    linarith
  have hd : 1 ≤ ‖z - 1‖ := by
    have := Complex.abs_im_le_norm (z - 1)
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at this
    linarith
  have hzn : ‖z‖ ≤ |t| + 3 := by
    have := Complex.norm_le_abs_re_add_abs_im z
    have hr : |z.re| ≤ 17 / 10 := abs_le.mpr ⟨by linarith [hre.1], by linarith [hre.2]⟩
    linarith
  have hg := Formalism.ZF.growthBound z (by linarith) hz1
  have hA : 1 / ‖z - 1‖ ≤ 1 := (div_le_one (by linarith)).mpr hd
  have hB : 1 / z.re ≤ 2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have hC : ‖z‖ * (1 + 1 / z.re) ≤ (|t| + 3) * 3 :=
    mul_le_mul hzn (by linarith)
      (by have := one_div_pos.mpr (by linarith : (0 : ℝ) < z.re); linarith) (by positivity)
  refine ⟨hzre, hz1, ?_⟩
  linarith

lemma zeta_log_deriv_landau_bound (t σ : ℝ) (ht : 2 < |t|) (hσ : 1 < σ) (hσ' : σ ≤ 6 / 5) :
    (-(deriv riemannZeta ((σ:ℂ) + t * I) / riemannZeta ((σ:ℂ) + t * I))).re ≤
      840 * Real.log (|t| + 2) := by
  have hz0re : ((((11 / 10 : ℝ) : ℂ) + t * I)).re = 11 / 10 := by simp
  have hinv := Formalism.ZF.zetaInvBound_statement (((11 / 10 : ℝ) : ℂ) + t * I) (by rw [hz0re]; norm_num)
  have h1110 : (11 / 10 : ℝ) / (11 / 10 - 1) = 11 := by norm_num
  rw [hz0re, h1110] at hinv
  have hz0ne : riemannZeta (((11 / 10 : ℝ) : ℂ) + t * I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by rw [hz0re]; norm_num)
  have hpos : 0 < ‖riemannZeta (((11 / 10 : ℝ) : ℂ) + t * I)‖ := norm_pos_iff.mpr hz0ne
  have h11 : 1 ≤ ‖riemannZeta (((11 / 10 : ℝ) : ℂ) + t * I)‖ * 11 := by
    have := mul_le_mul_of_nonneg_left hinv hpos.le
    rwa [mul_inv_cancel₀ hpos.ne'] at this
  have hT : 4 ≤ |t| + 2 := by linarith
  have hM1 : (1 : ℝ) ≤ 66 * (|t| + 2) := by linarith
  obtain ⟨Z, m, hZ, -, -, hbound⟩ := Formalism.ZF.landauLocal riemannZeta (((11 / 10 : ℝ) : ℂ) + t * I) (3 / 5)
    (66 * (|t| + 2)) (by norm_num) hM1
    (fun z hz => (differentiableAt_riemannZeta
      (re_ge_and_norm_zeta_le_of_near_eleven_tenths ht (by rwa [Metric.mem_closedBall, dist_eq_norm] at hz)).2.1).differentiableWithinAt)
    hz0ne
    (fun z hz => by
      have hb := (re_ge_and_norm_zeta_le_of_near_eleven_tenths ht (by rwa [Metric.mem_closedBall, dist_eq_norm] at hz)).2.2
      nlinarith [mul_le_mul_of_nonneg_left h11 (by linarith : (0 : ℝ) ≤ 6 * (|t| + 2))])
  have hzmem : ((σ : ℂ) + t * I) ∈ Metric.closedBall (((11 / 10 : ℝ) : ℂ) + t * I) (3 / 5 / 6) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have e : (σ : ℂ) + t * I - (((11 / 10 : ℝ) : ℂ) + t * I) = ((σ - 11 / 10 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hzre : ((σ : ℂ) + t * I).re = σ := by simp
  have hzne : riemannZeta ((σ : ℂ) + t * I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by rw [hzre]; exact hσ)
  have hb := hbound _ hzmem hzne
  have hsum : 0 ≤ (∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) + t * I - ρ)).re := by
    rw [Complex.re_sum]
    apply Finset.sum_nonneg
    intro ρ hρ
    have hρ0 := ((hZ ρ).mp hρ).2
    have hρre : ρ.re ≤ 1 := by
      by_contra h
      push_neg at h
      exact riemannZeta_ne_zero_of_one_lt_re h hρ0
    apply re_natCast_div_nonneg
    simp
    linarith
  have hneg := _root_.Formalism.ZF.zfo_neg_re_le_norm (deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I) -
      ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) + t * I - ρ))
  have hsplit : (-(deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I))).re =
      (-(deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I) -
        ∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) + t * I - ρ))).re -
        (∑ ρ ∈ Z, (m ρ : ℂ) / ((σ : ℂ) + t * I - ρ)).re := by
    simp only [Complex.neg_re, Complex.sub_re]; ring
  have hlogM : Real.log (66 * (|t| + 2)) ≤ 7 * Real.log (|t| + 2) := by
    have h6 : (4 : ℝ) ^ 6 ≤ (|t| + 2) ^ 6 := pow_le_pow_left₀ (by norm_num) hT 6
    have hle : 66 * (|t| + 2) ≤ (|t| + 2) ^ 7 := by
      have e7 : (|t| + 2) ^ 7 = (|t| + 2) ^ 6 * (|t| + 2) := by ring
      rw [e7]; nlinarith
    calc Real.log (66 * (|t| + 2)) ≤ Real.log ((|t| + 2) ^ 7) := Real.log_le_log (by linarith) hle
      _ = 7 * Real.log (|t| + 2) := by rw [Real.log_pow]; norm_num
  have h72 : 72 * Real.log (66 * (|t| + 2)) / (3 / 5) = 120 * Real.log (66 * (|t| + 2)) := by ring
  rw [hsplit]
  linarith

lemma zeta_neg_log_deriv_re_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ t : ℝ, 1 < σ → σ ≤ 2 →
    (-(deriv riemannZeta ((σ:ℂ) + t * I) / riemannZeta ((σ:ℂ) + t * I))).re ≤
      (1 / ((σ : ℂ) - 1 + t * I)).re + K * Real.log (|t| + 2) := by
  obtain ⟨c, C, hc, hreg⟩ := Formalism.ZF.logDerivRegion
  obtain ⟨K₃, hK₃⟩ : ∃ k : ℝ, k = ∑' n, ‖LSeries.term (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))
      ((6 / 5 : ℝ) : ℂ) n‖ := ⟨_, rfl⟩
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨840 + |C| * Real.log 4 + |K₃|,
    add_nonneg (add_nonneg (by norm_num) (mul_nonneg (abs_nonneg _) hlog4)) (abs_nonneg _), ?_⟩
  intro σ t hσ hσ2
  have hre1 : 0 ≤ ((σ : ℂ) - 1 + t * I).re := by simp; linarith
  have hR := re_one_div_nonneg hre1
  have hL0 : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hC0 : 0 ≤ |C| * Real.log 4 * Real.log (|t| + 2) := mul_nonneg (mul_nonneg (abs_nonneg _) hlog4) hL0
  have hK30 : 0 ≤ |K₃| * Real.log (|t| + 2) := mul_nonneg (abs_nonneg _) hL0
  have h840 : 0 ≤ 840 * Real.log (|t| + 2) := mul_nonneg (by norm_num) hL0
  rcases le_or_gt |t| 2 with ht | ht
  ·
    have hs1 : ((σ : ℂ) + t * I) ≠ 1 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have him : ((σ : ℂ) + t * I).im = t := by simp
    have hsre : ((σ : ℂ) + t * I).re = σ := by simp
    have hLpos : 0 < Real.log (|t| + 2) := Real.log_pos (by linarith [abs_nonneg t])
    have hcond : 1 - c / Real.log (|((σ : ℂ) + t * I).im| + 2) ≤ ((σ : ℂ) + t * I).re := by
      rw [him, hsre]; have := div_nonneg hc.le hLpos.le; linarith
    have hb := hreg _ hs1 hcond
    rw [him] at hb
    have es : (σ : ℂ) + t * I - 1 = (σ : ℂ) - 1 + t * I := by ring
    rw [es] at hb
    have hneg := _root_.Formalism.ZF.zfo_neg_re_le_norm (deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I) +
      1 / ((σ : ℂ) - 1 + t * I))
    have hsplit : (-(deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I))).re =
        (1 / ((σ : ℂ) - 1 + t * I)).re + (-(deriv riemannZeta ((σ : ℂ) + t * I) /
          riemannZeta ((σ : ℂ) + t * I) + 1 / ((σ : ℂ) - 1 + t * I))).re := by
      simp only [Complex.neg_re, Complex.add_re]; ring
    have hL4 : Real.log (|t| + 2) ≤ Real.log 4 :=
      Real.log_le_log (by linarith [abs_nonneg t]) (by linarith)
    have hCL : C * Real.log (|t| + 2) ^ 2 ≤ |C| * Real.log 4 * Real.log (|t| + 2) := by
      have h1 : C * Real.log (|t| + 2) ^ 2 ≤ |C| * Real.log (|t| + 2) ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg _)
      have h2 : |C| * (Real.log (|t| + 2) * Real.log (|t| + 2)) ≤ |C| * (Real.log 4 * Real.log (|t| + 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL4 hL0) (abs_nonneg C)
      nlinarith
    rw [hsplit]
    nlinarith
  rcases le_or_gt σ (6 / 5) with hσ' | hσ'
  ·
    have := zeta_log_deriv_landau_bound t σ ht hσ hσ'
    nlinarith
  ·
    have hs1 : 1 < ((σ : ℂ) + t * I).re := by simp; linarith
    have hLs := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs1
    rw [neg_div] at hLs
    rw [← hLs]
    have hsum := ArithmeticFunction.LSeriesSummable_vonMangoldt hs1
    have hsum0 := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := ((6 / 5 : ℝ) : ℂ))
      (by rw [Complex.ofReal_re]; norm_num)
    have hbd : (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((σ : ℂ) + t * I)).re ≤ K₃ := by
      calc (LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((σ : ℂ) + t * I)).re
          ≤ ‖LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((σ : ℂ) + t * I)‖ :=
            Complex.re_le_norm _
        _ ≤ ∑' n, ‖LSeries.term (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((σ : ℂ) + t * I) n‖ :=
            norm_tsum_le_tsum_norm (summable_norm_iff.mpr hsum)
        _ ≤ ∑' n, ‖LSeries.term (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((6 / 5 : ℝ) : ℂ) n‖ :=
            Summable.tsum_le_tsum (fun n => LSeries.norm_term_le_of_re_le_re _ (by simp; linarith) n)
              (summable_norm_iff.mpr hsum) (summable_norm_iff.mpr hsum0)
        _ = K₃ := hK₃.symm
    have hL1 : 1 ≤ Real.log (|t| + 2) := by
      rw [Real.le_log_iff_exp_le (by linarith [abs_nonneg t])]
      have := Real.exp_one_lt_d9; norm_num at this; linarith
    have hK3 : K₃ ≤ |K₃| * Real.log (|t| + 2) := by
      have := mul_le_mul_of_nonneg_left hL1 (abs_nonneg K₃)
      linarith [le_abs_self K₃]
    nlinarith

end Formalism.ZeroFreeDirichlet
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ZetaLogDerivLandauBound =====

-- ===== clump member: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.TrivLogDeriv =====
-- clump-header: {"m": "Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.TrivLogDeriv", "h": "module\n\npublic import Formalism.LandauZeroFreeBounds.NoZeroComplexOf\npublic import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.EulerFactorLogDerivBound\npublic import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ZetaLogDerivLandauBound\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem trivial_log_deriv_bound : TrivLogDeriv := by
  obtain ⟨K, hK0, hK⟩ := zeta_neg_log_deriv_re_bound
  refine ⟨K + 1, fun q _ σ t hσ hσ2 => ?_⟩
  have hs : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  have h1 := re_negLogDeriv_le q ((σ : ℂ) + t * I) hs
  have h2 := hK σ t hσ hσ2
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hT : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hlog : Real.log ((q : ℝ) * (|t| + 2)) = Real.log q + Real.log (|t| + 2) :=
    Real.log_mul (by linarith : (0 : ℝ) < q).ne' (by linarith [abs_nonneg t] : (0 : ℝ) < |t| + 2).ne'
  rw [hlog]
  nlinarith [mul_nonneg hK0 hlq]

end Formalism.ZeroFreeDirichlet
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.TrivLogDeriv =====

-- ===== clump member: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.TwoRealOf =====
-- clump-header: {"m": "Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.TwoRealOf", "h": "module\n\npublic import Formalism.LandauZeroFreeBounds.NoZeroComplexOf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\npublic import Mathlib.NumberTheory.LSeries.Nonvanishing\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma re_one_div_sub_zero_pos_bis {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ)
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (σ : ℝ) (hσ : 1 < σ) :
    0 < (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re := by
  have hre : ρ.re < 1 := by
    by_contra h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (not_lt.mp h) hρ
  have hw : ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ).re = σ - ρ.re := by simp
  have hwpos : 0 < ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ).re := by rw [hw]; linarith
  rw [one_div, Complex.inv_re]
  apply div_pos hwpos
  rw [Complex.normSq_pos]
  intro h0
  rw [h0] at hwpos
  simp at hwpos

lemma sum_re_one_div_sub_zero_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (Z : Finset ℂ)
    (m : ℂ → ℕ) (hZ : ∀ ρ ∈ Z, DirichletCharacter.LFunction χ ρ = 0) (σ : ℝ) (hσ : 1 < σ) :
    0 ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re := by
  apply Finset.sum_nonneg
  intro ρ hρ
  exact mul_nonneg (Nat.cast_nonneg _) (re_one_div_sub_zero_pos_bis χ hχ ρ (hZ ρ hρ) σ hσ).le

lemma re_negLogDeriv_le_of_real_zero (C : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (Z : Finset ℂ) (m : ℂ → ℕ)
    (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔
        (ρ ∈ Metric.closedBall ((11 / 10 : ℂ) + ((0 : ℝ) : ℂ) * I) (1 / 5) ∧
          DirichletCharacter.LFunction χ ρ = 0))
    (hm1 : ∀ ρ ∈ Z, 1 ≤ m ρ)
    (β σ : ℝ) (hσ : 1 < σ) (hβσ : β < σ) (hβ9 : 9 / 10 ≤ β) (hβ1 : β < 1)
    (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0)
    (hb : (negLD χ ((σ : ℂ) + ((0 : ℝ) : ℂ) * I)).re ≤
      C * Real.log ((q : ℝ) * (|(0 : ℝ)| + 2)) -
        ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re) :
    (negLD χ (σ : ℂ)).re ≤ C * Real.log ((q : ℝ) * 2) - 1 / (σ - β) := by
  have hs0 : ((σ : ℂ) + ((0 : ℝ) : ℂ) * I) = (σ : ℂ) := by simp
  have hl : (negLD χ ((σ : ℂ) + ((0 : ℝ) : ℂ) * I)).re = (negLD χ (σ : ℂ)).re := by
    rw [hs0]
  have h02 : |(0 : ℝ)| + 2 = 2 := by norm_num
  rw [h02] at hb
  have hβZ : (β : ℂ) ∈ Z := by
    rw [hZ]
    refine ⟨?_, hzero⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h' : (β : ℂ) - ((11 / 10 : ℂ) + ((0 : ℝ) : ℂ) * I) = ((β - 11 / 10 : ℝ) : ℂ) := by
      push_cast; ring
    rw [h', Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hterm : (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - (β : ℂ))).re = 1 / (σ - β) := by
    have h' : (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - (β : ℂ))) = ((1 / (σ - β) : ℝ) : ℂ) := by
      push_cast; ring
    rw [h', Complex.ofReal_re]
  have hrest : 0 ≤ ∑ ρ ∈ Z.erase (β : ℂ), (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re := by
    apply Finset.sum_nonneg
    intro ρ hρ
    have hρZ := ((hZ ρ).1 (Finset.mem_of_mem_erase hρ)).2
    exact mul_nonneg (Nat.cast_nonneg _) (re_one_div_sub_zero_pos_bis χ hχ ρ hρZ σ hσ).le
  have hsplit : (m (β : ℂ) : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - (β : ℂ))).re +
      ∑ ρ ∈ Z.erase (β : ℂ), (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re =
      ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re :=
    Finset.add_sum_erase Z (fun ρ => (m ρ : ℝ) * (1 / ((σ : ℂ) + ((0 : ℝ) : ℂ) * I - ρ)).re) hβZ
  rw [hterm] at hsplit
  have hpos : 0 < 1 / (σ - β) := one_div_pos.mpr (sub_pos.mpr hβσ)
  have hm : (1 : ℝ) ≤ (m (β : ℂ) : ℝ) := by exact_mod_cast hm1 _ hβZ
  have hbig : 1 / (σ - β) ≤ (m (β : ℂ) : ℝ) * (1 / (σ - β)) := by nlinarith
  linarith

theorem twoRealCharNoCommonZeroOfBounds : TwoRealOf := by
  intro hZS hLD hPos
  obtain ⟨C, hC⟩ := hZS
  obtain ⟨C', hC'0, hC'⟩ := hLD
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 3 * |C| + 2 * C' + 1 := ⟨_, rfl⟩
  have hA1 : 1 ≤ A := by have := abs_nonneg C; linarith
  have hA0 : 0 < A := by linarith
  refine ⟨1 / (20 * A), one_div_pos.mpr (mul_pos (by norm_num) hA0), ?_⟩
  intro q hq0 χ₁ χ₂ h₁ h₂ h₁1 h₂1 h12 β₁ β₂ hr₁ hr₂
  by_contra hcon
  obtain ⟨hz₁', hz₂'⟩ := not_or.mp hcon
  have hz₁ := not_not.mp hz₁'
  have hz₂ := not_not.mp hz₂'
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log ((q : ℝ) * 2) := ⟨_, rfl⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hL2 : Real.log 2 ≤ L := by
    rw [hL]; exact Real.log_le_log (by norm_num) (by linarith)
  have hLhalf : 1 / 2 < L := by have := Real.log_two_gt_d9; linarith
  have hL0 : 0 < L := by linarith
  have hAL0 : 0 < 20 * A * L := mul_pos (mul_pos (by norm_num) hA0) hL0
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = 1 / (20 * A * L) := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [he]; exact one_div_pos.mpr hAL0
  have hE : 20 * A * L * e = 1 := by rw [he]; exact mul_one_div_cancel hAL0.ne'
  have hAL : A * L = 3 * |C| * L + 2 * C' * L + L := by rw [hA]; ring
  have hAL10 : 10 ≤ 20 * A * L := by nlinarith
  have he10 : e ≤ 1 / 10 := by
    have := mul_le_mul_of_nonneg_left hAL10 he0.le
    linarith
  have hreg : ∀ β : ℝ, InRegion (1 / (20 * A)) q (β : ℂ) → 1 - e ≤ β := by
    intro β hr
    simp only [InRegion, Complex.ofReal_im, Complex.ofReal_re, abs_zero, zero_add] at hr
    have : 1 / (20 * A) / Real.log ((q : ℝ) * 2) = e := by rw [he, hL, div_div]
    linarith
  have hσ : (1 : ℝ) < 1 + 2 * e := by linarith
  have hσ6 : 1 + 2 * e ≤ 6 / 5 := by linarith
  have hβlt : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ β : ℝ,
      DirichletCharacter.LFunction χ (β : ℂ) = 0 → β < 1 := by
    intro χ hχ β hz
    by_contra h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using not_lt.mp h) hz
  have hbound : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ β : ℝ,
      InRegion (1 / (20 * A)) q (β : ℂ) → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
      (negLD χ ((1 + 2 * e : ℝ) : ℂ)).re ≤ C * L - 20 * A * L / 3 := by
    intro χ hχ β hr hz
    have hb1 := hβlt χ hχ β hz
    have hb0 := hreg β hr
    obtain ⟨Z, m, hZ, hm, -, hb⟩ := hC q χ hχ 0
    have key := re_negLogDeriv_le_of_real_zero C χ hχ Z m hZ hm β (1 + 2 * e) hσ
      (by linarith) (by linarith) hb1 hz (hb (1 + 2 * e) hσ hσ6)
    rw [← hL] at key
    have h3 : 1 / (3 * e) = 20 * A * L / 3 := by
      rw [div_eq_iff (mul_pos (by norm_num) he0).ne']
      linear_combination -hE
    have hinv : 1 / (3 * e) ≤ 1 / (1 + 2 * e - β) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith
  have h0b : (negLD (1 : DirichletCharacter ℂ q) ((1 + 2 * e : ℝ) : ℂ)).re ≤ 10 * A * L + C' := by
    have h := hC' q 1 ((1 + 2 * e : ℝ) : ℂ) (by rw [Complex.ofReal_re]; exact hσ)
    rw [Complex.ofReal_re] at h
    have h2 : 1 / (1 + 2 * e - 1) = 10 * A * L := by
      rw [div_eq_iff (show (0 : ℝ) < 1 + 2 * e - 1 by linarith).ne']
      linear_combination -hE
    rw [h2] at h
    have := Complex.re_le_norm (negLD (1 : DirichletCharacter ℂ q) ((1 + 2 * e : ℝ) : ℂ))
    linarith
  have h12ne : χ₁ * χ₂ ≠ 1 := by
    intro h
    apply h12
    calc χ₁ = χ₁ * χ₂ ^ 2 := by rw [h₂, mul_one]
      _ = χ₁ * χ₂ * χ₂ := by rw [pow_two, mul_assoc]
      _ = χ₂ := by rw [h, one_mul]
  have h12b : (negLD (χ₁ * χ₂) ((1 + 2 * e : ℝ) : ℂ)).re ≤ C * L := by
    obtain ⟨Z, m, hZ, -, -, hb⟩ := hC q (χ₁ * χ₂) h12ne 0
    have hb' := hb (1 + 2 * e) hσ hσ6
    have hs := sum_re_one_div_sub_zero_nonneg (χ₁ * χ₂) h12ne Z m
      (fun ρ hρ => ((hZ ρ).1 hρ).2) (1 + 2 * e) hσ
    have hs0 : (((1 + 2 * e : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) = ((1 + 2 * e : ℝ) : ℂ) := by simp
    have hl : (negLD (χ₁ * χ₂) (((1 + 2 * e : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I)).re =
        (negLD (χ₁ * χ₂) ((1 + 2 * e : ℝ) : ℂ)).re := by rw [hs0]
    have h02 : |(0 : ℝ)| + 2 = 2 := by norm_num
    rw [h02, ← hL] at hb'
    linarith
  have hpos := (hPos q (1 + 2 * e) hσ).2.2 χ₁ χ₂ h₁ h₂
  have k1 := hbound χ₁ h₁1 β₁ hr₁ hz₁
  have k2 := hbound χ₂ h₂1 β₂ hr₂ hz₂
  have hCL : C * L ≤ |C| * L := mul_le_mul_of_nonneg_right (le_abs_self C) hL0.le
  have hC'L : C' * (1 / 2) ≤ C' * L := mul_le_mul_of_nonneg_left hLhalf.le hC'0
  have hCL0 : 0 ≤ |C| * L := mul_nonneg (abs_nonneg C) hL0.le
  have hC'L0 : 0 ≤ C' * L := mul_nonneg hC'0 hL0.le
  linarith

end Formalism.ZeroFreeDirichlet
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.TwoRealOf =====

-- ===== clump member: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ZFRDirichletOf =====
-- clump-header: {"m": "Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ZFRDirichletOf", "h": "module\n\npublic import Formalism.LandauZeroFreeBounds.NoZeroComplexOf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma one_le_natCast (q : ℕ) [NeZero q] : (1 : ℝ) ≤ q := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)

lemma log_two_le_log_mul_abs_add_two (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log 2 ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
  have hq := one_le_natCast q
  apply Real.log_le_log (by norm_num)
  nlinarith [abs_nonneg t]

lemma log_mul_abs_add_two_pos (q : ℕ) [NeZero q] (t : ℝ) :
    0 < Real.log ((q : ℝ) * (|t| + 2)) := lt_of_lt_of_le (Real.log_pos (by norm_num)) (log_two_le_log_mul_abs_add_two q t)

lemma inRegion_mono' {c c' : ℝ} {q : ℕ} [NeZero q] {s : ℂ} (h : c ≤ c') (hs : InRegion c q s) :
    InRegion c' q s := by
  unfold InRegion at *
  have hL := log_mul_abs_add_two_pos q s.im
  have := div_le_div_of_nonneg_right h hL.le
  linarith

lemma re_pos_of_inRegion {c : ℝ} {q : ℕ} [NeZero q] {s : ℂ} (hc : c ≤ 1 / 2) (hs : InRegion c q s) :
    0 < s.re := by
  unfold InRegion at hs
  have hL := log_two_le_log_mul_abs_add_two q s.im
  have hLpos := log_mul_abs_add_two_pos q s.im
  have h2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 := div_le_div_of_nonneg_right hc hLpos.le
  have h2 : (1 / 2 : ℝ) / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ (1 / 2) / Real.log 2 :=
    div_le_div_of_nonneg_left (by norm_num) h2pos hL
  have h3 : (1 / 2 : ℝ) / Real.log 2 < 1 := by
    rw [div_lt_one h2pos]; linarith [Real.log_two_gt_d9]
  linarith

lemma one_sub_div_log_le_re {c cz : ℝ} {q : ℕ} [NeZero q] {s : ℂ} (hcz : 0 < cz) (h : c ≤ cz)
    (hs : InRegion c q s) : 1 - cz / Real.log (|s.im| + 2) ≤ s.re := by
  unfold InRegion at hs
  have hq := one_le_natCast q
  have hT : (2 : ℝ) ≤ |s.im| + 2 := by linarith [abs_nonneg s.im]
  have hlogT : 0 < Real.log (|s.im| + 2) := Real.log_pos (by linarith)
  have hle : Real.log (|s.im| + 2) ≤ Real.log ((q : ℝ) * (|s.im| + 2)) :=
    Real.log_le_log (by linarith) (by nlinarith)
  have hLpos := log_mul_abs_add_two_pos q s.im
  have h1 := div_le_div_of_nonneg_right h hLpos.le
  have h2 := div_le_div_of_nonneg_left hcz.le hlogT hle
  linarith

theorem zeroFreeRegionExceptionalZeroOfBounds : ZFRDirichletOf := by
  intro hZ hT hN hL hS h2
  obtain ⟨cz, hcz, hZ⟩ := hZ
  obtain ⟨cN, hcN, hN⟩ := hN
  obtain ⟨δ, cS, hδ, hcS, hS⟩ := hS
  obtain ⟨cL, hcL, hL⟩ := hL δ hδ
  obtain ⟨c2, hc2, h2⟩ := h2
  set c := min (min (min cz cN) (min cL cS)) (min c2 (1 / 2)) with hc
  have hc0 : 0 < c := lt_min (lt_min (lt_min hcz hcN) (lt_min hcL hcS)) (lt_min hc2 (by norm_num))
  have hccz : c ≤ cz := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hccN : c ≤ cN := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hccL : c ≤ cL := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hccS : c ≤ cS := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcc2 : c ≤ c2 := (min_le_right _ _).trans (min_le_left _ _)
  have hc12 : c ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, hc0, ?_⟩
  intro q _ χ s hs hz

  have key : ∀ (χ : DirichletCharacter ℂ q) (s : ℂ), InRegion c q s → IsLZero χ s →
      χ ^ 2 = 1 ∧ χ ≠ 1 ∧ |s.im| < δ / Real.log ((q : ℝ) * (|s.im| + 2)) := by
    intro χ s hs hz
    obtain ⟨hne, h0⟩ := hz
    have hχ1 : χ ≠ 1 := by
      rintro rfl
      have hs1 : s ≠ 1 := hne.resolve_left (fun h => h rfl)
      have hre := re_pos_of_inRegion hc12 hs
      exact hZ s hs1 (one_sub_div_log_le_re hcz hccz hs) (hT q s hre hs1 h0)
    have hsq : χ ^ 2 = 1 := by
      by_contra hsq
      exact hN q χ s hsq (inRegion_mono' hccN hs) h0
    refine ⟨hsq, hχ1, ?_⟩
    by_contra hlt
    push_neg at hlt
    exact hL q χ s hsq hχ1 hlt (inRegion_mono' hccL hs) h0
  obtain ⟨hsq, hχ1, hsm⟩ := key χ s hs hz
  obtain ⟨him, hder, -⟩ := hS q χ hsq hχ1 s s hsm hsm (inRegion_mono' hccS hs)
    (inRegion_mono' hccS hs) hz.2 hz.2
  refine ⟨hsq, hχ1, him, hder, ?_⟩
  intro χ' s' hs' hz'
  obtain ⟨hsq', hχ1', hsm'⟩ := key χ' s' hs' hz'
  have him' := (hS q χ' hsq' hχ1' s' s' hsm' hsm' (inRegion_mono' hccS hs')
    (inRegion_mono' hccS hs') hz'.2 hz'.2).1
  have hχeq : χ' = χ := by
    by_contra hne
    have es : ((s.re : ℝ) : ℂ) = s := Complex.ext (by simp) (by simp [him])
    have es' : ((s'.re : ℝ) : ℂ) = s' := Complex.ext (by simp) (by simp [him'])
    have r1 : InRegion c2 q ((s.re : ℝ) : ℂ) := by rw [es]; exact inRegion_mono' hcc2 hs
    have r2 : InRegion c2 q ((s'.re : ℝ) : ℂ) := by rw [es']; exact inRegion_mono' hcc2 hs'
    rcases h2 q χ χ' hsq hsq' hχ1 hχ1' (Ne.symm hne) s.re s'.re r1 r2 with h | h
    · exact h (by rw [es]; exact hz.2)
    · exact h (by rw [es']; exact hz'.2)
  refine ⟨hχeq, ?_⟩
  rw [hχeq] at hz'
  exact (hS q χ hsq hχ1 s s' hsm hsm' (inRegion_mono' hccS hs) (inRegion_mono' hccS hs')
    hz.2 hz'.2).2.2

end Formalism.ZeroFreeDirichlet
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ZFRDirichletOf =====

-- ===== clump member: Formalism.LandauZeroFreeBounds.NoZeroComplex =====
-- clump-header: {"m": "Formalism.LandauZeroFreeBounds.NoZeroComplex", "h": "module\n\npublic import Formalism.LandauZeroFreeBounds.NoZeroComplexOf\npublic import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LGrowth\npublic import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LRight\npublic import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LocalZeroExpansionWithMultiplicity\npublic import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LocalZerosOf\npublic import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.NoZeroComplexOf\npublic import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Positivity\npublic import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.RealLargeTOf\npublic import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.RealSmallTOf\npublic import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.TrivLogDeriv\npublic import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.TrivReal\npublic import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.TwoRealOf\npublic import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ZFRDirichletOf\nimport Formalism.ZeroFreeRegion.FinalZFR\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

namespace Formalism.ZeroFreeDirichlet

theorem localZeros : LocalZeros :=
  localZeroSumBoundOfBounds localZeroExpansionWithMultiplicity lfunction_polynomial_growth inverseBound

theorem noZeroComplex : NoZeroComplex :=
  zeroFreeNonRealCharOfBounds localZeros l_log_deriv_right negLogDerivPositivity

theorem realLargeT : RealLargeT :=
  realCharZeroFreeLargeHeightOfBounds localZeros l_log_deriv_right negLogDerivPositivity trivial_log_deriv_bound

theorem realSmallT : RealSmallT :=
  realCharZeroSmallHeightOfBounds localZeros l_log_deriv_right negLogDerivPositivity realCharConj

theorem twoReal : TwoReal :=
  twoRealCharNoCommonZeroOfBounds localZeros l_log_deriv_right negLogDerivPositivity

theorem zFRDirichlet : ZFRDirichlet :=
  zeroFreeRegionExceptionalZeroOfBounds Formalism.ZF.zeroFreeRegion trivialCharZerosOfZeta noZeroComplex realLargeT realSmallT twoReal

end Formalism.ZeroFreeDirichlet
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LandauZeroFreeBounds.NoZeroComplex =====
