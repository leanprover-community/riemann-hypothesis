module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula
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

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

theorem UpperTheory.Esk.pf_KapSum : UpperTheory.Esk.Pack → UpperTheory.Esk.Mult → UpperTheory.Esk.KapInt → UpperTheory.Esk.KapSum := by
  intro hPack hMult hKap F I Gf _ _ _ D hD k hk c₀ hc₀
  obtain ⟨C₁, hC₁⟩ := hPack F I Gf D hD
  obtain ⟨C₃, A₃, hK⟩ := hKap I k hk
  obtain ⟨C₂, hC₂⟩ := hMult F I Gf D hD (1 / 16) c₀ (by norm_num) hc₀
  refine ⟨(C₁ : ℝ) * A₃ * max C₂ 0 * C₃, ?_⟩
  intro y s hs hy ω' z
  obtain ⟨hfin, hcard⟩ := hC₂ y s hs hy
  obtain ⟨hmeas, hint, -, hnear⟩ := hK z
  have hpos : 0 ≤ 1 + D.HtY s y := by linarith
  have key : ∀ n : ℕ, (n : ℝ) ≤ C₂ * (1 + D.HtY s y) →
      (n : ℝ≥0∞) ≤ ENNReal.ofReal (max C₂ 0 * (1 + D.HtY s y)) := by
    intro n hn
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos))
  have hA : ∀ w w' : D.Xs, Near (1 / 2) w w' →
      ENNReal.ofReal (Kap k z w) ≤ (A₃ : ℝ≥0∞) * ENNReal.ofReal (Kap k z w') := by
    intro w w' hww
    calc ENNReal.ofReal (Kap k z w) ≤ ENNReal.ofReal (A₃ * Kap k z w') :=
          ENNReal.ofReal_le_ofReal (hnear w w' hww).1
      _ = (A₃ : ℝ≥0∞) * ENNReal.ofReal (Kap k z w') := by
          rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
  have hpack := hC₁ y ω' (fun w => ENNReal.ofReal (Kap k z w)) A₃
    (ENNReal.measurable_ofReal.comp hmeas) hA hfin
  refine hpack.trans ((mul_le_mul' (mul_le_mul' le_rfl (key _ hcard)) hint).trans (le_of_eq ?_))
  rw [show (C₁ : ℝ) * A₃ * max C₂ 0 * C₃ * (1 + D.HtY s y)
      = ((C₁ * A₃ * C₃ : ℝ≥0) : ℝ) * (max C₂ 0 * (1 + D.HtY s y)) by push_cast; ring,
    ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
  push_cast
  ring
