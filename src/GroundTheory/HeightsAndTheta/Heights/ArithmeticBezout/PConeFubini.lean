module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
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
import Mathlib.MeasureTheory.Measure.RegularityCompacts
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

noncomputable section

theorem ConeFubini.proof (h1 : BallVolume.Statement) : ConeFubini.Statement := by
  intro n h μ _ F c M hF hy
  obtain ⟨hpos, hfin⟩ := h1 n h
  have : IsFiniteMeasure (volume.restrict (ballH h)) := isFiniteMeasure_restrict.2 hfin.ne
  have hsm : StronglyMeasurable (Function.uncurry F) := hF.stronglyMeasurable

  have hint : Integrable (Function.uncurry F) ((volume.restrict (ballH h)).prod μ) := by
    rw [integrable_prod_iff' hsm.aestronglyMeasurable]
    refine ⟨hy.mono fun y hy => hy.1, ?_⟩
    refine Integrable.of_bound ?_ M ?_
    · exact (hsm.norm.integral_prod_left' (μ := volume.restrict (ballH h))).aestronglyMeasurable
    · filter_upwards [hy] with y hy
      have e : ∀ x, ‖Function.uncurry F (x, y)‖ = |F x y| := fun x => Real.norm_eq_abs _
      simp only [e]
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
      exact hy.2.1
  refine ⟨hint.integral_prod_left, ?_⟩
  have hvol : (volume (ballH h)).toReal ≠ 0 := (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  have hreal : volume.real (ballH h) = (volume (ballH h)).toReal := rfl

  have hin : ∀ᵐ y ∂μ, ∫ v in ballH h, F v y = c * (volume (ballH h)).toReal := by
    filter_upwards [hy] with y hy
    have e := hy.2.2
    rw [setAverage_eq, hreal, smul_eq_mul] at e
    field_simp at e ⊢
    linarith
  have hswap := integral_integral_swap hint
  rw [setAverage_eq, hreal, smul_eq_mul, hswap, integral_congr_ae hin, integral_const, smul_eq_mul]
  simp only [measureReal_def]
  field_simp
