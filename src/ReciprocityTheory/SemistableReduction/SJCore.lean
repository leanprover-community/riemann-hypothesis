module

public import ReciprocityTheory.SemistableReduction.SJCoreA
public import ReciprocityTheory.SemistableReduction.SJCoreB
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.SemistableReduction.SJCoreD

@[expose] public section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Set Real

theorem gaussLogC_div {a : ℝ} (ha : 0 < a) :
    gaussLogC a / gaussOneC = log a + radK 1 / radJ 1 := by
  have hdim : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  have h1 := integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => exp (-r ^ 2))
  have h2 := integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => log (a * r) * exp (-r ^ 2))
  rw [hdim] at h1 h2
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h1 h2
  set C : ℝ := (volume : Measure ℂ).real (Metric.ball 0 1) with hCdef
  have hC : 0 < C :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume (0 : ℂ) one_pos).ne' measure_ball_lt_top.ne
  have hG : gaussOneC = 2 * C * radJ 1 := by
    unfold gaussOneC radJ
    rw [h1]
    simp only [pow_one]
    ring
  have hsplit : ∫ y in Ioi (0 : ℝ), y * (log (a * y) * exp (-y ^ 2)) =
      log a * radJ 1 + radK 1 := by
    have heq : EqOn (fun y : ℝ => y * (log (a * y) * exp (-y ^ 2)))
        (fun y : ℝ => log a * (y ^ 1 * exp (-y ^ 2)) + y ^ 1 * log y * exp (-y ^ 2)) (Ioi 0) := by
      intro y hy
      simp only
      rw [log_mul ha.ne' (ne_of_gt hy)]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi heq,
      integral_add ((integrableOn_radJ 1).const_mul (log a)) (integrableOn_radK le_rfl),
      integral_const_mul]
    rfl
  have hL : gaussLogC a = 2 * C * (log a * radJ 1 + radK 1) := by
    unfold gaussLogC
    rw [h2, hsplit]
    ring
  have hM := radJ_pos 1
  rw [hL, hG]
  field_simp

theorem sjCore_holds : SphereLinLogStatement := by
  intro n c hc
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (Subsingleton.elim c 0) hc
    · exact h
  obtain ⟨hi, he⟩ := polar_mean hn c hc
  refine ⟨hi, ?_⟩
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have h2 : 2 * n - 1 = 2 * (n - 1) + 1 := by omega
  rw [he, gaussLogC_div hcn, h2, radRatio_odd]
  ring

end ReciprocityTheory.MultiplicativeHeights
