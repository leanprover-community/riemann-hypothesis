module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.VanishAtSStatementPf
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
open scoped ContDiff

namespace GlobalTheory

theorem holo_vanish_of_critical_integrable : ∀ {n : ℕ}, 0 < n → ∀ (u : V n → ℂ) (ρ : ℝ), 0 < ρ → DifferentiableOn ℂ u (Metric.ball 0 ρ) → ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (‖u z‖ ^ 2 * ‖z‖ ^ (-(2 * (n : ℝ)))) < ⊤ → u 0 = 0 := by
  intro n hn u ρ hρ hu hint
  by_contra hne
  have hb : Metric.ball (0 : V n) ρ ∈ nhds (0 : V n) := Metric.ball_mem_nhds 0 hρ
  set a := ‖u 0‖ with ha
  have ha0 : 0 < a := norm_pos_iff.mpr hne
  have hc : ContinuousAt u 0 := hu.continuousOn.continuousAt hb
  have ev1 : ∀ᶠ z in nhds (0 : V n), a / 2 < ‖u z‖ :=
    hc.norm.eventually (Ioi_mem_nhds (by show a / 2 < a; linarith))
  obtain ⟨δ0, hδ0, hall⟩ := Metric.eventually_nhds_iff.mp (ev1.and (Filter.eventually_of_mem hb fun z hz => hz))
  set δ := min δ0 ρ with hδ
  have hδpos : 0 < δ := lt_min hδ0 hρ
  have hsub : Metric.ball (0 : V n) δ ⊆ Metric.ball (0 : V n) ρ := Metric.ball_subset_ball (min_le_right _ _)
  have hpt : ∀ z ∈ Metric.ball (0 : V n) δ,
      ENNReal.ofReal ((a / 2) ^ 2) * ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))) ≤
        ENNReal.ofReal (‖u z‖ ^ 2 * ‖z‖ ^ (-(2 * (n : ℝ)))) := by
    intro z hz
    have hz0 : dist z 0 < δ0 := by
      rw [Metric.mem_ball] at hz; exact lt_of_lt_of_le hz (min_le_left _ _)
    have h1 := (hall hz0).1
    rw [← ENNReal.ofReal_mul (by positivity), neg_mul]
    refine ENNReal.ofReal_le_ofReal ?_
    have hr : 0 ≤ ‖z‖ ^ (-(2 * (n : ℝ))) := Real.rpow_nonneg (norm_nonneg _) _
    have h2 : (a / 2) ^ 2 ≤ ‖u z‖ ^ 2 := pow_le_pow_left₀ (by positivity) h1.le 2
    exact mul_le_mul_of_nonneg_right h2 hr
  have hlow : ENNReal.ofReal ((a / 2) ^ 2) * ∫⁻ z in Metric.ball (0 : V n) δ, ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ)))
      ≤ ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (‖u z‖ ^ 2 * ‖z‖ ^ (-(2 * (n : ℝ)))) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ∫⁻ z in Metric.ball (0 : V n) δ, ENNReal.ofReal ((a / 2) ^ 2) * ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ)))
        ≤ ∫⁻ z in Metric.ball (0 : V n) δ, ENNReal.ofReal (‖u z‖ ^ 2 * ‖z‖ ^ (-(2 * (n : ℝ)))) :=
          setLIntegral_mono' Metric.isOpen_ball.measurableSet hpt
      _ ≤ _ := lintegral_mono_set hsub
  rw [ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf.crit_div hn hδpos,
    ENNReal.mul_top (by simp [ENNReal.ofReal_eq_zero, not_le]; positivity)] at hlow
  exact absurd (lt_of_le_of_lt hlow hint) (lt_irrefl _)

end GlobalTheory
