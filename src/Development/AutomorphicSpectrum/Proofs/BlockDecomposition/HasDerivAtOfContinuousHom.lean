module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

namespace GlobalTheory.CompanionTheory.CharDeriv

theorem hasDerivAt_of_continuous_hom :
    ∀ (χ : ℝ → ℂ), Continuous χ → χ 0 = 1 → (∀ s t, χ (s + t) = χ s * χ t) →
      ∃ c : ℂ, ∀ t, HasDerivAt χ (c * χ t) t := by
  intro χ hc h0 hadd
  have hP : ∀ x : ℝ, HasDerivAt (fun y : ℝ => ∫ s in (0 : ℝ)..y, χ s) (χ x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  obtain ⟨δ, hI⟩ : ∃ δ : ℝ, (∫ s in (0 : ℝ)..δ, χ s) ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : (fun y : ℝ => ∫ s in (0 : ℝ)..y, χ s) = fun _ => (0 : ℂ) := funext h
    have h1 := hP 0
    rw [hz] at h1
    have h2 := h1.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    rw [h0] at h2
    exact one_ne_zero h2
  have key : ∀ t : ℝ, χ t = ((∫ s in (0 : ℝ)..(t + δ), χ s) - ∫ s in (0 : ℝ)..t, χ s) /
      (∫ s in (0 : ℝ)..δ, χ s) := by
    intro t
    rw [eq_div_iff hI, ← intervalIntegral.integral_const_mul]
    have h1 : (∫ s in (0 : ℝ)..δ, χ t * χ s) = ∫ u in t..(t + δ), χ u := by
      have h2 := intervalIntegral.integral_comp_add_left (a := 0) (b := δ) (fun u => χ u) t
      rw [add_zero] at h2
      rw [← h2]
      exact intervalIntegral.integral_congr fun s _ => (hadd t s).symm
    rw [h1]
    exact (intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)).symm
  refine ⟨(χ δ - 1) / (∫ s in (0 : ℝ)..δ, χ s), fun t => ?_⟩
  have hD : HasDerivAt (fun y : ℝ => ((∫ s in (0 : ℝ)..(y + δ), χ s) - ∫ s in (0 : ℝ)..y, χ s) /
      (∫ s in (0 : ℝ)..δ, χ s)) ((χ (t + δ) - χ t) / (∫ s in (0 : ℝ)..δ, χ s)) t := by
    have h3 : HasDerivAt (fun y : ℝ => ∫ s in (0 : ℝ)..(y + δ), χ s) (χ (t + δ)) t := by
      simpa using (hP (t + δ)).comp_add_const t δ
    exact (h3.sub (hP t)).div_const _
  have hval : (χ δ - 1) / (∫ s in (0 : ℝ)..δ, χ s) * χ t =
      (χ (t + δ) - χ t) / (∫ s in (0 : ℝ)..δ, χ s) := by
    rw [hadd t δ]
    ring
  rw [hval]
  exact hD.congr_of_eventuallyEq (Filter.Eventually.of_forall key)

end GlobalTheory.CompanionTheory.CharDeriv
