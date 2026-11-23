module

public import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
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
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

noncomputable section

open MvPolynomial
open scoped ContDiff

namespace GlobalTheory.PsCo.Pc1

theorem stProfile_holds : StProfile := by
  intro N
  induction N with
  | zero =>
    refine ⟨fun x => expNegInvGlue (1 - x), ?_, ?_, ?_, ?_⟩
    · exact expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)
    · intro x hx
      exact expNegInvGlue.zero_of_nonpos (by linarith)
    · intro x
      simpa using expNegInvGlue.nonneg _
    · simpa using expNegInvGlue.pos_of_pos (x := 1) one_pos
  | succ N ih =>
    obtain ⟨G, h1, h2, h3, h4⟩ := ih
    have hc : Continuous G := h1.continuous
    have hd : deriv (fun x => ∫ s in (1:ℝ)..x, G s) = G := by
      funext x
      exact (hc.deriv_integral G 1 x)
    refine ⟨fun x => ∫ s in (1:ℝ)..x, G s, ?_, ?_, ?_, ?_⟩
    · rw [contDiff_infty_iff_deriv, hd]
      exact ⟨fun x => (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
        (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).differentiableAt, h1⟩
    · intro x hx
      have : ∫ s in (1:ℝ)..x, G s = ∫ s in (1:ℝ)..x, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [Set.uIcc_of_le hx] at hs
        exact h2 s hs.1
      simpa using this
    · intro x
      rw [iteratedDeriv_succ', hd]
      exact h3 x
    · rw [iteratedDeriv_succ', hd]
      exact h4

end GlobalTheory.PsCo.Pc1
