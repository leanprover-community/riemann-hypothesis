module

public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.OrderAsym
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AnalyticSeries.NeZeroOne
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

@[expose] public section

noncomputable section

namespace UpperTheory.ConvolutionTheory.R

open PositivityTheory.RgJS UpperTheory.ConvolutionTheory.Rs

theorem logAsym : LogAsym := by
  intro W q X d A hS x y
  obtain ⟨F, σ₀, hF, he⟩ := hS.rs x y
  have hn := exp_re hS x y F σ₀ hF he
  have h0 : ∀ t ∈ Set.Icc (1 : ℝ) 2, ‖F t‖ ≠ 0 := fun t ht => by
    rcases ht.1.eq_or_lt with h | h
    · subst h
      simpa using ne_zero_one hS x y F σ₀ hF he
    · rw [hn t h]
      refine mul_ne_zero ?_ (Real.exp_pos _).ne'
      split_ifs
      · linarith
      · exact one_ne_zero
  have hc : ContinuousOn (fun t : ℝ => Real.log ‖F t‖) (Set.Icc 1 2) := ContinuousOn.log (fun t ht =>
    ((hF t (by linarith [ht.1])).continuousAt.comp (f := fun t : ℝ => (t : ℂ))
      Complex.continuous_ofReal.continuousAt).norm.continuousWithinAt) h0
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨M, fun σ h1 h2 => ?_⟩
  have h := hM σ ⟨h1.le, h2⟩
  rw [hn σ h1, Real.norm_eq_abs] at h
  unfold dre
  split_ifs at h ⊢
  · rw [Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp] at h
    rwa [sub_neg_eq_add, add_comm]
  · rwa [one_mul, Real.log_exp, ← sub_zero (Complex.re _)] at h

end UpperTheory.ConvolutionTheory.R
