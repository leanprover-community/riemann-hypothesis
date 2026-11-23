module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRotCut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem rotation_ode_holds : GTRRODE := by
  intro ι _ _ Mf Bm h0 hadd hper hd hoff
  have hderiv : ∀ (φ : ℝ) (i j : ι), HasDerivAt (fun x => Mf x i j) (Bm i i * Mf φ i j) φ := by
    intro φ i j
    have hg0 := HasDerivAt.sum (u := Finset.univ) (fun k _ => (hd i k).mul_const (Mf φ k j))
    have ef : (∑ k : ι, fun (y : ℝ) => Mf y i k * Mf φ k j) = fun h : ℝ => ∑ k, Mf h i k * Mf φ k j := by
      funext h
      rw [Finset.sum_apply]
    rw [ef] at hg0
    have hsum : ∑ k, Bm i k * Mf φ k j = Bm i i * Mf φ i j := by
      rw [Finset.sum_eq_single i]
      · intro k _ hk
        rw [hoff i k (Ne.symm hk), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [hsum] at hg0
    have h2 := HasDerivAt.comp_sub_const φ φ (by rw [sub_self]; exact hg0)
    have e : (fun x => Mf x i j) = fun x : ℝ => ∑ k, Mf (x - φ) i k * Mf φ k j := by
      funext x
      rw [← Matrix.mul_apply, ← hadd, sub_add_cancel]
    rw [e]
    exact h2
  have hsol : ∀ (i j : ι) (x : ℝ), Mf x i j = Complex.exp (Bm i i * x) * (if i = j then 1 else 0) := by
    intro i j x
    have hf : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (-Bm i i * y) * Mf y i j) 0 y := by
      intro y
      have he : HasDerivAt (fun y : ℝ => Complex.exp (-Bm i i * y)) (Complex.exp (-Bm i i * y) * (-Bm i i * 1)) y :=
        (((hasDerivAt_id y).ofReal_comp).const_mul (-Bm i i)).cexp
      have hm := he.mul (hderiv y i j)
      have h3 : Complex.exp (-Bm i i * ↑y) * (-Bm i i * 1) * Mf y i j + Complex.exp (-Bm i i * ↑y) * (Bm i i * Mf y i j) = 0 := by
        ring
      rw [h3] at hm
      exact hm
    have hc := is_const_of_deriv_eq_zero (fun y => (hf y).differentiableAt) (fun y => (hf y).deriv) x 0
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, h0, Matrix.one_apply] at hc
    rw [← hc, ← mul_assoc, ← Complex.exp_add]
    simp
  have hn : ∀ i, ∃ n : ℤ, Bm i i = n * Complex.I := by
    intro i
    have h1 := hsol i i (2 * Real.pi)
    rw [hper] at h1
    simp only [Matrix.one_apply_eq, if_true, mul_one] at h1
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1.symm
    refine ⟨n, ?_⟩
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by
      simp [Real.pi_ne_zero]
    apply mul_right_cancel₀ hpi
    push_cast at hn
    linear_combination hn
  choose n hn using hn
  refine ⟨n, fun φ i j => ?_⟩
  rw [hsol]
  split_ifs with h
  · subst h
    rw [hn]
    ring_nf
  · simp

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
