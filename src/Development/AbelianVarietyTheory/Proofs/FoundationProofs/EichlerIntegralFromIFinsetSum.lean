module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.EichlerSum

theorem eichler_integrand_intervalIntegrable {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (τ : ℍ) (k : ℕ) :
    IntervalIntegrable (fun t : ℝ => (f ∘ UpperHalfPlane.ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) *
        (-(Complex.I + t * ((τ : ℂ) - Complex.I))) ^ k * ((τ : ℂ) - Complex.I)) MeasureTheory.volume 0 1 := by
  have hd := (UpperHalfPlane.mdifferentiable_iff.mp hf).continuousOn
  apply ContinuousOn.intervalIntegrable
  have hmap : Set.MapsTo (fun t : ℝ => Complex.I + t * ((τ : ℂ) - Complex.I)) (Set.uIcc 0 1) {z : ℂ | 0 < z.im} := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    obtain ⟨h0, h1⟩ := ht
    have hτ := τ.im_pos
    simp only [Set.mem_setOf_eq, Complex.add_im, Complex.I_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.sub_im, Complex.sub_re, Complex.I_re, zero_mul, add_zero]
    rw [UpperHalfPlane.coe_im]
    rcases eq_or_lt_of_le h1 with h | h
    · subst h; nlinarith
    · nlinarith [mul_nonneg h0 hτ.le]
  have hc : ContinuousOn (fun t : ℝ => Complex.I + t * ((τ : ℂ) - Complex.I)) (Set.uIcc 0 1) := by fun_prop
  refine ContinuousOn.mul (ContinuousOn.mul (hd.comp hc hmap) ?_) continuousOn_const
  fun_prop

theorem eichler_finset_sum (w : ℕ) {ι : Type} [Fintype ι] (g : ι → ℍ → ℂ)
    (hg : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g i)) (τ : ℍ) :
    eichler w (∑ i, g i) τ = ∑ i, eichler w (g i) τ := by
  unfold eichler
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_

  rw [← Finset.sum_mul, ← map_sum, ← Finset.mul_sum,
  ← intervalIntegral.integral_finsetSum fun i _ => eichler_integrand_intervalIntegrable (hg i) τ (w - j)]
  congr 4
  funext t
  simp only [Function.comp_apply, Finset.sum_apply, Finset.sum_mul]

end GlobalTheory.EichlerSum
