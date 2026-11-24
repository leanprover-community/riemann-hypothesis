module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow
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
public import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace UpperTheory.Gal.LocD

theorem tracePow : TracePow := by
  intro J _ _ _ _ φ hφ k₀
  by_contra hne
  push_neg at hne
  set p := φ.charpoly with hp
  have hc : p.coeff 0 ≠ 0 := by
    intro h0
    obtain ⟨m, hm, hm0⟩ := (LinearMap.charpoly_constantCoeff_eq_zero_iff φ).1
      (by rw [Polynomial.constantCoeff_apply]; exact h0)
    exact hm (hφ (by rw [hm0, map_zero]))
  set t : Polynomial ℂ := -Polynomial.C (p.coeff 0)⁻¹ * Polynomial.divX p with ht
  have hinv : φ * Polynomial.aeval φ t = 1 := by
    have h := congrArg (Polynomial.aeval φ) (Polynomial.X_mul_divX_add p)
    rw [hp, LinearMap.aeval_self_charpoly, ← hp] at h
    simp only [map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h
    have h' : φ * Polynomial.aeval φ (Polynomial.divX p) = -(algebraMap ℂ _ (p.coeff 0)) :=
      eq_neg_of_add_eq_zero_left h
    rw [ht, map_mul, map_neg, Polynomial.aeval_C, neg_mul, mul_neg, ← mul_assoc,
      ← Algebra.commutes, mul_assoc, h', mul_neg, neg_neg, ← map_mul, inv_mul_cancel₀ hc,
      map_one]
  set Q : Polynomial ℂ := (Polynomial.X * t) ^ k₀ with hQ
  have hQ1 : Polynomial.aeval φ Q = 1 := by
    rw [hQ, map_pow, map_mul, Polynomial.aeval_X, hinv, one_pow]
  have htr : LinearMap.trace ℂ J (Polynomial.aeval φ Q) = 0 := by

    rw [Polynomial.aeval_eq_sum_range, map_sum]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [map_smul, smul_eq_mul]
    by_cases hi : k₀ ≤ i
    · rw [hne i hi, mul_zero]
    · rw [hQ, mul_pow, Polynomial.coeff_X_pow_mul', if_neg hi, zero_mul]
  rw [hQ1, LinearMap.trace_one] at htr
  exact (Nat.cast_ne_zero.2 (Module.finrank_pos (R := ℂ) (M := J)).ne') htr

end UpperTheory.Gal.LocD
