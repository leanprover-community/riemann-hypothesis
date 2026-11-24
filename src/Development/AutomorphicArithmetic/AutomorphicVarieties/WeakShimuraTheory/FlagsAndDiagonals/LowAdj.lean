module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.WMConjDiagonal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem low_mk {R : Type} [CommRing R] (x y z t : R) :
    IsLow (!![1, 0, 0, 0; x, 1, 0, 0; y + t * x, t, 1, 0; z, y, -x, 1] : M4 R) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four] <;> ring
  · intro i
    fin_cases i <;> simp
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp at h ⊢

private theorem low_adj {R : Type} [CommRing R] {m : M4 R} (h : IsLow m) : IsLow (adj m) := by
  refine ⟨sp_adj h.1, fun i => ?_, fun i j hij => ?_⟩
  · rw [adj_apply, h.2.1]
    fin_cases i <;> simp [sgn]
  · rw [adj_apply, h.2.2 _ _ (Fin.rev_lt_rev.2 hij), smul_zero]

private theorem up_of {R : Type} [CommRing R] {w : M4 R} (h : IsGSp 1 w) (h0 : IsUnit (w 0 0))
    (h1 : w 1 0 = 0) (h2 : w 2 0 = 0) (h3 : w 3 0 = 0) (h4 : w 2 1 = 0) : IsUp w := by
  have e := sp_adj_mul h
  have e1 := congrFun (congrFun e 1) 0
  have e2 := congrFun (congrFun e 2) 0
  simp [adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four, h1, h2, h3] at e1 e2
  have a1 : w 3 2 = 0 := (h0.mul_left_eq_zero).1 e1
  have a2 : w 3 1 = 0 := (h0.mul_left_eq_zero).1 e2
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> assumption

theorem UpperTheory.V.Ws.Lab.luSp :
    ∀ (R : Type) [CommRing R] (u : M4 R), IsGSp 1 u → IsUnit (u 0 0) → IsUnit (u 0 0 * u 1 1 - u 0 1 * u 1 0) →
      ∃ n b : M4 R, IsLow n ∧ IsGSp 1 b ∧ IsUp b ∧ u = n * b := by
  intro R _ u hu h0 hD
  obtain ⟨ai, hai⟩ := h0.exists_right_inv
  obtain ⟨di, hdi⟩ := hD.exists_right_inv
  obtain ⟨x, hx⟩ : ∃ x : R, x = -(u 1 0 * ai) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : R, s = (u 2 1 * u 1 0 - u 2 0 * u 1 1) * di := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : R, t = (u 0 1 * u 2 0 - u 0 0 * u 2 1) * di := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : R, y = s - t * x := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : R, z = (-(y * u 1 0) + x * u 2 0 - u 3 0) * ai := ⟨_, rfl⟩
  have hm := low_mk x y z t
  refine ⟨_, _, low_adj hm, sp_mul hm.1 hu, ?_, ?_⟩
  · refine up_of (sp_mul hm.1 hu) ?_ ?_ ?_ ?_ ?_
    · simpa [Matrix.mul_apply, Fin.sum_univ_four] using h0
    · simp [Matrix.mul_apply, Fin.sum_univ_four]
      linear_combination u 0 0 * hx + (-u 1 0) * hai
    · simp [Matrix.mul_apply, Fin.sum_univ_four]
      linear_combination u 0 0 * hy + u 0 0 * hs + u 1 0 * ht + (-u 2 0) * hdi
    · simp [Matrix.mul_apply, Fin.sum_univ_four]
      linear_combination u 0 0 * hz + (-(y * u 1 0) + x * u 2 0 - u 3 0) * hai
    · simp [Matrix.mul_apply, Fin.sum_univ_four]
      linear_combination u 0 1 * hy + u 0 1 * hs + u 1 1 * ht + (-u 2 1) * hdi
  · rw [← Matrix.mul_assoc, sp_adj_mul hm.1, Matrix.one_mul]
