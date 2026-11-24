module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import GroundTheory.GlobalFields.Artin.LogCharpoly
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory

open Polynomial

theorem charpolyRev_mul_charpolyRev_eq_one_of_trace_pow_add_eq_zero
    {K R : Type} [Field K] [CharZero K] [CommRing R] [Algebra K R] {p q : ℕ}
    (M : Matrix (Fin p) (Fin p) R) (N : Matrix (Fin q) (Fin q) R)
    (h : ∀ k, 1 ≤ k → (M ^ k).trace + (N ^ k).trace = 0) :
    M.charpolyRev * N.charpolyRev = 1 := by
  set f := M.charpolyRev
  set g := N.charpolyRev
  have hS : (PowerSeries.mk fun k => (M ^ (k + 1)).trace) +
      (PowerSeries.mk fun k => (N ^ (k + 1)).trace) = 0 := by
    ext k
    simp [h (k + 1) (Nat.le_add_left 1 k)]
  have hd : derivative (f * g) = 0 := by
    apply Polynomial.coe_injective
    rw [Polynomial.derivative_mul, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_mul,
      GroundTheory.Global.coe_derivative_charpolyRev, GroundTheory.Global.coe_derivative_charpolyRev,
      Polynomial.coe_zero]
    calc -(f : PowerSeries R) * PowerSeries.mk (fun k => (M ^ (k + 1)).trace) * (g : PowerSeries R) +
          (f : PowerSeries R) * (-(g : PowerSeries R) * PowerSeries.mk fun k => (N ^ (k + 1)).trace)
        = -((f : PowerSeries R) * (g : PowerSeries R)) *
          ((PowerSeries.mk fun k => (M ^ (k + 1)).trace) +
            (PowerSeries.mk fun k => (N ^ (k + 1)).trace)) := by ring
      _ = 0 := by rw [hS, mul_zero]
  have h0 : (f * g).coeff 0 = 1 := by
    rw [Polynomial.mul_coeff_zero, Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev, Matrix.eval_charpolyRev,
      mul_one]
  ext k
  rcases k with _ | k
  · rw [h0, Polynomial.coeff_one_zero]
  · have hk := congrArg (fun r => r.coeff k) hd
    simp only [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hk
    have hu : IsUnit ((k : R) + 1) := by
      have : ((k : R) + 1) = algebraMap K R ((k : K) + 1) := by simp
      rw [this]
      exact (IsUnit.mk0 _ (by exact_mod_cast Nat.succ_ne_zero k)).map _
    rw [Polynomial.coeff_one, if_neg (Nat.succ_ne_zero k)]
    exact hu.mul_left_eq_zero.mp hk

end GlobalTheory
