module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
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

@[expose] public section

open Filter Topology

namespace GlobalTheory

theorem hermitian_dotProduct_mulVec_star_swap {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ)
    (hH : H.IsHermitian) (x y : Fin g → ℂ) :
    y ⬝ᵥ H.mulVec (star x) = (starRingEnd ℂ) (x ⬝ᵥ H.mulVec (star y)) := by

  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := hH.apply j i
  simp only [Complex.star_def, Complex.conj_conj] at h ⊢
  rw [h]
  ring

theorem pi_mul_hermitian_alternation {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ)
    (hH : H.IsHermitian) (x y : Fin g → ℂ) :
    (Real.pi : ℂ) * (y ⬝ᵥ H.mulVec (star x)) - Real.pi * (x ⬝ᵥ H.mulVec (star y)) =
      (((-1 : ℤˣ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) *
        ((x ⬝ᵥ H.mulVec (star y)).im : ℂ) := by
  rw [hermitian_dotProduct_mulVec_star_swap H hH x y]
  set a := x ⬝ᵥ H.mulVec (star y)
  have h := Complex.sub_conj a
  push_cast at h
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
  linear_combination (-(Real.pi : ℂ)) * h

end GlobalTheory
