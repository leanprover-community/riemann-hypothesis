module

public import Mathlib.Analysis.Complex.Norm
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
public import Mathlib.Analysis.Normed.Field.Basic

@[expose] public section

open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF

theorem u_disc (η : ℝ) (hη : 0 < η) (w : ℂ) (hw : η ≤ w.re) :
    ‖(η : ℂ) / w‖ ^ 2 ≤ ((η : ℂ) / w).re := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw
    linarith
  have hn : 0 < Complex.normSq w := Complex.normSq_pos.2 hw0
  rw [norm_div, div_pow, Complex.sq_norm, Complex.sq_norm, Complex.div_re, Complex.normSq_ofReal,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
  have h1 : η * η ≤ η * w.re := mul_le_mul_of_nonneg_left hw hη.le
  simp only [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hn.le)

theorem u_sum_re (η : ℝ) {N : ℕ} (w : Fin N → ℂ) (j : ℕ) :
    (∑ i, ((η : ℂ) / w i) ^ j).re = η ^ j * (∑ i, 1 / (w i) ^ j).re := by
  have h : ∑ i, ((η : ℂ) / w i) ^ j = ((η ^ j : ℝ) : ℂ) * ∑ i, 1 / (w i) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [div_pow, div_eq_mul_one_div, Complex.ofReal_pow]
  rw [h, Complex.re_ofReal_mul]


end Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
