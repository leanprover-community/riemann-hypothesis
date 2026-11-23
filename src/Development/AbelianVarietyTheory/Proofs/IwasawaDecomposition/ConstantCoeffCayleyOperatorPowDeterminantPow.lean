module

public import ReciprocityTheory.DualLattices.FischerAdjointStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockGraph

@[expose] public section

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

namespace GlobalTheory

theorem cayOp_pow_cayDet_pow (p s k : ℕ) :
    (cayOp p ℂ ^ k) (cayDet p ℂ ^ (s + k)) =
      (∏ t ∈ Finset.range k, ∏ j ∈ Finset.range p, (s + 1 + t + j)) • cayDet p ℂ ^ s := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ← add_assoc, cayley p ℂ (s + k + 1), Nat.add_sub_cancel,
      map_nsmul, ih, smul_smul, Finset.prod_range_succ]
    congr 1
    rw [mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    ring

theorem prod_succ_mul_factorial (j q : ℕ) :
    (∏ t ∈ Finset.range q, (1 + t + j)) * j.factorial = (q + j).factorial := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.prod_range_succ, mul_right_comm, ih, show q + 1 + j = (q + j) + 1 by ring,
      Nat.factorial_succ]
    ring

theorem constantCoeff_cayOp_pow_cayDet_pow : ∀ (p q : ℕ),
    constantCoeff ((cayOp p ℂ ^ q) (cayDet p ℂ ^ q)) =
      ∏ i ∈ Finset.range p, (((q + i).factorial : ℂ) / i.factorial) := by
  intro p q
  have h := cayOp_pow_cayDet_pow p 0 q
  rw [zero_add] at h
  rw [h, pow_zero, map_nsmul, map_one, nsmul_eq_mul, mul_one, Finset.prod_comm]
  push_cast
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [eq_div_iff (by exact_mod_cast (Nat.factorial_pos j).ne')]
  have := prod_succ_mul_factorial j q
  simp only [zero_add] at *
  exact_mod_cast this

end GlobalTheory
