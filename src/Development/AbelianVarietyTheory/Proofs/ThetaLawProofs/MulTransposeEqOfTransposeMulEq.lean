module

public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
public import Mathlib.LinearAlgebra.Matrix.Adjugate

@[expose] public section

namespace GlobalTheory.TransposeMulCommute

theorem mul_transpose_eq_of_transpose_mul_eq :
    ∀ {al : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) ℤ} {m : ℕ}, (1 : ℕ) ≤ m →
      Matrix.transpose al * al = (↑m : ℤ) • (1 : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) ℤ) →
      al * Matrix.transpose al = (↑m : ℤ) • (1 : Matrix (Fin (4 : ℕ)) (Fin (4 : ℕ)) ℤ) := by
  intro al m hm h
  have hm0 : (m : ℤ) ≠ 0 := by
    have : m ≠ 0 := by omega
    exact_mod_cast this
  have hdet : al.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ hm0 h1.symm
  have h2 : (al * al.transpose) * al = ((m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) * al := by
    rw [Matrix.mul_assoc, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  have h3 := congrArg (fun X => X * al.adjugate) h2
  simp only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at h3
  ext i j
  have h4 := congrFun (congrFun h3 i) j
  rw [Matrix.smul_apply, Matrix.smul_apply al.det, smul_eq_mul, smul_eq_mul al.det] at h4
  exact mul_left_cancel₀ hdet h4

end GlobalTheory.TransposeMulCommute
