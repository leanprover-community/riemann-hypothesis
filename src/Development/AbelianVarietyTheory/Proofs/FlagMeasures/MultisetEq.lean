module

public import Formalism.RealPlaceAnalysis.StatementB
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

@[expose] public section

open Finset Matrix

noncomputable section

namespace GlobalTheory.Dec.GelfSepProof


open PowerSeries Matrix in
theorem _root_.GlobalTheory.Dec.GelfSepProof.gen {n : ℕ} (l : Fin n → ℂ) :
    ((1 : PowerSeries ℂ) -
        PowerSeries.X * PowerSeries.mk fun (k : ℕ) ↦ ∑ a : Fin n, ∑ b : Fin n, (_root_.Formalism.REAL.Amat l ^ k) a b) *
      ∏ a : Fin n, ((1 : PowerSeries ℂ) - (PowerSeries.C : ℂ → PowerSeries ℂ) (l a) * PowerSeries.X) =
    ∏ a : Fin n,
      ((1 : PowerSeries ℂ) -
        ((PowerSeries.C : ℂ → PowerSeries ℂ) (l a) + (1 : PowerSeries ℂ)) * PowerSeries.X) := by
  have hA : ∀ a b, _root_.Formalism.REAL.Amat l a b = if a = b then l a else if a < b then -1 else 0 := by
    intro a b
    unfold _root_.Formalism.REAL.Amat
    rfl
  set A := _root_.Formalism.REAL.Amat l with hAdef
  let Y : Matrix (Fin n) (Fin n) (PowerSeries ℂ) := A.map (PowerSeries.C : ℂ → PowerSeries ℂ)
  let B : Matrix (Fin n) (Fin n) (PowerSeries ℂ) :=
    Matrix.of fun a b => PowerSeries.mk fun k => (A ^ k) a b
  have hB : (1 - (X : PowerSeries ℂ) • Y) * B = 1 := by
    rw [sub_mul, one_mul, smul_mul_assoc]
    ext a b k
    rcases k with _ | k
    · simp [B, Matrix.one_apply]

    · simp [B, Y, Matrix.mul_apply, Matrix.one_apply, pow_succ', PowerSeries.coeff_succ_X_mul,
        map_sum]
      split_ifs <;> simp
  let c : Matrix (Fin n) (Fin 1) (PowerSeries ℂ) := replicateCol (Fin 1) 1
  let R : Matrix (Fin 1) (Fin n) (PowerSeries ℂ) := replicateRow (Fin 1) 1
  let J : Matrix (Fin n) (Fin n) (PowerSeries ℂ) := Matrix.of fun _ _ => 1
  let U : Matrix (Fin n) (Fin 1) (PowerSeries ℂ) := -((X : PowerSeries ℂ) • (B * c))
  have hcR : c * R = J := by
    ext a b
    simp [c, R, J, Matrix.mul_apply]
  have hBc : (1 - (X : PowerSeries ℂ) • Y) * (B * c) = c := by
    rw [← Matrix.mul_assoc, hB, Matrix.one_mul]
  have hfactor : (1 - (X : PowerSeries ℂ) • Y) * (1 + U * R) =
      1 - (X : PowerSeries ℂ) • Y - (X : PowerSeries ℂ) • J := by
    have hU : (1 - (X : PowerSeries ℂ) • Y) * U = -((X : PowerSeries ℂ) • c) := by
      show (1 - (X : PowerSeries ℂ) • Y) * -((X : PowerSeries ℂ) • (B * c)) = _
      rw [Matrix.mul_neg, Matrix.mul_smul, hBc]
    rw [mul_add, mul_one, ← Matrix.mul_assoc, hU, Matrix.neg_mul, Matrix.smul_mul, hcR]
    abel
  have hdet1 : (1 - (X : PowerSeries ℂ) • Y).det = ∏ a : Fin n, (1 - C (l a) * X) := by
    rw [Matrix.det_of_isUpperTriangular]
    · refine Finset.prod_congr rfl fun a _ => ?_
      simp [Y, hA, mul_comm]
    · intro a b hab
      have hba : b < a := hab
      simp [Y, hA, hba.ne', not_lt_of_gt hba, Matrix.one_apply_ne hba.ne']
  have hdet2 : (1 - (X : PowerSeries ℂ) • Y - (X : PowerSeries ℂ) • J).det =
      ∏ a : Fin n, (1 - (C (l a) + 1) * X) := by
    rw [Matrix.det_of_isLowerTriangular]
    · refine Finset.prod_congr rfl fun a _ => ?_
      simp [Y, J, hA]
      ring
    · intro a b hab
      have hab' : a < b := hab
      simp [Y, J, hA, hab'.ne, hab', Matrix.one_apply_ne hab'.ne]
  have hdet3 : (1 + U * R).det =
      1 - X * PowerSeries.mk fun k => ∑ a : Fin n, ∑ b : Fin n, (A ^ k) a b := by
    rw [Matrix.det_one_add_mul_comm, Matrix.det_unique]
    simp [U, R, B, c, Matrix.mul_apply, Finset.mul_sum, sub_eq_add_neg]
    simp only [← Finset.mul_sum]
    congr 1
    ext k

    simp [PowerSeries.coeff_mk, map_sum]
  rw [← hdet2, ← hfactor, Matrix.det_mul, hdet1, hdet3, mul_comm]



end GlobalTheory.Dec.GelfSepProof

namespace GlobalTheory.Dec

end GlobalTheory.Dec
