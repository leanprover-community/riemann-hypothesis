module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InCell
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L GlobalTheory.CompanionTheory.MuC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.MuC

variable {D : D7} {p : ℕ}

theorem mul_nBlock_inl {R : Type} [CommRing R] {n : ℕ} (A : Matrix (Fin (n + n)) (Fin (n + n)) R)
    (y : Matrix (Fin n) (Fin n) R) (i : Fin (n + n)) (j : Fin n) :
    (A * blk4 1 y 0 1) i (finSumFinEquiv (Sum.inl j)) = A i (finSumFinEquiv (Sum.inl j)) := by
  simp [Matrix.mul_apply, blk4, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Matrix.one_apply]

theorem mul_nBlock_inr {R : Type} [CommRing R] {n : ℕ} (A : Matrix (Fin (n + n)) (Fin (n + n)) R)
    (y : Matrix (Fin n) (Fin n) R) (i : Fin (n + n)) (j : Fin n) :
    (A * blk4 1 y 0 1) i (finSumFinEquiv (Sum.inr j)) =
      ∑ k, A i (finSumFinEquiv (Sum.inl k)) * y k j + A i (finSumFinEquiv (Sum.inr j)) := by
  rw [Matrix.mul_apply, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₂]
  simp [Matrix.one_apply]

theorem lowC_mul_nb {nb : hermA D p → G D p} (hnb : IsNMap nb) (g : G D p) (y : hermA D p) :
    lowC (g * nb y) = lowC g := by
  have hm : mat (g * nb y) = mat g * blk4 1 y.1 0 1 := by
    rw [← hnb y]; rfl
  ext i j
  simp only [lowC, Matrix.submatrix_apply, hm]
  exact mul_nBlock_inl _ _ _ _

theorem lowD_mul_nb {nb : hermA D p → G D p} (hnb : IsNMap nb) (g : G D p) (y : hermA D p) :
    lowD (g * nb y) = lowC g * y.1 + lowD g := by
  have hm : mat (g * nb y) = mat g * blk4 1 y.1 0 1 := by
    rw [← hnb y]; rfl
  ext i j
  simp only [lowC, lowD, Matrix.submatrix_apply, hm, Matrix.add_apply, Matrix.mul_apply]
  exact mul_nBlock_inr _ _ _ _

theorem isB_mul_nb {D : D7} {p : ℕ} {e : AE D} {nb : hermA D p → G D p} (hnb : IsNMap nb) {g : G D p}
    (y x : hermS D p e) : IsB e (g * nb y.1) (x + y) ↔ IsB e g x := by
  have hy : e • y.1.1 = y.1.1 := y.2
  have hc : e • (lowC g * y.1.1) = lowC g * y.1.1 := by rw [← Matrix.mul_smul, hy]
  have hs : (x + y).1.1 = x.1.1 + y.1.1 := rfl
  unfold IsB InCell
  rw [lowC_mul_nb hnb, lowD_mul_nb hnb, hs]
  refine and_congr_right fun _ => ?_
  simp only [mm]
  rw [mul_add, smul_add, hc, add_comm (lowC g * y.1.1) (e • lowD g), add_left_inj]

end GlobalTheory.CompanionTheory.MuC

end
