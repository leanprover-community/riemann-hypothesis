module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplReduceMem

theorem omega_sub_smul {l : Type} [Fintype l] [DecidableEq l] (u v w : l ⊕ l → ℝ) (c d : ℝ) :
    symplOmega (u - c • w) (v - d • w) =
      symplOmega u v - d * symplOmega u w - c * symplOmega w v + c * d * symplOmega w w := by
  unfold symplOmega
  simp only [mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  ring

theorem omega_tail (h2 : SymplCons.Statement) {n : ℕ} (x y : Fin (n + 1) ⊕ Fin (n + 1) → ℝ) :
    symplOmega (symplTail x) (symplTail y) =
      symplOmega x y - (x (Sum.inr 0) * y (Sum.inl 0) - x (Sum.inl 0) * y (Sum.inr 0)) := by
  have key := (h2 ℝ n).2 (x (Sum.inl 0)) (x (Sum.inr 0)) (y (Sum.inl 0)) (y (Sum.inr 0))
    (symplTail x) (symplTail y)
  rw [(h2 ℝ n).1 x, (h2 ℝ n).1 y] at key
  linarith

theorem J_succ {n : ℕ} (a b : Fin n ⊕ Fin n) :
    J (Fin (n + 1)) ℝ (Sum.map Fin.succ Fin.succ a) (Sum.map Fin.succ Fin.succ b) =
      J (Fin n) ℝ a b := by
  rcases a with i | i <;> rcases b with j | j <;> simp [J, Matrix.one_apply, Fin.succ_inj]

theorem J_succ_e {n : ℕ} (a : Fin n ⊕ Fin n) :
    J (Fin (n + 1)) ℝ (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) = 0 := by
  rcases a with i | i <;> simp [J, one_apply, Fin.succ_ne_zero]

theorem J_e_succ {n : ℕ} (b : Fin n ⊕ Fin n) :
    J (Fin (n + 1)) ℝ (Sum.inl 0) (Sum.map Fin.succ Fin.succ b) = 0 := by
  rcases b with j | j <;> simp [J, one_apply, (Fin.succ_ne_zero j).symm]

theorem reduce_row {n : ℕ} (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ)
    (a : Fin n ⊕ Fin n) :
    symplReduce H a = symplTail (H (Sum.map Fin.succ Fin.succ a)) -
      (H (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) / H (Sum.inl 0) (Sum.inl 0)) •
        symplTail (H (Sum.inl 0)) := by
  funext b
  simp only [symplReduce, symplTail, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

end PSymplReduceMem


open PSymplReduceMem in
theorem SymplReduceMem.proof (h1 : SymplOmegaMem.Statement) (h2 : SymplCons.Statement) :
    SymplReduceMem.Statement := by
  intro n H hH he
  have hω := (h1 ℝ (Fin (n + 1)) H).1 hH
  rw [h1 ℝ (Fin n) (symplReduce H)]
  intro a b
  rw [reduce_row, reduce_row, omega_sub_smul, omega_tail h2, omega_tail h2, omega_tail h2,
    omega_tail h2, hω, hω, hω, hω, J_succ, J_succ_e, J_e_succ]
  simp only [J, fromBlocks_apply₁₁, Matrix.zero_apply]
  field_simp
  ring

end GroundTheory.Heights₂.Heights
