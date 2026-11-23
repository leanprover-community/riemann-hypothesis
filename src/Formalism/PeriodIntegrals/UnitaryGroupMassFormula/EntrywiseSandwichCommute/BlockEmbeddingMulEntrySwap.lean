module

public import Formalism.YangianSpanCharacter.ExchangeGen
public import Formalism.YangianSpanCharacter.StatementT
public import Mathlib.Basic.Complex.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstEmbeddingOne

@[expose] public section

namespace PI.QmSandwichWork

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P.W

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem tm_entry_comm (Y : ℂ) {p c ci x : A} (hp : Commute p x) (hc : Commute c x)
    (hci : Commute ci x) (i j : Fin 2) : Commute (Tm Y p c ci i j) x := by
  fin_cases i <;> fin_cases j
  · simpa [Tm] using (Algebra.commute_algebraMap_left Y x).add_left hp
  · simpa [Tm] using hc.neg_left
  · simpa [Tm] using hci
  · simp [Tm]

theorem flip_row (D : ℂ) (K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) :
    ((D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A) * K) (0, 0) (0, 0) =
      algebraMap ℂ A (D - 1) * K (0, 0) (0, 0) := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Pf, Matrix.one_apply,
    Algebra.algebraMap_eq_smul_one, sub_smul, sub_mul, smul_mul_assoc]

theorem flip_col (D : ℂ) (K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) :
    (K * (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A)) (0, 0) (0, 0) =
      algebraMap ℂ A (D - 1) * K (0, 0) (0, 0) := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Pf, Matrix.one_apply,
    Algebra.algebraMap_eq_smul_one, sub_smul, sub_mul, mul_sub, mul_one, smul_mul_assoc, mul_smul_comm]

theorem block_embedding_mul_entry (M N : Matrix (Fin 2) (Fin 2) A) : (E1 M * E2 N) (0, 0) (0, 0) = M 0 0 * N 0 0 := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, E1, E2]

theorem block_embedding_mul_entry_swap (M N : Matrix (Fin 2) (Fin 2) A) : (E2 N * E1 M) (0, 0) (0, 0) = N 0 0 * M 0 0 := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, E1, E2]

end PI.QmSandwichWork
