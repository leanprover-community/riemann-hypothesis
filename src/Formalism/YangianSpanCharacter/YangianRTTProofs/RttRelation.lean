module

public import Formalism.YangianSpanCharacter.StatementT
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace Formalism.YangianSpanCharacter.P

open Matrix Formalism.YangianSpanCharacter.T

set_option linter.unusedSimpArgs false in
theorem rttRelation : Formalism.YangianSpanCharacter.T.RTT := by
  intro R A _ _ _ p c ci Y Y' hW
  obtain ⟨hcc, hcc', hpc⟩ := hW
  have hpc2 : ∀ x : A, p * (c * x) = c * (p * x) + c * x := fun x => by
    rw [← mul_assoc, hpc, add_mul, mul_assoc]
  have hpci : p * ci = ci * p - ci := by
    have h := congrArg (fun x => ci * x * ci) hpc
    simp only [mul_add, add_mul, ← mul_assoc, hcc', one_mul] at h
    simp only [mul_assoc, hcc, mul_one] at h
    rw [h]; abel
  have hpci2 : ∀ x : A, p * (ci * x) = ci * (p * x) - ci * x := fun x => by
    rw [← mul_assoc, hpci, sub_mul, mul_assoc]
  have hcc2 : ∀ x : A, c * (ci * x) = x := fun x => by rw [← mul_assoc, hcc, one_mul]
  have hcc2' : ∀ x : A, ci * (c * x) = x := fun x => by rw [← mul_assoc, hcc', one_mul]
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, T1, T2, Pf, Tm,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  all_goals
    simp only [Algebra.algebraMap_eq_smul_one, mul_add, add_mul, mul_sub, sub_mul, neg_mul,
      mul_neg, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, mul_assoc, smul_add, smul_sub,
      smul_neg, smul_smul, hpc, hpc2, hpci, hpci2, hcc, hcc', hcc2, hcc2', neg_neg, sub_smul]
  all_goals module

end Formalism.YangianSpanCharacter.P
