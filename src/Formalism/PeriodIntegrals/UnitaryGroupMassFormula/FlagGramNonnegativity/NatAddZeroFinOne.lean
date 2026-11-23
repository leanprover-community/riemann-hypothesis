module

public import Formalism.PeriodIntegrals.FlagGramNonneg
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix PI.FlagGramNonneg

namespace PI.UnitaryGroupMassFormula.FlagGramNonneg

theorem det_succ_schur {E : Type} [Field E] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (h : IsUnit (Z.submatrix Fin.castSucc Fin.castSucc).det) :
    Z.det = (Z.submatrix Fin.castSucc Fin.castSucc).det *
      (Z (Fin.last r) (Fin.last r) - (fun b => Z (Fin.last r) (Fin.castSucc b)) ⬝ᵥ
        ((Z.submatrix Fin.castSucc Fin.castSucc)⁻¹ *ᵥ (fun a => Z (Fin.castSucc a) (Fin.last r)))) := by
  haveI : Invertible (Z.submatrix Fin.castSucc Fin.castSucc) := Matrix.invertibleOfIsUnitDet _ h
  have hZ : Z.submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks
      (Z.submatrix Fin.castSucc Fin.castSucc) (Matrix.of fun a (_ : Fin 1) => Z (Fin.castSucc a) (Fin.last r))
      (Matrix.of fun (_ : Fin 1) b => Z (Fin.last r) (Fin.castSucc b))
      (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => Z (Fin.last r) (Fin.last r)) := by
    ext (i | i) (j | j)
    · rfl
    · rw [Fin.fin_one_eq_zero j]
      rfl
    · rw [Fin.fin_one_eq_zero i]
      rfl
    · rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
      rfl
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv Z, hZ, Matrix.det_fromBlocks₁₁,
    Matrix.invOf_eq_nonsing_inv, Matrix.det_unique (n := Fin 1)]
  congr 1
  rw [Matrix.sub_apply, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.of_apply] <;> rfl

theorem leadMinorE_succ {E : Type} [Field E] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    leadMinorE Z (r + 1) = Z.det := by
  unfold leadMinorE
  rw [dite_eq_left le_rfl]
  rfl

theorem leadMinorE_self {E : Type} [Field E] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    leadMinorE Z r = (Z.submatrix Fin.castSucc Fin.castSucc).det := by
  unfold leadMinorE
  rw [dite_eq_left (Nat.le_succ r)]
  rfl

end PI.UnitaryGroupMassFormula.FlagGramNonneg
