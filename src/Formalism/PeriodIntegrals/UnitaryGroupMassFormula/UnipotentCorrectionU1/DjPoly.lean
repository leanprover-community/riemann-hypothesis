module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CoreStar
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

@[expose] public section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def djVarMat (k j ρ : ℕ) :
    Matrix (Fin j) (Fin j)
      (MvPolynomial ((Fin (2 * (j + ρ) + k + 1) × Fin (2 * (j + ρ) + k + 1)) ⊕
        (Fin (2 * (j + ρ) + k + 1) × Fin (2 * (j + ρ) + k + 1))) ℂ) :=
  fun a b => MvPolynomial.X (Sum.inl (⟨2 * (j + ρ) + k - a.val, by omega⟩, ⟨b.val, by omega⟩))

theorem isPolyDeg_determinant_derivative (k j ρ : ℕ) : IsPolyDeg j (DjU k j ρ) := by
  refine ⟨∑ σ : Equiv.Perm (Fin j),
      MvPolynomial.C ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)) * ∏ i, djVarMat k j ρ (σ i) i, ?_, ?_⟩
  · refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
    refine Finset.sup_le fun σ _ => ?_
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    calc (∑ i : Fin j, (djVarMat k j ρ (σ i) i).totalDegree) ≤ ∑ _i : Fin j, 1 := by
          refine Finset.sum_le_sum fun i _ => ?_
          simp [djVarMat, MvPolynomial.totalDegree_X]
      _ = j := by simp
  · intro g
    rw [DjU, Matrix.det_apply']

    simp only [map_sum, map_mul, map_prod, MvPolynomial.eval_C]
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [djVarMat, Zh, MvPolynomial.eval_X]

theorem determinant_derivative_polynomial : DjPoly := fun k j ρ => isPolyDeg_determinant_derivative k j ρ

end PI.UnitaryCorollaryDerivatives
