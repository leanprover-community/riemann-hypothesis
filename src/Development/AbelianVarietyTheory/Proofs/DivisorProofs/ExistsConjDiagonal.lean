module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
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
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

@[expose] public section

namespace GlobalTheory.DiagonalConjugateExistence

theorem exists_conj_diagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (t : Fin n → ℂ)
    (ht : Function.Injective t)
    (hA : Matrix.charpoly A = ∏ i : Fin n, (Polynomial.X - Polynomial.C (t i))) :
    ∃ P : GL (Fin n) ℂ, A * (P : Matrix (Fin n) (Fin n) ℂ)
      = (P : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal t := by
  have hev : ∀ i, ∃ v : Fin n → ℂ, v ≠ 0 ∧ A.mulVec v = t i • v := by
    intro i
    have h0 : (Matrix.scalar (Fin n) (t i) - A).det = 0 := by
      rw [← Matrix.eval_charpoly, hA, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv0
    rw [← hv0]
    ext j
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  choose v hv0 hv using hev
  have hli : LinearIndependent ℂ v := by
    refine Module.End.eigenvectors_linearIndependent' (Matrix.toLin' A) t ht v ?_
    intro i
    refine ⟨?_, hv0 i⟩
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, hv]
  have hu : IsUnit (Matrix.of fun i j => v j i : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli
  refine ⟨hu.unit, ?_⟩
  rw [hu.unit_spec]
  ext i j
  have := congrFun (hv j) i
  rw [Matrix.mul_diagonal]
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [this, mul_comm]

end GlobalTheory.DiagonalConjugateExistence
