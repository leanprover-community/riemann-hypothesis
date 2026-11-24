module

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
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

theorem UpperTheory.Reformulated.B.DiagonalizeThreeByThree.diagonalize_three_by_three_split :
    ∀ {K : Type} [inst : Field K] (d : Fin (3 : ℕ) → K),
    Function.Injective d →
      ∀ (M : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) K),
        M.charpoly = ∏ a : Fin (3 : ℕ), (Polynomial.X - (Polynomial.C : K → Polynomial K) (d a)) →
          ∃ (h : GL (Fin (3 : ℕ)) K),
            (↑h⁻¹ : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) K) * M * (↑h : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) K) =
              Matrix.diagonal d := by
  intro K _ d hd M hM
  have hev : ∀ a, Module.End.HasEigenvalue (Matrix.toLin' M) (d a) := by
    intro a
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM,
      Polynomial.IsRoot.def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp)
  choose v hv using fun a => (hev a).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' M) d hd v hv
  let P : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => v j i
  have hP : IsUnit P := Matrix.linearIndependent_cols_iff_isUnit.mp hli
  have hMP : M * P = P * Matrix.diagonal d := by
    ext i j
    have h := congrFun (hv j).apply_eq_smul i
    rw [Matrix.toLin'_apply] at h
    rw [Matrix.mul_diagonal, mul_comm]
    exact h
  obtain ⟨u, hu⟩ := hP
  refine ⟨u, ?_⟩
  rw [Matrix.mul_assoc, hu, hMP, ← hu, ← Matrix.mul_assoc]
  rw [Units.inv_mul, Matrix.one_mul]
