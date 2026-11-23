module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
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

namespace UpperTheory.Reformulated.B.OrderedFlagDiagonal
abbrev M4 (R : Type) : Type := Matrix (Fin 4) (Fin 4) R

variable {K : Type} [Field K]

theorem ordFlag_diag (c : Fin 4 → K) (hc : Function.Injective c) (X : M4 K)
    (hX : X.charpoly = ∏ j, (Polynomial.X - Polynomial.C (c j))) :
    ∃ P : (M4 K)ˣ, X * (P : M4 K) = (P : M4 K) * Matrix.diagonal c := by
  have hev : ∀ j, Module.End.HasEigenvalue (Matrix.toLin' X) (c j) := by
    intro j
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hX,
      Polynomial.IsRoot, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
  choose v hv using fun j => (hev j).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' X) c hc v hv
  have hU : IsUnit (Matrix.of fun i j => v j i : Matrix (Fin 4) (Fin 4) K) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hli
  obtain ⟨P, hP⟩ := hU
  refine ⟨P, ?_⟩
  rw [hP]
  ext i j
  have h := congrFun (hv j).apply_eq_smul i
  rw [Matrix.toLin'_apply] at h
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simpa [Matrix.mulVec, dotProduct, mul_comm] using h

end UpperTheory.Reformulated.B.OrderedFlagDiagonal
