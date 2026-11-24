module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.UnitaryGroup
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

@[expose] public section

namespace GlobalTheory.UnitaryUpperTriangular

open Module InnerProductSpace

theorem exists_unitary_mul_upperTriangular {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) :
    ∃ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ (t : Matrix (Fin n) (Fin n) ℂ),
      Matrix.BlockTriangular t id ∧ y = u * t := by
  classical
  let f : Fin n → EuclideanSpace ℂ (Fin n) := fun i => WithLp.toLp 2 (fun k => y k i)
  have h : finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n) := finrank_euclideanSpace
  let a := EuclideanSpace.basisFun (Fin n) ℂ
  let b := gramSchmidtOrthonormalBasis h f
  refine ⟨a.toBasis.toMatrix b, a.toMatrix_orthonormalBasis_mem_unitary b,
    b.toBasis.toMatrix f, gramSchmidtOrthonormalBasis_inv_isUpperTriangular h f, ?_⟩
  rw [← b.coe_toBasis, Basis.toMatrix_mul_toMatrix]
  ext k i
  simp [Basis.toMatrix_apply, a, f]

end GlobalTheory.UnitaryUpperTriangular
