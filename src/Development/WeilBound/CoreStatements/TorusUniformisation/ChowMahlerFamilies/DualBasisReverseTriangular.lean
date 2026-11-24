module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

namespace PositivityTheory.Xgn.DualReverseTriangular

theorem repr_eq_dot {Ω : Type} [Field Ω] {r : ℕ} (w v : Module.Basis (Fin r) Ω (Fin r → Ω))
    (h : ∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0) (z : Fin r → Ω) (j : Fin r) :
    v.repr z j = w j.rev ⬝ᵥ z := by
  conv_rhs => rw [← v.sum_repr z]
  rw [dotProduct_sum]
  simp only [dotProduct_smul, h, Fin.rev_inj, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

theorem repr_eq_dot' {Ω : Type} [Field Ω] {r : ℕ} (w v : Module.Basis (Fin r) Ω (Fin r → Ω))
    (h : ∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0) (z : Fin r → Ω) (j : Fin r) :
    w.repr z j.rev = z ⬝ᵥ v j := by
  conv_rhs => rw [← w.sum_repr z]
  rw [sum_dotProduct]
  simp only [smul_dotProduct, h, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

theorem tri_inv {Ω : Type} [Field Ω] {r : ℕ} (w w' : Module.Basis (Fin r) Ω (Fin r → Ω))
    (h : ∀ i j, i < j → w.repr (w' i) j = 0) :
    (∀ i j, i < j → w'.repr (w i) j = 0) ∧ ∀ i, w'.repr (w i) i * w.repr (w' i) i = 1 := by
  have hAB := w.toMatrix_mul_toMatrix_flip w'
  have hBA := w'.toMatrix_mul_toMatrix_flip w
  letI : Invertible (w.toMatrix w') := ⟨w'.toMatrix w, hBA, hAB⟩
  have hA : (w.toMatrix w').BlockTriangular id := by
    intro i j hji
    rw [Module.Basis.toMatrix_apply]
    exact h j i hji
  have hB : (w'.toMatrix w).BlockTriangular id := by
    have hinv := Matrix.blockTriangular_inv_of_blockTriangular hA
    rwa [Matrix.inv_eq_right_inv hAB] at hinv
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · simpa [Module.Basis.toMatrix_apply] using hB hij
  · have e := congrFun (congrFun hBA i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at e
    · simpa [Module.Basis.toMatrix_apply] using e
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hlt | hlt
      · rw [hB hlt, zero_mul]
      · rw [hA hlt, mul_zero]
    · simp

end PositivityTheory.Xgn.DualReverseTriangular

theorem PositivityTheory.Xgn.dual_basis_reverse_triangular : ∀ (Ω : Type) [Field Ω] (r : ℕ) (w w' v v' : Module.Basis (Fin r) Ω (Fin r → Ω)),
    (∀ i j, w i ⬝ᵥ v j = if i = j.rev then 1 else 0) → (∀ i j, w' i ⬝ᵥ v' j = if i = j.rev then 1 else 0) →
    (∀ i j, i < j → w.repr (w' i) j = 0) →
    (∀ i j, i < j → v.repr (v' i) j = 0) ∧ ∀ i, v.repr (v' i) i * w.repr (w' i.rev) i.rev = 1 := by
  intro Ω _ r w w' v v' h h' ht
  obtain ⟨h1, h2⟩ := PositivityTheory.Xgn.DualReverseTriangular.tri_inv w w' ht
  have key : ∀ i j, v.repr (v' i) j = w'.repr (w j.rev) i.rev := fun i j => by
    rw [PositivityTheory.Xgn.DualReverseTriangular.repr_eq_dot w v h,
      PositivityTheory.Xgn.DualReverseTriangular.repr_eq_dot' w' v' h']
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [key]
    exact h1 _ _ (Fin.rev_lt_rev.mpr hij)
  · rw [key]
    exact h2 _
