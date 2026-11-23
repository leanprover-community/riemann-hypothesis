module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.WeaklyAdmissibleFiltrations.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

theorem UpperTheory.exists_square_submatrix_det_ne_zero_of_left_inverse :
    ∀ {B : Type} [CommRing B] [IsDomain B] {d r : ℕ} (X : Matrix (Fin d) (Fin r) B) (Z : Matrix (Fin r) (Fin d) B), Z * X = 1 → ∃ s : Fin r → Fin d, (X.submatrix s id).det ≠ 0 := by
  intro B _ _ d r X Z hZX
  classical
  by_contra h
  push_neg at h
  have hM : (Z * X) = fun a => ∑ k, Z a k • X k := by
    funext a b
    simp [Matrix.mul_apply, Finset.sum_apply, smul_eq_mul]
  have key : (Z * X).det = ∑ s : Fin r → Fin d, (∏ a, Z a (s a)) * (X.submatrix s id).det := by
    have e1 : (Z * X).det = Matrix.detRowAlternating (fun a => ∑ k, Z a k • X k) := by
      rw [← hM]
      rfl
    rw [e1]
    have e2 := (Matrix.detRowAlternating : (Fin r → B) [⋀^Fin r]→ₗ[B] B).toMultilinearMap.map_sum
      (fun a k => Z a k • X k)
    simp only [AlternatingMap.coe_multilinearMap] at e2
    rw [e2]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have e3 := (Matrix.detRowAlternating : (Fin r → B) [⋀^Fin r]→ₗ[B] B).toMultilinearMap.map_smul_univ
      (fun a => Z a (s a)) (fun a => X (s a))
    simp only [AlternatingMap.coe_multilinearMap, smul_eq_mul] at e3
    rw [e3]
    rfl
  have h0 : (Z * X).det = 0 := by
    rw [key]
    exact Finset.sum_eq_zero (fun s _ => by rw [h s, mul_zero])
  rw [hZX, Matrix.det_one] at h0
  exact one_ne_zero h0
