module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
import Formalism.LocalRingCardinality.DataTheta
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

namespace GlobalTheory.PolarU


open Kronecker in
theorem abs_det_unitary_mul_mul : ∀ (p q : ℕ), ∀ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∀ V ∈ Matrix.unitaryGroup (Fin q) ℂ, ∀ T : (Fin p → Fin q → ℂ) →ₗ[ℝ] (Fin p → Fin q → ℂ), (∀ B, Matrix.of (T B) = U * Matrix.of B * V) → |LinearMap.det T| = 1 := by
  classical
  intro p q U hU V hV T hT

  let e : (Fin p → Fin q → ℂ) ≃ₗ[ℂ] (Fin q → Fin p → ℂ) :=
    { toFun := fun B j i => B i j
      invFun := fun C i j => C j i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

  let L : (Fin q → Fin p → ℂ) →ₗ[ℂ] (Fin q → Fin p → ℂ) :=
    LinearMap.pi (fun j => (Matrix.toLin' U).comp (LinearMap.proj j))

  let R : (Fin p → Fin q → ℂ) →ₗ[ℂ] (Fin p → Fin q → ℂ) :=
    LinearMap.pi (fun i => (Matrix.toLin' Vᵀ).comp (LinearMap.proj i))
  let C : (Fin p → Fin q → ℂ) →ₗ[ℂ] (Fin p → Fin q → ℂ) :=
    ((e.symm : (Fin q → Fin p → ℂ) →ₗ[ℂ] (Fin p → Fin q → ℂ)) ∘ₗ L ∘ₗ
      (e.symm.symm : (Fin p → Fin q → ℂ) →ₗ[ℂ] (Fin q → Fin p → ℂ))) ∘ₗ R
  have hTC : T = C.restrictScalars ℝ := by
    apply LinearMap.ext
    intro B
    funext i j
    have h := congrFun (congrFun (hT B) i) j
    simp only [Matrix.of_apply] at h
    rw [h, Matrix.mul_assoc]
    simp [C, L, R, e, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
  have hL : LinearMap.det L = U.det ^ q := by
    simp [L, LinearMap.det_pi, LinearMap.det_toLin']
  have hR : LinearMap.det R = V.det ^ p := by
    simp [R, LinearMap.det_pi, LinearMap.det_toLin', Matrix.det_transpose]
  have hC : LinearMap.det C = U.det ^ q * V.det ^ p := by
    simp only [C]
    rw [LinearMap.det_comp, LinearMap.det_conj L e.symm, hL, hR]
  have hu : ‖U.det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hU)
  have hv : ‖V.det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hV)
  rw [hTC, LinearMap.det_restrictScalars, Algebra.norm_complex_apply, hC, map_mul, map_pow,
    map_pow, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hu, hv]
  simp

end GlobalTheory.PolarU
