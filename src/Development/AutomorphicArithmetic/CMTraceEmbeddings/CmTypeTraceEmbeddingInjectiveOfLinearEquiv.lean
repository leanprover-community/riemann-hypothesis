module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.OrientEv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit
public import Development.AutomorphicArithmetic.CMTraceEmbeddings.CmFieldRealTensorBijectiveCmType
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne

@[expose] public section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed UpperTheory.Gal.W2.Seed.Ori
open scoped TensorProduct

theorem UpperTheory.cmType_trace_embedding_injective_of_linearEquiv :
    TraceType → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) {V : Type} [AddCommGroup V] [Module ℚ V] (β : V ≃ₗ[ℚ] (Fin n → E)), Function.Injective (Th (fun τ : Phi A => τ.1) (β : V →ₗ[ℚ] (Fin n → E))) := by
  intro hT E _ _ _ A n V _ _ β z z' h
  have hb := (UpperTheory.cmField_real_tensor_bijective_cmType hT A).1
  set B : V →ₗ[ℚ] (Fin n → E) := (β : V →ₗ[ℚ] (Fin n → E)) with hBdef
  have key : ∀ j (y : ℝ ⊗[ℚ] V) (τ : Phi A), Th (fun τ : Phi A => τ.1) B y (τ, j) =
      ev1 τ.1 ((LinearMap.proj j ∘ₗ B).baseChange ℝ y) := by
    intro j y τ
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r w =>
      rw [Th_tmul, LinearMap.baseChange_tmul, realTensorEvalAlgHom_tmul]
      rfl
    | add a b ha hb' =>
      rw [map_add (f := _), Pi.add_apply, ha, hb', map_add (f := _), map_add (f := _)]
  have hj : ∀ j, (LinearMap.proj j ∘ₗ B).baseChange ℝ z = (LinearMap.proj j ∘ₗ B).baseChange ℝ z' := by
    intro j
    apply hb
    funext τ
    simp only
    rw [← key, ← key, h]
  have hsum : ∀ y : ℝ ⊗[ℚ] (Fin n → E), y = ∑ j, (LinearMap.single ℚ (fun _ : Fin n => E) j).baseChange ℝ
      ((LinearMap.proj j : (Fin n → E) →ₗ[ℚ] E).baseChange ℝ y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r v =>
      simp only [LinearMap.baseChange_tmul, ← TensorProduct.tmul_sum]
      congr 1
      simp [Finset.univ_sum_single v]
    | add a b ha hb' =>
      conv_lhs => rw [ha, hb']
      simp only [map_add (f := _), ← Finset.sum_add_distrib]
  have hc : ∀ j (y : ℝ ⊗[ℚ] V), (LinearMap.proj j : (Fin n → E) →ₗ[ℚ] E).baseChange ℝ (B.baseChange ℝ y) =
      (LinearMap.proj j ∘ₗ B).baseChange ℝ y := by
    intro j y
    rw [LinearMap.baseChange_comp]
    rfl
  have hB : B.baseChange ℝ z = B.baseChange ℝ z' := by
    rw [hsum (B.baseChange ℝ z), hsum (B.baseChange ℝ z')]
    simp only [hc, hj]
  have hid : ((β.symm : (Fin n → E) →ₗ[ℚ] V).baseChange ℝ).comp (B.baseChange ℝ) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hBdef, LinearEquiv.symm_comp, LinearMap.baseChange_id]
  have hl : ∀ x, ((β.symm : (Fin n → E) →ₗ[ℚ] V).baseChange ℝ) (B.baseChange ℝ x) = x :=
    fun x => LinearMap.congr_fun hid x
  rw [← hl z, ← hl z', hB]
