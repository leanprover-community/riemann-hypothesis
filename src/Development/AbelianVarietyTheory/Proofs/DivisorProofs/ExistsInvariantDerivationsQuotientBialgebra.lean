module

public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantDerivationOfCounitalComul
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped TensorProduct

namespace GlobalTheory

theorem quotient_base_change_invariant_derivations :
    ∀ (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] (I : Ideal O) (d : ℕ) (l : Fin d → (A →ₗ[O] O ⧸ I)), (∀ i a b, l i (a * b) = Coalgebra.counit (R := O) a • l i b + Coalgebra.counit (R := O) b • l i a) → ∃ D : Fin d → Derivation (O ⧸ I) ((O ⧸ I) ⊗[O] A) ((O ⧸ I) ⊗[O] A), ∀ i a, Bialgebra.counitAlgHom (O ⧸ I) ((O ⧸ I) ⊗[O] A) (D i (1 ⊗ₜ a)) = l i a := by
  intro O A _ _ _ I d l hl
  set S := O ⧸ I
  set B := S ⊗[O] A
  let ε := Bialgebra.counitAlgHom S B
  let Δ := Bialgebra.comulAlgHom S B
  have hεt : ∀ (s : S) (a : A), ε (s ⊗ₜ a) = Coalgebra.counit (R := O) a • s := by
    intro s a
    show Coalgebra.counit (R := S) (s ⊗ₜ[O] a) = _
    rw [TensorProduct.counit_tmul]
    rfl
  have hε : (∀ b : B, TensorProduct.lid S B (LinearMap.rTensor B ε.toLinearMap (Δ b)) = b) ∧
      (∀ b : B, TensorProduct.rid S B (LinearMap.lTensor B ε.toLinearMap (Δ b)) = b) := by
    constructor
    · intro b
      have := Coalgebra.rTensor_counit_comul (R := S) b
      show TensorProduct.lid S B (LinearMap.rTensor B Coalgebra.counit (Coalgebra.comul b)) = b
      rw [this]; simp
    · intro b
      have := Coalgebra.lTensor_counit_comul (R := S) b
      show TensorProduct.rid S B (LinearMap.lTensor B Coalgebra.counit (Coalgebra.comul b)) = b
      rw [this]; simp
  have key : ∀ i, ∃ D : Derivation S B B, ∀ b, ε (D b) = LinearMap.liftBaseChange S (l i) b := by
    intro i
    refine invariant_derivation_exists S B ε Δ hε (LinearMap.liftBaseChange S (l i)) ?_
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s a =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul t c =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, hεt, hεt]
        rw [LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul,
          LinearMap.liftBaseChange_tmul, hl]
        simp only [smul_eq_mul, smul_add, Algebra.smul_def]
        ring
      | add y₁ y₂ ih₁ ih₂ =>
        rw [mul_add, map_add (f := _), ih₁, ih₂, map_add (f := _), map_add (f := _)]
        ring
    | add x₁ x₂ ih₁ ih₂ =>
      rw [add_mul, map_add (f := _), ih₁, ih₂, map_add (f := _), map_add (f := _)]
      ring
  choose D hD using key
  refine ⟨D, fun i a => ?_⟩
  rw [hD, LinearMap.liftBaseChange_tmul, one_smul]

end GlobalTheory
