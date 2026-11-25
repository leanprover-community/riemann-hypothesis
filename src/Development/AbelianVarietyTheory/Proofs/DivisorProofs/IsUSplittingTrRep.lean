module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Matrix

namespace GlobalTheory.WeilTr

open GlobalTheory.WeilM

variable {R : Type} [CommRing R] {κ : Type} [Fintype κ]

def trRep {G : Type} [Group G] (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) (om : G →* Module.End ℂ ((κ → R) → ℂ)) :
    G →* Module.End ℂ ((κ → R) → ℂ) where
  toFun g := T.toLinearMap ∘ₗ om g ∘ₗ T.symm.toLinearMap
  map_one' := by
    ext φ x
    simp
  map_mul' g h := by
    ext φ x
    simp

variable [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R}

def IsGoodInt [TopologicalSpace R] (C : TestClass R) (ψ : AddChar R ℂ) (d d₁ : Darboux B κ)
    (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) : Prop :=
  (∀ φ, φ ∈ C.sp κ ↔ T φ ∈ C.sp κ) ∧
  (∀ w, ∀ φ ∈ C.sp κ, T (d.rho ψ w φ) = d₁.rho ψ w (T φ)) ∧
  (∀ l : ((κ → R) → ℂ) →ₗ[ℂ] ℂ, l ∈ C.adm κ ↔ l ∘ₗ T.toLinearMap ∈ C.adm κ) ∧
  ∀ μ : @Measure (κ → R) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ c : ℝ≥0∞, ∀ φ ∈ C.sp κ, ∫⁻ x, ‖T φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ

section Dbl

variable {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
  [DecidableEq β]

def HasDbl [TopologicalSpace R] (C : TestClass R) (ψ : AddChar R ℂ) (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E)
    (d d₁ : Darboux (symp c ξ JA JB) κ) (T : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)) : Prop :=
  ∀ dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ), IsDblCoord c ξ JA JB d dd →
    ∃ (dd₁ : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)) (Td : ((κ ⊕ κ → R) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ → R) → ℂ))
      (S : ((κ → R) → ℂ) ≃ₗ[ℂ] ((κ → R) → ℂ)), IsDblCoord c ξ JA JB d₁ dd₁ ∧ IsGoodInt C ψ dd dd₁ Td ∧
      (∀ φ, φ ∈ C.sp κ ↔ S φ ∈ C.sp κ) ∧
      ∀ φ₁ ∈ C.sp κ, ∀ φ₂ ∈ C.sp κ, Td (boxFun φ₁ φ₂) = boxFun (T φ₁) (S φ₂)

end Dbl

theorem symp_transpose {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type}
    [Fintype α] [Fintype β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix β α E) :
    symp c ξ JB JA x y = symp c ξ JA JB xᵀ yᵀ := by
  unfold symp hTens
  congr 2
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.transpose_apply]
  ring

def transpCoord {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
    {α β : Type} [Fintype α] [Fintype β] {κ : Type} [Fintype κ] {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}
    (d : Darboux (symp c ξ JA JB) κ) : Darboux (symp c ξ JB JA) κ where
  e := (Matrix.transposeLinearEquiv β α R E).trans d.e
  form w w' := by
    rw [symp_transpose, d.form]
    rfl

end GlobalTheory.WeilTr

end
