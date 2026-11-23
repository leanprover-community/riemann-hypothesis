module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
public import Mathlib.GroupTheory.GroupAction.Ring
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.ShearLow

theorem main : ∀ (R : Type) [CommRing R] (n : ℕ) (h : (ℕ →₀ R) →ₗ[R] R) (t : ℕ →₀ R), t ∈ low R n → h t = 0 → ∃ ψ : (ℕ →₀ R) ≃ₗ[R] (ℕ →₀ R), (∀ x, ψ x = x + h x • t) ∧ (∀ x, ψ x ∈ low R n ↔ x ∈ low R n) ∧ ∀ j x, ψ x ∈ aff R n j ↔ x ∈ aff R n j := by
  intro R _ n h t ht hht
  have key : ∀ x y : ℕ →₀ R, y ∈ low R n → (x + y ∈ low R n ↔ x ∈ low R n) := by
    intro x y hy
    simp only [low, Set.mem_setOf_eq, Finsupp.add_apply] at hy ⊢
    constructor
    · intro hx i hi
      have hxi := hx i hi
      rw [hy i hi, add_zero] at hxi
      exact hxi
    · intro hx i hi
      rw [hx i hi, hy i hi, add_zero]
  have hts : ∀ c : R, c • t ∈ low R n := by
    intro c
    simp only [low, Set.mem_setOf_eq, Finsupp.smul_apply] at ht ⊢
    intro i hi
    rw [ht i hi, smul_zero]
  let ψ : (ℕ →₀ R) ≃ₗ[R] (ℕ →₀ R) :=
    { toFun := fun x => x + h x • t
      invFun := fun x => x - h x • t
      map_add' := by
        intro x y
        simp only [map_add (f := _), add_smul]
        abel
      map_smul' := by
        intro c x
        simp only [map_smul, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add]
      left_inv := by
        intro x
        simp only [map_add (f := _), map_smul, hht, smul_eq_mul, mul_zero, add_zero, add_sub_cancel_right]
      right_inv := by
        intro x
        simp only [map_sub, map_smul, hht, smul_eq_mul, mul_zero, sub_zero, sub_add_cancel] }
  have hψ : ∀ x, ψ x = x + h x • t := fun x => rfl
  refine ⟨ψ, hψ, ?_, ?_⟩
  · intro x
    rw [hψ]
    exact key x _ (hts _)
  · intro j x
    rw [hψ]
    simp only [aff, Set.mem_setOf_eq]
    have e : x + h x • t - (Finsupp.single j 1) = (x - Finsupp.single j 1) + h x • t := by abel
    rw [e]
    exact key _ _ (hts _)

end GlobalTheory.ShearLow

section
theorem _root_.GlobalTheory.T.exists_transvection_preserving_low_and_aff : ∀ (R : Type) [CommRing R] (n : ℕ) (h : (ℕ →₀ R) →ₗ[R] R) (t : ℕ →₀ R), t ∈ low R n → h t = 0 → ∃ ψ : (ℕ →₀ R) ≃ₗ[R] (ℕ →₀ R), (∀ x, ψ x = x + h x • t) ∧ (∀ x, ψ x ∈ low R n ↔ x ∈ low R n) ∧ ∀ j x, ψ x ∈ aff R n j ↔ x ∈ aff R n j := by
  first
  | exact @GlobalTheory.ShearLow.main
end
