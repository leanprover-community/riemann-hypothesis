module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.Finiteness.Defs
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.SublatticeFacts

open Matrix

theorem finiteRing_sq_sub_mul_sq_eq_of_card {A : Type} [CommRing A] {S : Subring A} {n : Type} [Fintype n] [DecidableEq n]
    (Λ : Submodule (↥S) (n → A)) (hfg : Submodule.FG Λ)
    (hden : ∀ (v : n → A), ∃ (N : ℕ), (1 : ℕ) ≤ N ∧ (↑N : A) • v ∈ Λ) (X : Matrix n n A) :
    ∃ (N : ℕ), (1 : ℕ) ≤ N ∧ ∀ y ∈ Λ, (↑N : A) • Matrix.mulVec X y ∈ Λ := by
  classical
  obtain ⟨t, rfl⟩ := hfg
  choose f hf1 hf using fun v : n → A => hden (X *ᵥ v)
  refine ⟨∏ v ∈ t, f v, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun v _ => by have := hf1 v; omega)
  · intro y hy
    rw [Nat.cast_smul_eq_nsmul A]
    induction hy using Submodule.span_induction with
    | mem x hx =>
      rw [← Finset.mul_prod_erase t f hx, mul_nsmul, ← Nat.cast_smul_eq_nsmul A (f x)]
      exact Submodule.smul_of_tower_mem _ (∏ v ∈ t.erase x, f v) (hf x)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [Matrix.mulVec_add, smul_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have : X *ᵥ (a • x) = a • (X *ᵥ x) := by
        ext i
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum, Subring.smul_def, mul_left_comm]
      rw [this, smul_comm]
      exact Submodule.smul_mem _ a hx

theorem main : ∀ {A : Type} [inst : CommRing A] {S : Subring A} {n : Type} [inst_1 : Fintype n] [DecidableEq n]
    (Λ : Submodule (↥S) (n → A)), Submodule.FG Λ →
    (∀ (v : n → A), ∃ (N : ℕ), (1 : ℕ) ≤ N ∧ (↑N : A) • v ∈ Λ) →
    ∀ (X : Matrix n n A), ∃ (N : ℕ), (1 : ℕ) ≤ N ∧ ∀ y ∈ Λ, (↑N : A) • Matrix.mulVec X y ∈ Λ :=
  fun Λ hfg hden X => finiteRing_sq_sub_mul_sq_eq_of_card Λ hfg hden X

end GlobalTheory.SublatticeFacts
