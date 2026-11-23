module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkBern
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkInd
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

theorem UpperTheory.V.AlgebraTools.hkSpan :
    ∀ (R : Type) [CommRing R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H) (w : Perm (Fin n)) (c : Perm (Fin n) → MvPolynomial (Fin n) R),
      ∃ c' : Perm (Fin n) → MvPolynomial (Fin n) R, b.T w * ∑ u, b.th (c u) * b.T u = ∑ u, b.th (c' u) * b.T u := by
  intro R _ n q H _ _ b
  classical
  let S : Submodule R H :=
    { carrier := {h | ∃ c' : Perm (Fin n) → MvPolynomial (Fin n) R, h = ∑ u, b.th (c' u) * b.T u}
      add_mem' := by
        rintro _ _ ⟨c₁, rfl⟩ ⟨c₂, rfl⟩
        exact ⟨c₁ + c₂, by simp [add_mul, Finset.sum_add_distrib]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro r _ ⟨c₁, rfl⟩
        exact ⟨r • c₁, by simp [Finset.smul_sum]⟩ }
  have hone : ∀ x u, b.th x * b.T u ∈ S := by
    intro x u
    refine ⟨Pi.single u x, ?_⟩
    rw [Finset.sum_eq_single u]
    · simp
    · intro v _ hv
      simp [Pi.single_eq_of_ne hv]
    · simp
  have hTT : ∀ a c : Fin n, a.val + 1 = c.val → ∀ x u, b.th x * (b.T (swap a c) * b.T u) ∈ S := by
    intro a c hac x u
    by_cases hlt : u⁻¹ a < u⁻¹ c
    · rw [← b.T_mul a c hac u hlt]
      exact hone _ _
    · have hne : u⁻¹ c ≠ u⁻¹ a := by
        intro e
        have := (u⁻¹).injective e
        rw [this] at hac
        omega
      have hw' : (swap a c * u)⁻¹ a < (swap a c * u)⁻¹ c := by
        rw [mul_inv_rev, swap_inv, Perm.mul_apply, Perm.mul_apply, swap_apply_left, swap_apply_right]
        exact lt_of_le_of_ne (not_lt.mp hlt) hne
      have e := b.T_mul a c hac _ hw'
      rw [swap_mul_self_mul] at e
      have e2 : b.T (swap a c) * b.T u = (q - 1) • b.T u + q • b.T (swap a c * u) := by
        calc b.T (swap a c) * b.T u = (b.T (swap a c) * b.T (swap a c)) * b.T (swap a c * u) := by
              rw [mul_assoc, ← e]
          _ = (q - 1) • b.T u + q • b.T (swap a c * u) := by
              rw [b.T_sq a c hac, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, ← e]
      rw [e2, mul_add, mul_smul_comm, mul_smul_comm]
      exact S.add_mem (S.smul_mem _ (hone _ _)) (S.smul_mem _ (hone _ _))
  have hs : ∀ a c : Fin n, a.val + 1 = c.val → ∀ h ∈ S, b.T (swap a c) * h ∈ S := by
    rintro a c hac _ ⟨c₁, rfl⟩
    rw [Finset.mul_sum]
    refine S.sum_mem fun u _ => ?_
    obtain ⟨y, -, hy⟩ := (UpperTheory.V.AlgebraTools.hkBern R n q H b).1 a c hac (c₁ u)
    rw [← mul_assoc, hy, add_mul, smul_mul_assoc, mul_assoc]
    exact S.add_mem (hTT a c hac _ _) (S.smul_mem _ (hone _ _))
  have key : ∀ w, ∀ h ∈ S, b.T w * h ∈ S := by
    refine UpperTheory.V.AlgebraTools.hkInd n _ ?_ ?_
    · intro h hh
      rwa [b.T_one, one_mul]
    · intro a c hac w hw ih h hh
      rw [b.T_mul a c hac w hw, mul_assoc]
      exact hs a c hac _ (ih h hh)
  intro w c
  exact key w _ ⟨c, rfl⟩
