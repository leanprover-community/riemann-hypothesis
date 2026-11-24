module

public import Formalism.LocalToGlobal.HermitianForms.PsiZeroNontrivialCharacter
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ComplexRootOfUnityMemRangeOfIsPrimitiveRoot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem lamJ_mem_range_and_pow_eq_one :
    ∀ (k K : Type) [Field k] [Field K] (s : K →+* ℂ) (p : ℕ), p.Prime → Nat.card k = p →
      (∃ ζ : K, IsPrimitiveRoot ζ p) → (∃ ζ : K, IsPrimitiveRoot ζ (p - 1)) →
      ∀ (n : ℕ) (ψ : AddChar k ℂ) (χ : ℕ → MulChar k ℂ) (a t nb skip : ℕ)
        (M : Matrix (Fin n) (Fin n) k),
        (∃ r : K, s r = lamJ ψ χ a t nb skip M) ∧
          (lamJ ψ χ a t nb skip M ≠ 0 → lamJ ψ χ a t nb skip M ^ (p * (p - 1)) = 1) := by
  intro k K _ _ s p hp hk ⟨ζ, hζ⟩ ⟨ξ, hξ⟩ n ψ χ a t nb skip M
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact hp.ne_zero)
  letI : Fintype k := Fintype.ofFinite k
  have hk' : Fintype.card k = p := by rw [← Nat.card_eq_fintype_card]; exact hk
  have hψ : ∀ x : k, ψ x ^ p = 1 := by
    intro x
    rw [← AddChar.map_nsmul_eq_pow, ← hk, card_nsmul_eq_zero', AddChar.map_zero_eq_one]
  have hχ : ∀ (i : ℕ) (x : k), χ i x ≠ 0 → χ i x ^ (p - 1) = 1 := by
    intro i x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx (MulChar.map_zero _)
    rw [← map_pow, ← hk', FiniteField.pow_card_sub_one_eq_one x hx0, map_one]
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hψr : ∀ x : k, ψ x ∈ s.range := fun x =>
    complex_rootOfUnity_mem_range_of_isPrimitiveRoot K s p ζ hp.pos hζ _ (hψ x)
  have hχr : ∀ (i : ℕ) (x : k), χ i x ∈ s.range := by
    intro i x
    by_cases hx : χ i x = 0
    · rw [hx]; exact zero_mem _
    · exact complex_rootOfUnity_mem_range_of_isPrimitiveRoot K s (p - 1) ξ hp1 hξ _ (hχ i x hx)
  unfold lamJ
  refine ⟨?_, ?_⟩
  · exact mul_mem (hψr _) (prod_mem fun i _ => hχr i _)
  · intro h
    have h2 := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul h)
    rw [mul_pow, pow_mul, hψ, one_pow, one_mul, mul_comm p, pow_mul, ← Finset.prod_pow,
      Finset.prod_eq_one (fun i hi => hχ i _ (h2 i hi)), one_pow]

end GlobalTheory
