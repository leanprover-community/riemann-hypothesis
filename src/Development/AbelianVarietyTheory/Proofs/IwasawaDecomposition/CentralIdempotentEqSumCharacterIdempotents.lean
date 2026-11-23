module

public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
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
import Mathlib.Tactic.ENatToNat
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

open Formalism.L2.DIV

namespace GlobalTheory.IdemExpand

theorem coeff_idemOf_eq {G : Type} [Group G] [Fintype G] (X : Finset (G → ℂ)) (t : G) :
    (idemOf X).coeff t = ∑ χ ∈ X, χ 1 / (Fintype.card G : ℂ) * χ t⁻¹ := by
  classical
  simp only [idemOf, chiIdem, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_single, Finsupp.single_apply]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [Finset.sum_ite_eq' Finset.univ t]
  simp

theorem sum_coeff_mul {G : Type} [Group G] [Fintype G] (x y : MonoidAlgebra ℂ G) (ψ : G → ℂ) :
    ∑ g, (x * y).coeff g * ψ g = ∑ b, y.coeff b * ∑ a, x.coeff a * ψ (a * b) := by
  have h : ∀ g, (x * y).coeff g = ∑ b, x.coeff (g * b⁻¹) * y.coeff b := by
    intro g
    rw [MonoidAlgebra.coeff_mul_apply_right, Finsupp.sum_fintype]
    intro i; simp
  simp only [h, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Fintype.sum_equiv (Equiv.mulRight b⁻¹) _ _ fun g => ?_
  simp only [Equiv.coe_mulRight, inv_mul_cancel_right]
  ring

theorem eq_idemOf_filter : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] [inst_2 : DecidableEq G] (A : Finset (G → ℂ)) (e : MonoidAlgebra ℂ G), (∀ ψ ∈ A, ψ 1 ≠ 0) → (∀ g : G, ∑ ψ ∈ A, ψ 1 * ψ g = if g = 1 then (Fintype.card G : ℂ) else 0) → (∀ ψ ∈ A, ∀ x : G, ψ 1 * ∑ g, e.coeff g * ψ (g * x) = (∑ g, e.coeff g * ψ g) * ψ x) → e * e = e → e = idemOf (A.filter fun ψ => ∑ g, e.coeff g * ψ g = ψ 1) := by
  intro G _ _ _ A e hone hcol hsc hee
  have hn : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h2 : ∀ ψ ∈ A, (∑ g, e.coeff g * ψ g) = 0 ∨ (∑ g, e.coeff g * ψ g) = ψ 1 := by
    intro ψ hψ
    have h := sum_coeff_mul e e ψ
    rw [hee] at h
    have h' : ψ 1 * ∑ b, e.coeff b * ∑ a, e.coeff a * ψ (a * b)
        = (∑ g, e.coeff g * ψ g) * ∑ g, e.coeff g * ψ g := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [mul_left_comm, hsc ψ hψ b]
      ring
    rw [← h] at h'
    by_cases h0 : (∑ g, e.coeff g * ψ g) = 0
    · exact Or.inl h0
    · exact Or.inr (mul_right_cancel₀ h0 h').symm
  refine MonoidAlgebra.ext (Finsupp.ext fun t => ?_)
  have h1 : (Fintype.card G : ℂ) * e.coeff t = ∑ ψ ∈ A, (∑ g, e.coeff g * ψ g) * ψ t⁻¹ := by
    have a1 : ∑ g, e.coeff g * ∑ ψ ∈ A, ψ 1 * ψ (g * t⁻¹) = (Fintype.card G : ℂ) * e.coeff t := by
      simp only [hcol, mul_inv_eq_one, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq' Finset.univ t]
      simp [mul_comm]
    rw [← a1, ← Finset.sum_congr rfl fun ψ hψ => hsc ψ hψ t⁻¹]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ψ _ => Finset.sum_congr rfl fun g _ => ?_
    ring
  apply mul_left_cancel₀ hn
  rw [h1, coeff_idemOf_eq, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun ψ hψ => ?_
  split_ifs with h
  · rw [h]; field_simp
  · rcases h2 ψ hψ with h0 | h0
    · rw [h0, zero_mul]
    · exact absurd h0 h

end GlobalTheory.IdemExpand
