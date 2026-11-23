module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

theorem UpperTheory.Reformulated.B.Qh30.artin :
    ∀ {P : Type} [inst : Mul P] (T : Finset (P → ℂ))
    (c : (P → ℂ) → ℂ),
    (∀ χ ∈ T, χ ≠ (0 : P → ℂ) ∧ ∀ (p q : P), χ (p * q) = χ p * χ q) →
      (∀ (p : P), ∑ χ ∈ T, c χ * χ p = (0 : ℂ)) → ∀ χ ∈ T, c χ = (0 : ℂ) := by
  intro P inst T
  classical
  induction T using Finset.induction_on with
  | empty => intro c _ _ χ hχ; simp at hχ
  | insert ψ T hψ ih =>
    intro c hT h
    have hψm := hT ψ (Finset.mem_insert_self ψ T)
    have hT' : ∀ χ ∈ T, χ ≠ (0 : P → ℂ) ∧ ∀ (p q : P), χ (p * q) = χ p * χ q :=
      fun χ hχ => hT χ (Finset.mem_insert_of_mem hχ)
    have key : ∀ q : P, ∀ χ ∈ T, c χ * (χ q - ψ q) = 0 := by
      intro q
      refine ih (fun χ => c χ * (χ q - ψ q)) hT' ?_
      intro p
      have h1 := h (q * p)
      have h2 := h p
      rw [Finset.sum_insert hψ] at h1 h2
      have h3 : ∑ χ ∈ T, c χ * (χ q - ψ q) * χ p
          = ∑ χ ∈ T, c χ * χ (q * p) - ψ q * ∑ χ ∈ T, c χ * χ p := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun χ hχ => ?_
        rw [(hT' χ hχ).2]
        ring
      rw [hψm.2] at h1
      rw [h3]
      linear_combination h1 - ψ q * h2
    have hc : ∀ χ ∈ T, c χ = 0 := by
      intro χ hχ
      by_contra hne
      have : χ = ψ := by
        funext q
        exact sub_eq_zero.mp ((mul_eq_zero.mp (key q χ hχ)).resolve_left hne)
      exact hψ (this ▸ hχ)
    have hcψ : c ψ = 0 := by
      by_contra hne
      apply hψm.1
      funext p
      have h2 := h p
      rw [Finset.sum_insert hψ, Finset.sum_eq_zero (fun χ hχ => by rw [hc χ hχ, zero_mul]),
        add_zero] at h2
      exact (mul_eq_zero.mp h2).resolve_left hne
    intro χ hχ
    rcases Finset.mem_insert.mp hχ with rfl | hχ
    · exact hcψ
    · exact hc χ hχ
