module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem Reg.not_modEq_of_lt {q N k u v : ℕ} (hq : 2 ≤ q) (h : Reg q N k) (huv : u < v) (hv : v < u + N) :
    ¬ k * q ^ v ≡ k * q ^ u [MOD q ^ N - 1] := by
  intro hmod
  obtain ⟨d, rfl⟩ : ∃ d, v = u + d := ⟨v - u, by omega⟩
  have hd0 : 0 < d := by omega
  have hdN : d < N := by omega
  have hN : 0 < N := by omega
  have hcop : Nat.Coprime (q ^ N - 1) (q ^ u) := by
    obtain ⟨t, ht⟩ : ∃ t, q ^ N = t + 1 := ⟨q ^ N - 1, by have := Nat.one_le_pow N q (by omega); omega⟩
    have h2 : Nat.Coprime (q ^ N - 1) (q ^ N) := by
      rw [ht, Nat.add_sub_cancel]
      exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right t)
    exact (h2.coprime_dvd_right (dvd_pow_self q hN.ne')).pow_right u
  have key : k * q ^ d ≡ k [MOD q ^ N - 1] := by
    apply Nat.ModEq.cancel_right_of_coprime (c := q ^ u) hcop
    have e : k * q ^ d * q ^ u = k * q ^ (u + d) := by ring
    rw [e]
    exact hmod
  exact h d hd0 hdN key

theorem reg_step_of_dvd : ∀ q l m k : ℕ, 2 ≤ q → 0 < l → 0 < m → Reg q (l * m) k →
    (∀ i, Reg (q ^ l) m (k * q ^ i)) ∧ (2 ≤ l * m → ∀ i, ¬ k * q ^ i ≡ 0 [MOD q ^ (l * m) - 1]) ∧
    ∀ i j a, i < l → j < l → a < m →
      (k * q ^ i * (q ^ l) ^ a ≡ k * q ^ j [MOD (q ^ l) ^ m - 1] ↔ i = j ∧ a = 0) := by
  intro q l m k hq hl hm h
  refine ⟨?_, ?_, ?_⟩
  · intro i j hj0 hjm hmod
    simp only [← pow_mul] at hmod
    rw [mul_assoc, ← pow_add] at hmod
    have hlj : 0 < l * j := Nat.mul_pos hl hj0
    have hljm : l * j < l * m := (Nat.mul_lt_mul_left hl).mpr hjm
    exact Reg.not_modEq_of_lt hq h (by omega : i < i + l * j) (by omega : i + l * j < i + l * m) hmod
  · intro hlm i hmod
    have h1 : k * q ^ (i + 1) ≡ k * q ^ i [MOD q ^ (l * m) - 1] := by
      have e : k * q ^ (i + 1) = k * q ^ i * q := by ring
      rw [e]
      have h0 := hmod.mul_right q
      rw [zero_mul] at h0
      exact h0.trans hmod.symm
    exact Reg.not_modEq_of_lt hq h (by omega : i < i + 1) (by omega : i + 1 < i + l * m) h1
  · intro i j a hi hj ha
    constructor
    · intro hmod
      simp only [← pow_mul] at hmod
      rw [mul_assoc, ← pow_add] at hmod
      have hla : l * a + l ≤ l * m := by
        calc l * a + l = l * (a + 1) := by ring
          _ ≤ l * m := Nat.mul_le_mul_left l ha
      rcases lt_trichotomy (i + l * a) j with hlt | heq | hgt
      · exact absurd hmod.symm (Reg.not_modEq_of_lt hq h hlt (by omega))
      · rcases Nat.eq_zero_or_pos a with ha0 | ha0
        · subst ha0
          simp at heq
          exact ⟨heq, rfl⟩
        · have := Nat.le_mul_of_pos_right l ha0
          omega
      · exact absurd hmod (Reg.not_modEq_of_lt hq h hgt (by omega))
    · rintro ⟨rfl, rfl⟩
      simp [Nat.ModEq]

end GlobalTheory.Shin
