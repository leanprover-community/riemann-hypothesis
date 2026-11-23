module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitMulPowOfMaximalIdealEqSpan
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Filtration

@[expose] public section

open IsLocalRing

namespace GlobalTheory

theorem eq_pow_mul_unit_of_maximalIdeal_eq_span {V : Type} [CommRing V] [IsLocalRing V]
    [IsNoetherianRing V] (T : V) (hm : maximalIdeal V = Ideal.span {T}) (v : V) (hv : v ≠ 0) :
    ∃ (a : ℕ) (c : V), IsUnit c ∧ v = T ^ a * c := by
  apply GlobalTheory.Pat.unit_mul_pow_of_maximalIdeal_eq_span <;> assumption

theorem maximalIdeal_eq_span_map_of_fractions (V W : Type) [CommRing V] [IsLocalRing V]
    [IsNoetherianRing V] [CommRing W] [IsLocalRing W] (φ : V →+* W) (T : V)
    (hm : IsLocalRing.maximalIdeal V = Ideal.span {T})
    (hTm : φ T ∈ IsLocalRing.maximalIdeal W) (hTn : φ T ∈ nonZeroDivisors W)
    (hfrac : ∀ w : W, ∃ x z : V, φ z ∈ nonZeroDivisors W ∧ φ z * w = φ x) :
    IsLocalRing.maximalIdeal W = Ideal.span {φ T} := by
  have cancel : ∀ (n : ℕ) (y : W), φ T ^ n * y = 0 → y = 0 := fun n y h =>
    (mul_left_mem_nonZeroDivisors_eq_zero_iff (pow_mem hTn n)).mp h
  have surj : ∀ w : W, ∃ v : V, φ v = w := by
    intro w
    obtain ⟨x, z, hz, hzw⟩ := hfrac w
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [map_zero] at hz
      have h1 : (1 : W) = 0 :=
        (mul_left_mem_nonZeroDivisors_eq_zero_iff hz).mp (zero_mul 1)
      exact one_ne_zero h1
    by_cases hx : x = 0
    · refine ⟨0, ?_⟩
      rw [hx, map_zero] at hzw
      rw [map_zero, eq_comm]
      exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hz).mp hzw
    obtain ⟨a, α, hα, rfl⟩ := eq_pow_mul_unit_of_maximalIdeal_eq_span T hm x hx
    obtain ⟨c, β, hβ, rfl⟩ := eq_pow_mul_unit_of_maximalIdeal_eq_span T hm z hz0
    obtain ⟨βi, hβi⟩ := hβ.exists_right_inv
    simp only [map_mul, map_pow] at hzw
    rcases le_or_gt c a with h | h
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      refine ⟨βi * T ^ d * α, ?_⟩
      have h1 : φ β * w = φ T ^ d * φ α := by
        apply sub_eq_zero.mp
        apply cancel c
        linear_combination hzw
      have h2 : φ βi * φ β = 1 := by rw [← map_mul, mul_comm, hβi, map_one]
      calc φ (βi * T ^ d * α) = φ βi * (φ T ^ d * φ α) := by simp only [map_mul, map_pow]; ring
        _ = φ βi * (φ β * w) := by rw [h1]
        _ = w := by rw [← mul_assoc, h2, one_mul]
    · exfalso
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
      have h1 : φ T ^ (d + 1) * φ β * w = φ α := by
        apply sub_eq_zero.mp
        apply cancel a
        linear_combination hzw
      have hmem : φ T ^ (d + 1) * φ β * w ∈ maximalIdeal W := by
        rw [mul_assoc]
        exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hTm _ (Nat.succ_pos d))
      rw [h1, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmem
      exact hmem (hα.map φ)
  ext w
  constructor
  · intro hw
    obtain ⟨v, rfl⟩ := surj w
    have hv : v ∈ maximalIdeal V := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hw
      exact hw (hu.map φ)
    rw [hm] at hv
    obtain ⟨v', rfl⟩ := Ideal.mem_span_singleton'.mp hv
    rw [map_mul, Ideal.mem_span_singleton']
    exact ⟨φ v', rfl⟩
  · intro hw
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hw
    exact Ideal.mul_mem_left _ _ hTm

end GlobalTheory
