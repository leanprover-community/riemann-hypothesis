module

public import Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open GlobalTheory.SgAlg Matrix

namespace GlobalTheory.SgAlg

theorem isField_or_exists_idempotent_of_isQA {E : Type} [CommRing E] (σ : E →+* E) (h : IsQA σ) :
    IsField E ∨ ∃ e : E, e * e = e ∧ e + σ e = 1 ∧ ∀ x : E, e * x ≠ 0 → ∃ y, e * x * y = e := by
  obtain ⟨hinv, ⟨x₀, hx₀⟩, hred, -, hunit⟩ := h
  by_cases hN : ∀ y : E, y ≠ 0 → y * σ y ≠ 0
  · left
    refine ⟨⟨σ x₀, x₀, hx₀⟩, mul_comm, ?_⟩
    intro y hy
    have hfix : σ (y * σ y) = y * σ y := by
      rw [map_mul, hinv, mul_comm]
    obtain ⟨u, hu⟩ := hunit _ hfix (hN y hy)
    refine ⟨σ y * (↑u⁻¹ : E), ?_⟩
    rw [← mul_assoc, ← hu]
    exact u.mul_inv
  · right
    push Not at hN
    obtain ⟨y, hy, hyy⟩ := hN
    have hsfix : σ (y + σ y) = y + σ y := by
      rw [map_add (f := _), hinv, add_comm]
    have hs : y + σ y ≠ 0 := by
      intro h0
      have h1 : σ y = -y := eq_neg_of_add_eq_zero_right h0
      rw [h1] at hyy
      have h2 : y ^ 2 = 0 := by
        have : y * y = 0 := by simpa using hyy
        rw [pow_two, this]
      exact hy (pow_eq_zero_iff (two_ne_zero) |>.mp h2)
    obtain ⟨s, hs'⟩ := hunit _ hsfix hs
    have hsum : (↑s⁻¹ : E) * (y + σ y) = 1 := by rw [← hs', Units.inv_mul]
    have hσs : σ (↑s⁻¹ : E) * (y + σ y) = 1 := by
      have : σ ((↑s⁻¹ : E) * (y + σ y)) = 1 := by
        rw [hsum, map_one]
      rwa [map_mul, hsfix] at this
    have hσs' : σ (↑s⁻¹ : E) = ↑s⁻¹ := by
      calc σ (↑s⁻¹ : E) = σ (↑s⁻¹ : E) * ((y + σ y) * ↑s⁻¹) := by
            rw [mul_comm (y + σ y), hsum, mul_one]
        _ = ↑s⁻¹ := by rw [← mul_assoc, hσs, one_mul]
    set e : E := y * ↑s⁻¹ with he
    have hσe : σ e = σ y * ↑s⁻¹ := by rw [he, map_mul, hσs']
    have hadd : e + σ e = 1 := by
      rw [hσe, he, ← add_mul, mul_comm]; exact hsum
    have horth : e * σ e = 0 := by
      rw [hσe, he]
      calc y * ↑s⁻¹ * (σ y * ↑s⁻¹) = (y * σ y) * (↑s⁻¹ * ↑s⁻¹) := by ring
        _ = 0 := by rw [hyy, zero_mul]
    have hidem : e * e = e := by
      have : e * (e + σ e) = e := by rw [hadd, mul_one]
      rwa [mul_add, horth, add_zero] at this
    refine ⟨e, hidem, hadd, ?_⟩
    intro x hx
    have hufix : σ (e * x + σ (e * x)) = e * x + σ (e * x) := by
      rw [map_add (f := _), hinv, add_comm]
    have heu : e * (e * x + σ (e * x)) = e * x := by
      rw [map_mul, mul_add, ← mul_assoc, hidem, ← mul_assoc, horth, zero_mul, add_zero]
    have hu0 : e * x + σ (e * x) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at heu
      exact hx heu.symm
    obtain ⟨u, hu⟩ := hunit _ hufix hu0
    refine ⟨↑u⁻¹, ?_⟩
    rw [← heu, ← hu, mul_assoc, u.mul_inv, mul_one]

end GlobalTheory.SgAlg
