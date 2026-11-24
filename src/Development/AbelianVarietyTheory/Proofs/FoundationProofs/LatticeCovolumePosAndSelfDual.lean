module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.PlaneLattice

theorem signedArea_ne_zero (L : PeriodPair) : ((starRingEnd ℂ) L.ω₁ * L.ω₂).im ≠ 0 := by
  intro h0
  have hind := LinearIndependent.pair_iff.mp L.indep
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h0
  have hy := hind L.ω₂.im (-L.ω₁.im) (by
    refine Complex.ext ?_ ?_ <;>
      simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul,
        Complex.zero_re, Complex.zero_im]
    · linear_combination h0
    · ring)
  have hy₁ : L.ω₁.im = 0 := neg_eq_zero.mp hy.2
  have hx := hind L.ω₂.re (-L.ω₁.re) (by
    refine Complex.ext ?_ ?_ <;>
      simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul,
        Complex.zero_re, Complex.zero_im]
    · ring
    · rw [hy₁, hy.1]; ring)
  have hω : L.ω₁ = 0 := Complex.ext (by simpa using neg_eq_zero.mp hx.2) (by simpa using hy₁)
  exact one_ne_zero (hind 1 0 (by simp [hω])).1

theorem exists_int_mul (L : PeriodPair) {w₁ w₂ : ℂ} (h₁ : w₁ ∈ L.lattice) (h₂ : w₂ ∈ L.lattice) :
    ∃ k : ℤ, ((starRingEnd ℂ) w₁ * w₂).im = k * ((starRingEnd ℂ) L.ω₁ * L.ω₂).im := by
  obtain ⟨a, b, rfl⟩ := PeriodPair.mem_lattice.mp h₁
  obtain ⟨c, d, rfl⟩ := PeriodPair.mem_lattice.mp h₂
  refine ⟨a * d - b * c, ?_⟩
  simp only [map_add (f := _), map_mul, map_intCast, Complex.mul_im, Complex.mul_re, Complex.add_im,
    Complex.add_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re, Complex.conj_im]
  push_cast
  ring

theorem area_eq (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z : ℂ, z ∈ Λ ↔ z ∈ L.lattice) :
    area Λ = |((starRingEnd ℂ) L.ω₁ * L.ω₂).im| := by
  have hA := signedArea_ne_zero L
  unfold Formalism.MainNotions.TaylorLogMetric.area
  refine IsLeast.csInf_eq ⟨⟨abs_pos.mpr hA, L.ω₁, (h _).mpr L.ω₁_mem_lattice, L.ω₂,
    (h _).mpr L.ω₂_mem_lattice, rfl⟩, ?_⟩
  rintro a ⟨ha, w₁, hw₁, w₂, hw₂, rfl⟩
  obtain ⟨k, hk⟩ := exists_int_mul L ((h _).mp hw₁) ((h _).mp hw₂)
  rw [hk, abs_mul] at ha ⊢
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at ha
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
  exact le_mul_of_one_le_left (abs_nonneg _) hk1

private theorem mul_signedArea_eq_periodPair_combination (L : PeriodPair) (z : ℂ) :
    z * (((starRingEnd ℂ) L.ω₁ * L.ω₂).im : ℂ) =
      (((starRingEnd ℂ) z * L.ω₂).im : ℂ) * L.ω₁ + (((starRingEnd ℂ) L.ω₁ * z).im : ℂ) * L.ω₂ := by
  refine Complex.ext ?_ ?_ <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring

theorem area_pos_and_selfDual : ∀ (L : PeriodPair) (Λ : AddSubgroup ℂ), (∀ z : ℂ, z ∈ Λ ↔ z ∈ L.lattice) → 0 < area Λ ∧ ∀ z : ℂ, z ∈ Λ ↔ ∀ w ∈ Λ, ∃ m : ℤ, (z * (starRingEnd ℂ) w).im / area Λ = m := by
  intro L Λ h
  have hA := signedArea_ne_zero L
  rw [area_eq L Λ h]
  refine ⟨abs_pos.mpr hA, fun z => ⟨fun hz w hw => ?_, fun hz => ?_⟩⟩
  · obtain ⟨k, hk⟩ := exists_int_mul L ((h _).mp hw) ((h _).mp hz)
    rw [mul_comm, hk]
    rcases abs_cases ((starRingEnd ℂ) L.ω₁ * L.ω₂).im with ⟨hab, _⟩ | ⟨hab, _⟩
    · exact ⟨k, by rw [hab, mul_div_cancel_right₀ _ hA]⟩
    · exact ⟨-k, by rw [hab, Int.cast_neg, div_neg, mul_div_cancel_right₀ _ hA]⟩
  · obtain ⟨m, hm⟩ := hz L.ω₂ ((h _).mpr L.ω₂_mem_lattice)
    obtain ⟨n, hn⟩ := hz L.ω₁ ((h _).mpr L.ω₁_mem_lattice)
    have habs : |((starRingEnd ℂ) L.ω₁ * L.ω₂).im| ≠ 0 := abs_ne_zero.mpr hA
    rw [div_eq_iff habs] at hm hn
    have key := mul_signedArea_eq_periodPair_combination L z
    have e1 : ((starRingEnd ℂ) z * L.ω₂).im = -(z * (starRingEnd ℂ) L.ω₂).im := by
      simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    have e2 : ((starRingEnd ℂ) L.ω₁ * z).im = (z * (starRingEnd ℂ) L.ω₁).im := by
      rw [mul_comm]
    rw [e1, e2, hm, hn] at key
    have hA' : ((((starRingEnd ℂ) L.ω₁ * L.ω₂).im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hA
    rw [h, PeriodPair.mem_lattice]
    rcases abs_cases ((starRingEnd ℂ) L.ω₁ * L.ω₂).im with ⟨hab, _⟩ | ⟨hab, _⟩
    · refine ⟨-m, n, mul_right_cancel₀ hA' ?_⟩
      rw [key, hab]
      push_cast
      ring
    · refine ⟨m, -n, mul_right_cancel₀ hA' ?_⟩
      rw [key, hab]
      push_cast
      ring

end GlobalTheory.PlaneLattice
