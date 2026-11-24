module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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

namespace GlobalTheory

theorem dvr_pow_mul_eq_unit_mul_pow_unif :
    ∀ (T V : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra T V], Function.Injective (algebraMap T V) →
    ∀ (α : V) (ϖ u : T) (m k : ℕ), Irreducible ϖ → IsUnit u → 0 < k →
    α ^ (m * k) = algebraMap T V (u * ϖ ^ k) →
    ∃ γ : V, IsUnit γ ∧ α ^ m = γ * algebraMap T V ϖ ∧ γ ^ k = algebraMap T V u := by
  intro T V _ _ _ _ _ _ _ hinj α ϖ u m k hϖ hu hk h
  have hw : algebraMap T V ϖ ≠ 0 := by
    intro h0
    apply hϖ.ne_zero
    apply hinj
    rw [h0, map_zero]
  have hu' : IsUnit (algebraMap T V u) := hu.map _
  have hxk : (α ^ m) ^ k = algebraMap T V u * (algebraMap T V ϖ) ^ k := by
    rw [← pow_mul, h, map_mul, map_pow]
  have hwk : (algebraMap T V ϖ) ^ k ≠ 0 := pow_ne_zero _ hw
  rcases ValuationRing.dvd_total (α ^ m) (algebraMap T V ϖ) with ⟨c, hc⟩ | ⟨c, hc⟩
  ·
    have heq : (c ^ k * algebraMap T V u) * (algebraMap T V ϖ) ^ k = 1 * (algebraMap T V ϖ) ^ k := by
      calc c ^ k * algebraMap T V u * (algebraMap T V ϖ) ^ k
          = c ^ k * (α ^ m) ^ k := by rw [hxk]; ring
        _ = (α ^ m * c) ^ k := by ring
        _ = (algebraMap T V ϖ) ^ k := by rw [← hc]
        _ = 1 * (algebraMap T V ϖ) ^ k := by ring
    have h1 := mul_right_cancel₀ hwk heq
    have hc' : IsUnit c := (isUnit_pow_iff hk.ne').mp (IsUnit.of_mul_eq_one _ h1)
    obtain ⟨cu, rfl⟩ := hc'
    refine ⟨↑cu⁻¹, Units.isUnit _, ?_, ?_⟩
    · rw [hc, mul_comm (α ^ m), ← mul_assoc, Units.inv_mul, one_mul]
    · calc ((↑cu⁻¹ : V)) ^ k = (↑cu⁻¹ : V) ^ k * ((↑cu : V) ^ k * algebraMap T V u) := by
            rw [h1, mul_one]
        _ = algebraMap T V u := by
            rw [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  ·
    have heq : c ^ k * (algebraMap T V ϖ) ^ k = algebraMap T V u * (algebraMap T V ϖ) ^ k := by
      rw [← hxk, hc]; ring
    have h1 := mul_right_cancel₀ hwk heq
    exact ⟨c, (isUnit_pow_iff hk.ne').mp (h1 ▸ hu'), by rw [hc, mul_comm], h1⟩

end GlobalTheory
