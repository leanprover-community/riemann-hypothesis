module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CstSApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem sdSet_eq_sum_add_mul (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) :
    ∀ F ∈ SdSet t K e, ∃ (N : ℕ) (v : ℕ → Wq l a), ∃ y ∈ SdSet t K e,
      F = ∑ n ∈ Finset.range N, cstS t K (v n) * dpS a e n + (l : ZMod a → K⟦X⟧) * y := by
  rintro F ⟨w, hw, hF⟩
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hl0 : (l : Wq l a) ≠ 0 := by
    have h := WittVector.p_nonzero l (Fq l a)
    exact h
  have h1 := hw 1
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop] at h1
  obtain ⟨N, hN⟩ := h1
  have h2 : ∀ n, ∃ z : Wq l a, (n < N → z = 0) ∧ (¬ n < N → w n = l * z) := by
    intro n
    by_cases h : n < N
    · exact ⟨0, fun _ => rfl, fun h' => absurd h h'⟩
    · obtain ⟨z, hz⟩ := hN n (not_lt.1 h)
      exact ⟨z, fun h' => absurd h' h, fun _ => by rw [hz, pow_one]⟩
  choose z hz0 hz using h2
  have hfac : ∀ n : ℕ, ((n / e).factorial : K) ≠ 0 := fun n => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  refine ⟨N, w, fun τ => PowerSeries.mk fun n => ((n / e).factorial : K)⁻¹ * algebraMap O K (emb t τ (z n)),
    ⟨z, fun r => ?_, fun τ n => ?_⟩, ?_⟩
  · filter_upwards [hw (r + 1)] with n hn
    by_cases h : n < N
    · rw [hz0 n h]; exact dvd_zero _
    · rw [hz n h, pow_succ'] at hn
      exact (mul_dvd_mul_iff_left hl0).1 hn
  · rw [coeff_mk, mul_inv_cancel_left₀ (hfac n)]
  · funext τ
    ext m
    apply mul_left_cancel₀ (hfac m)
    rw [hF]
    have hc : (l : K⟦X⟧) = C (l : K) := (map_natCast (C : K →+* K⟦X⟧) l).symm

    simp only [Pi.add_apply, Finset.sum_apply, Pi.mul_apply, Pi.natCast_apply, map_add (f := _), map_sum, cstS_apply, dpS,
    hc, coeff_C_mul, coeff_monomial, coeff_mk, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
    by_cases h : m < N
    · rw [if_pos h, hz0 m h, map_zero, map_zero]
      field_simp [hfac m]
      ring
    · rw [if_neg h, hz m h, map_mul, map_mul, map_natCast, map_natCast]
      field_simp [hfac m]
      ring

end GlobalTheory.CrysPrism
