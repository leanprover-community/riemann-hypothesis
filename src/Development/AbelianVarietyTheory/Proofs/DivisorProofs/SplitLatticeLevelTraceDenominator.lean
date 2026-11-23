module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem exists_int_mul_trace_of_hasLevel {F : Type} [Field F] [NumberField F] {N : ℕ} {𝔞 𝔟 : Frac F} {x : F}
    (h : HasLevel N (split 𝔞 𝔟 x)) {ν c : F} (hν : ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F))
    (hc : c ∈ (1 : Submodule (𝓞 F) F)) : ∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F (ν * c) = n := by
  have h1 : (![0, c] : Fin 2 → F) ∈ stdLat F := by
    intro i _
    fin_cases i
    · exact Submodule.zero_mem _
    · exact hc
  have h2 := (h.1 _ h1).2
  have h3 : ((N : 𝓞 F) • (![0, c] : Fin 2 → F)) 1 - ((N : 𝓞 F) • (![0, c] : Fin 2 → F)) 0 * x = (N : F) * c := by
    simp [Algebra.smul_def]
  rw [h3, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual, FractionalIdeal.mem_dual 𝔞.ne_zero] at h2
  obtain ⟨n, hn⟩ := h2 ν hν
  refine ⟨n, ?_⟩
  have h4 : (N : F) * c * ν = (N : ℚ) • (ν * c) := by
    rw [Algebra.smul_def, map_natCast]; ring
  rw [Algebra.traceForm_apply, h4, map_smul, smul_eq_mul] at hn
  simpa using hn.symm

theorem trace_denominator_of_hasLevel : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (𝔞 𝔟 : Frac F) (x ξ : F), HasLevel N (split 𝔞 𝔟 x) → ξ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) → (∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F ξ = n) ∧ ∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F (ξ * x) = n := by
  intro F _ _ _ N 𝔞 𝔟 x ξ h hξ
  rw [Units.val_mul] at hξ
  refine FractionalIdeal.mul_induction_on hξ (C := fun ξ ↦ (∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F ξ = n) ∧
    ∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F (ξ * x) = n) ?_ ?_
  · intro ν hν β hβ
    have h1 : (![β, β * x] : Fin 2 → F) ∈ split 𝔞 𝔟 x := by
      refine ⟨hβ, ?_⟩
      have : (![β, β * x] : Fin 2 → F) 1 - (![β, β * x] : Fin 2 → F) 0 * x = 0 := by simp
      rw [this]
      exact Submodule.zero_mem (latM 𝔞 : Submodule (𝓞 F) F)
    have h2 := h.2 h1
    refine ⟨exists_int_mul_trace_of_hasLevel h hν (h2 0 trivial), ?_⟩
    rw [mul_assoc]
    exact exists_int_mul_trace_of_hasLevel h hν (h2 1 trivial)
  · rintro a b ⟨⟨m, hm⟩, m', hm'⟩ ⟨⟨n, hn⟩, n', hn'⟩
    refine ⟨⟨m + n, ?_⟩, m' + n', ?_⟩
    · rw [map_add (f := _), mul_add, hm, hn]; push_cast; ring
    · rw [add_mul, map_add (f := _), mul_add, hm', hn']; push_cast; ring

end GlobalTheory.HilbFam
