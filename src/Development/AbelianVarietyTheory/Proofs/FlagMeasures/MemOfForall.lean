module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLocalizedModuleSubtype
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

@[expose] public section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open scoped nonZeroDivisors

namespace GlobalTheory.DegCnt.IdealPow

variable {K : Type} [Field K] [NumberField K] {𝔡 : Ideal (𝓞 K)}

theorem ipow_zero (𝔡 : Ideal (𝓞 K)) : ipow 𝔡 0 = 1 := by
  simp [ipow]

theorem ipow_mul (h : 𝔡 ≠ ⊥) (m n : ℤ) : ipow 𝔡 m * ipow 𝔡 n = ipow 𝔡 (m + n) := by
  have h0 : (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h
  unfold ipow
  rw [zpow_add₀ h0, FractionalIdeal.coe_mul]

theorem mul_mem (h : 𝔡 ≠ ⊥) {m n k : ℤ} (hk : m + n = k) {x y : K} (hx : x ∈ ipow 𝔡 m) (hy : y ∈ ipow 𝔡 n) :
    x * y ∈ ipow 𝔡 k := by
  rw [← hk, ← ipow_mul h]
  exact Submodule.mul_mem_mul hx hy

theorem mul_mem_one (h : 𝔡 ≠ ⊥) {m n : ℤ} (hk : m + n = 0) {x y : K} (hx : x ∈ ipow 𝔡 m) (hy : y ∈ ipow 𝔡 n) :
    x * y ∈ (1 : Submodule (𝓞 K) K) := by
  rw [← ipow_zero 𝔡]
  exact mul_mem h hk hx hy

theorem pow_mem (h : 𝔡 ≠ ⊥) {m : ℤ} {x : K} (hx : x ∈ ipow 𝔡 m) (s : ℕ) : x ^ s ∈ ipow 𝔡 (s * m) := by
  induction s with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul, ipow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
  | succ s ih => rw [pow_succ]; exact mul_mem h (by push_cast; ring) ih hx

theorem mem_of_forall (h : 𝔡 ≠ ⊥) {m n : ℤ} (hk : m + n = 0) {x : K}
    (hx : ∀ y ∈ ipow 𝔡 n, x * y ∈ (1 : Submodule (𝓞 K) K)) : x ∈ ipow 𝔡 m := by
  have h1 : (1 : K) ∈ ipow 𝔡 n * ipow 𝔡 m := by
    rw [ipow_mul h, add_comm, hk, ipow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
  have h2 : ∀ z ∈ ipow 𝔡 n * ipow 𝔡 m, x * z ∈ ipow 𝔡 m := by
    intro z hz
    refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hx a ha)
      rw [← mul_assoc, ← hc, ← Algebra.smul_def]
      exact Submodule.smul_mem _ c hb
    · rw [mul_add]; exact add_mem ha hb
  simpa using h2 1 h1

theorem prod_ipow (h : 𝔡 ≠ ⊥) {ι : Type} (s : Finset ι) (n : ι → ℤ) :
    ∏ i ∈ s, ipow 𝔡 (n i) = ipow 𝔡 (∑ i ∈ s, n i) := by
  induction s using Finset.induction_on with
  | empty => simp [ipow_zero]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, ipow_mul h]

theorem ipow_sum_le (h : 𝔡 ≠ ⊥) {ι : Type} [Fintype ι] (n : ι → ℤ) (J : Submodule (𝓞 K) K)
    (hJ : ∀ α : ι → K, (∀ i, α i ∈ ipow 𝔡 (n i)) → ∏ i, α i ∈ J) : ipow 𝔡 (∑ i, n i) ≤ J := by
  rw [← prod_ipow h]
  have : ∏ i, ipow 𝔡 (n i) = ∏ i, Submodule.span (𝓞 K) (ipow 𝔡 (n i) : Set K) := by simp
  rw [this, Submodule.prod_span, Submodule.span_le]
  intro x hx
  obtain ⟨α, hα, rfl⟩ := (Set.mem_fintype_prod _ _).1 hx
  exact hJ α hα

variable [StarRing K]

theorem star_mem_nat (h : 𝔡 ≠ ⊥) (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (n : ℕ) {x : K}
    (hx : x ∈ ipow 𝔡 n) : star x ∈ ipow 𝔡 n := by
  induction n generalizing x with
  | zero =>
    rw [Nat.cast_zero, ipow_zero] at hx ⊢
    exact GlobalTheory.UnimodQuot.star_mem_one hx
  | succ n ih =>
    rw [Nat.cast_succ, ← ipow_mul h] at hx ⊢
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [star_mul']
      refine Submodule.mul_mem_mul (ih ha) ?_
      simp only [ipow, zpow_one, FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal] at hb ⊢
      obtain ⟨y, hy, rfl⟩ := hb
      exact hs y hy
    · rw [star_add]; exact add_mem ha hb

theorem star_mem (h : 𝔡 ≠ ⊥) (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) {n : ℤ} {x : K}
    (hx : x ∈ ipow 𝔡 n) : star x ∈ ipow 𝔡 n := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · exact star_mem_nat h hs m hx
  · refine mem_of_forall h (neg_add_cancel _) fun y hy => ?_
    have := GlobalTheory.UnimodQuot.star_mem_one (mul_mem_one h (neg_add_cancel _) hx (star_mem_nat h hs m hy))
    rwa [star_mul', star_star] at this

end GlobalTheory.DegCnt.IdealPow
