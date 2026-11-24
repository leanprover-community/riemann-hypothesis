module

public import Formalism.CyclotomicNorms.StatementI
public import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Primality
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace Formalism.BasicNotions.Examples₂

theorem mem_of_dvd_prod_pow {l : ℕ} (hl : l.Prime) (ps : List ℕ) (K : ℕ) (hp : ∀ p ∈ ps, p.Prime)
    (h : l ∣ ps.prod ^ K) : l ∈ ps := by
  have h' : l ∣ ps.prod := (Nat.Prime.prime hl).dvd_of_dvd_pow h
  obtain ⟨p, hps, hlp⟩ := ((Nat.Prime.prime hl).dvd_prod_iff).1 h'
  rwa [(Nat.prime_dvd_prime_iff_eq hl (hp p hps)).1 hlp]

theorem gA_prime : Nat.Prime 413718278401 := by
  primality (cert := .witnesses [
    .lucas { root := 34, primeFactors := [2, 3, 5, 7, 571, 599] }])

theorem gB_prime : Nat.Prime 603339156001 := by
  primality (cert := .witnesses [
    .lucas { root := 17, primeFactors := [2, 3, 5, 7, 571, 599] }])

theorem prime_large : Nat.Prime 65794571027774832745588537266486439382601586586498771901135640963549130131839564588689999034983373394040350895271937 := by
  primality (cert := .witnesses [
    .lucas { root := 5, primeFactors := [2, 3, 571, 599, 413718278401, 603339156001] }]) [gA_prime, gB_prime]

def prodPowSubOne (g : ℕ) : ℕ := ((List.range 9).map fun i => g ^ (i + 1) - 1).prod

theorem exc_dvd {g d l : ℕ} (hg : 1 ≤ g) (h1 : 1 ≤ d) (h9 : d ≤ 9) (h : Formalism.CyclotomicNorms.Exc g d l) : l ∣ prodPowSubOne g := by
  have hv : padicValNat l (g ^ d - 1) ≠ 0 := by
    intro h0
    have := h.2
    rw [h0, mul_zero, pow_zero] at this
    have := Nat.one_le_pow d g hg
    omega
  refine ((dvd_pow_self l hv).trans (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))).trans (List.dvd_prod ?_)
  exact List.mem_map.mpr ⟨d - 1, List.mem_range.mpr (by omega), by rw [Nat.sub_add_cancel h1]⟩

theorem not_exc {g d l k : ℕ} (h1 : ¬ l ^ (k + 1) ∣ g ^ d - 1) (h2 : l ^ (4 * k) ≤ g ^ d) :
    ¬ Formalism.CyclotomicNorms.Exc g d l := by
  rintro ⟨hl, h⟩
  have hv : padicValNat l (g ^ d - 1) ≤ k := by
    by_contra hc
    exact h1 ((pow_dvd_pow l (by omega)).trans (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _)))
  have := Nat.pow_le_pow_right hl.pos (Nat.mul_le_mul_left 4 hv)
  omega

theorem BB_disj0 : Disjoint (Formalism.CyclotomicNorms.BB 9 413718278401) (Formalism.CyclotomicNorms.BB 9 603339156001) := by
  rw [Set.disjoint_left]
  rintro l (rfl | ⟨d, h1, h9, h⟩) (h' | ⟨d', h1', h9', h'⟩)
  · exact absurd (Set.mem_singleton_iff.mp h') (by norm_num)
  · exact absurd (exc_dvd (by norm_num) h1' h9' h') (by decide +kernel)
  · rw [Set.mem_singleton_iff.mp h'] at h
    exact absurd (exc_dvd (by norm_num) h1 h9 h) (by decide +kernel)
  · have hg : Nat.gcd (prodPowSubOne 413718278401) (prodPowSubOne 603339156001) ∣ [2, 3, 5, 7, 11, 13, 37, 571, 599].prod ^ 52 := by decide +kernel
    have hm := mem_of_dvd_prod_pow h.1 _ _ (by decide +kernel)
      ((Nat.dvd_gcd (exc_dvd (by norm_num) h1 h9 h) (exc_dvd (by norm_num) h1' h9' h')).trans hg)
    have key : ∀ l ∈ [2, 3, 5, 7, 11, 13, 37, 571, 599], ∀ d ∈ List.range 10, 1 ≤ d → ∃ k ∈ List.range 20,
        ¬ l ^ (k + 1) ∣ 413718278401 ^ d - 1 ∧ l ^ (4 * k) ≤ 413718278401 ^ d := by decide +kernel
    obtain ⟨k, -, hk1, hk2⟩ := key l hm d (List.mem_range.mpr (by omega)) h1
    exact not_exc hk1 hk2 h

end Formalism.BasicNotions.Examples₂
