module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem pow_padicVal_eq_one_of_primePow {k : Type} [Field k] {n l : ℕ} (hn : 0 < n) (hl : l.Prime) {y : k}
    (h1 : y ^ n = 1) {a : ℕ} (h2 : y ^ (l ^ a) = 1) : y ^ (l ^ padicValNat l n) = 1 := by
  have := Fact.mk hl
  have d1 : orderOf y ∣ n := orderOf_dvd_of_pow_eq_one h1
  have d2 : orderOf y ∣ l ^ a := orderOf_dvd_of_pow_eq_one h2
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hl).1 d2
  rw [hi] at d1
  have hle : i ≤ padicValNat l n := ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hn.ne').1 d1
  apply orderOf_dvd_iff_pow_eq_one.1
  rw [hi]
  exact pow_dvd_pow l hle

theorem primePowRoots_finite_ncard (k : Type) [Field k] (n l : ℕ) (hn : 0 < n) (hl : l.Prime) :
    {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1}.Finite ∧
      {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1}.ncard ≤ l ^ padicValNat l n := by
  have hm : 0 < l ^ padicValNat l n := pow_pos hl.pos _
  have hsub : {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1} ⊆
      ((nthRoots (l ^ padicValNat l n) (1 : k)).toFinset : Set k) := by
    rintro y ⟨h1, a, h2⟩
    rw [Finset.mem_coe, Multiset.mem_toFinset, mem_nthRoots hm]
    exact pow_padicVal_eq_one_of_primePow hn hl h1 h2
  refine ⟨(Finset.finite_toSet _).subset hsub, ?_⟩
  refine (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans ?_
  rw [Set.ncard_coe_finset]
  exact (Multiset.toFinset_card_le _).trans (card_nthRoots _ _)

theorem samePart_roots_finite_ncard :
    ∀ (k : Type) [Field k] (n l : ℕ), 0 < n → l.Prime →
      ({y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1}.Finite ∧
        {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1}.ncard ≤ l ^ padicValNat l n) ∧
      ∀ z : k, {x : k | x ^ n = 1 ∧ SamePart l x z}.Finite ∧
        {x : k | x ^ n = 1 ∧ SamePart l x z}.ncard ≤ l ^ padicValNat l n := by
  intro k _ n l hn hl
  obtain ⟨hf, hc⟩ := primePowRoots_finite_ncard k n l hn hl
  refine ⟨⟨hf, hc⟩, fun z => ?_⟩
  rcases Set.eq_empty_or_nonempty {x : k | x ^ n = 1 ∧ SamePart l x z} with he | ⟨x₀, hx₀, hb⟩
  · rw [he]; simp
  have hsub : {x : k | x ^ n = 1 ∧ SamePart l x z} ⊆
      (fun y => y * x₀) '' {y : k | y ^ n = 1 ∧ ∃ a : ℕ, y ^ (l ^ a) = 1} := by
    rintro x ⟨hx, ha⟩
    have hs : SamePart l x x₀ := Eq.trans ha (Eq.symm hb)
    obtain ⟨a, ha⟩ := (samePart_iff hl (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hx⟩)
      (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hx₀⟩)).1 hs
    have h0 : x₀ ≠ 0 := by
      rintro rfl
      rw [zero_pow hn.ne'] at hx₀
      exact zero_ne_one hx₀
    refine ⟨x / x₀, ⟨?_, a, ?_⟩, div_mul_cancel₀ x h0⟩
    · rw [div_pow, hx, hx₀, div_one]
    · rw [div_pow, ha, div_self (pow_ne_zero _ h0)]
  refine ⟨(hf.image _).subset hsub, ?_⟩
  exact (Set.ncard_le_ncard hsub (hf.image _)).trans ((Set.ncard_image_le hf).trans hc)

end GlobalTheory.BadShare
