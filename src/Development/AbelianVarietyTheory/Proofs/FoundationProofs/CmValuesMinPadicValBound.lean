module

public import Formalism.PairingDivisors.StatementN
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
public import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

@[expose] public section

namespace GlobalTheory

open Formalism.PairingDivisionLocalBalance

theorem exists_pow_ne_one_mod (l n : ℕ) (hl : l.Prime) (hn : ¬ (l - 1) ∣ n) :
    ∃ a : ℕ, 2 ≤ a ∧ a.Coprime l ∧ ¬ l ∣ a ^ n - 1 := by
  haveI := Fact.mk hl
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  have hord : orderOf g = l - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime hl]
  refine ⟨(g : ZMod l).val, ?_, ZMod.val_coe_unit_coprime g, ?_⟩
  · by_contra h
    push_neg at h
    interval_cases hv : (g : ZMod l).val
    · have : (g : ZMod l) = 0 := (ZMod.val_eq_zero _).mp hv
      exact (Units.ne_zero g) this
    · have h1 : (g : ZMod l) = 1 := by
        rw [← ZMod.natCast_zmod_val (g : ZMod l), hv, Nat.cast_one]
      have : g = 1 := Units.ext h1
      rw [this, orderOf_one] at hord
      exact hn (by rw [← hord]; exact one_dvd n)
  · intro hdvd
    have hpos : 1 ≤ (g : ZMod l).val ^ n := by
      apply Nat.one_le_pow
      rw [Nat.pos_iff_ne_zero, Ne, ZMod.val_eq_zero]
      exact Units.ne_zero g
    have h0 : (((g : ZMod l).val ^ n - 1 : ℕ) : ZMod l) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    rw [Nat.cast_sub hpos, Nat.cast_pow, ZMod.natCast_zmod_val, Nat.cast_one, sub_eq_zero] at h0
    have hgn : g ^ n = 1 := Units.ext (by simpa using h0)
    exact hn (hord ▸ orderOf_dvd_of_pow_eq_one hgn)

theorem cmValues_minPadicVal_bound : MinVal := by
  intro l n hl hn2 hne
  haveI := Fact.mk hl
  have hn0 : n ≠ 0 := by omega
  unfold mE
  simp only [Nat.padicValNat_def]
  by_cases h2 : l = 2
  · subst h2
    refine ⟨3, by norm_num, by norm_num, ?_⟩
    have h := padicValNat.pow_two_sub_one (x := 3) (n := n) (by norm_num) (by norm_num) hn0 hne
    have h4 : multiplicity 2 (3 + 1) = 2 := by
      norm_num
      rw [show (4:ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
    have h2' : multiplicity 2 (3 - 1) = 1 := by
      norm_num
    rw [h4, h2'] at h
    simp only [if_true]
    omega
  · simp only [h2, if_false]
    have hodd : Odd l := hl.odd_of_ne_two h2
    by_cases hd : (l - 1) ∣ n
    · simp only [hd, if_true]
      refine ⟨l + 1, by have := hl.two_le; omega, ?_, ?_⟩
      · first
          | exact (Nat.coprime_succ_self l)
          | exact (Nat.coprime_self_succ l)
          | simp
      · have h := padicValNat.pow_sub_pow (p := l) (x := l + 1) (y := 1) hodd (by have := hl.one_lt; omega)
          (by simp) (by
            intro hdv
            have : l ∣ 1 := (Nat.dvd_add_right (dvd_refl l)).mp hdv
            exact hl.one_lt.ne' (Nat.dvd_one.mp this)) hn0
        rw [one_pow] at h
        rw [h, show l + 1 - 1 = l by omega, padicValNat_self]
    · simp only [hd, if_false]
      obtain ⟨a, ha2, hac, hnd⟩ := exists_pow_ne_one_mod l n hl hd
      exact ⟨a, ha2, hac, padicValNat.eq_zero_of_not_dvd hnd⟩

end GlobalTheory
