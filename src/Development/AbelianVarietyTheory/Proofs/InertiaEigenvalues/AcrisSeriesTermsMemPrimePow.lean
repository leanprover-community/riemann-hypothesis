module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TmPowDvd
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem pw_natCast_eq_pow (l : ℕ) [Fact l.Prime] (n : ℕ) (x : Fl l) : pw (n : ℤ) x = x ^ l ^ n := by
  unfold pw
  rw [zpow_natCast]
  induction n generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, RingAut.mul_apply, ih, frobeniusEquiv_apply, frobenius_def, ← pow_mul, pow_succ,
      mul_comm]

theorem two_mul_succ_le_pow (l k h : ℕ) (hl : 2 ≤ l) (hh : 2 ≤ h) :
    2 * (k + 1) ≤ l ^ ((k + 1) * h - 1) := by
  have h1 : 2 * k + 1 < 2 ^ (2 * k + 1) := Nat.lt_two_pow_self
  have h2 : 2 ^ (2 * k + 1) ≤ l ^ (2 * k + 1) := Nat.pow_le_pow_left hl _
  have h3 : (k + 1) * 2 ≤ (k + 1) * h := Nat.mul_le_mul_left _ hh
  have h4 : l ^ (2 * k + 1) ≤ l ^ ((k + 1) * h - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem terms_mem (l : ℕ) [Fact l.Prime] (h : ℕ) (x : Fl l) (hh : 2 ≤ h)
    (hx : ‖sh x‖ ≤ ‖(l : ℂ_[l])‖) :
    ∃ c : ℤ → Acris l, (∀ n : ℤ, (l : Acris l) ^ n.natAbs ∣ c n) ∧ ∀ n : ℤ,
      (l : Acris l) ^ n.toNat * c n =
        (l : Acris l) ^ (-n).toNat * algebraMap (Ainf l) (Acris l) (tm (pw (n * h) x)) := by
  have key : ∀ n : ℤ, ∃ c : Acris l, (l : Acris l) ^ n.natAbs ∣ c ∧
      (l : Acris l) ^ n.toNat * c =
        (l : Acris l) ^ (-n).toNat * algebraMap (Ainf l) (Acris l) (tm (pw (n * h) x)) := by
    intro n
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · cases m with
      | zero => exact ⟨algebraMap (Ainf l) (Acris l) (tm (pw (0 * h) x)), by simp, by simp⟩
      | succ k =>
        have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
        obtain ⟨d, hd⟩ := tm_pow_dvd l x hx
        set y := algebraMap (Ainf l) (Acris l) (tm x)
        set M := l ^ ((k + 1) * h - 1)
        have hM := two_mul_succ_le_pow l k h hl2 hh
        have hN : l ^ ((k + 1) * h) = l * M := by
          have : (k + 1) * h = ((k + 1) * h - 1) + 1 := by
            have : 2 ≤ (k + 1) * h := le_trans hh (Nat.le_mul_of_pos_left h (Nat.succ_pos k))
            omega
          rw [this, pow_succ, mul_comm]
        have hpow : algebraMap (Ainf l) (Acris l) (tm (pw (((k + 1 : ℕ) : ℤ) * h) x)) =
            (l : Acris l) ^ (2 * (k + 1)) * ((l : Acris l) ^ (M - 2 * (k + 1)) * d ^ M) := by
          have e1 : (((k + 1 : ℕ) : ℤ) * (h : ℤ)) = (((k + 1) * h : ℕ) : ℤ) := by push_cast; ring
          rw [e1, pw_natCast_eq_pow, show tm (x ^ l ^ ((k + 1) * h)) = tm x ^ l ^ ((k + 1) * h) from
            map_pow (WittVector.teichmuller l) x _, map_pow, hN, pow_mul, hd, mul_pow, ← mul_assoc,
            ← pow_add, Nat.add_sub_cancel' hM]
        refine ⟨(l : Acris l) ^ (k + 1) * ((l : Acris l) ^ (M - 2 * (k + 1)) * d ^ M), ?_, ?_⟩
        · have e4 : (((k + 1 : ℕ) : ℤ)).natAbs = k + 1 := by omega
          rw [e4]
          exact Dvd.intro _ rfl
        · have e2 : (-((k + 1 : ℕ) : ℤ)).toNat = 0 := by omega
          have e3 : (((k + 1 : ℕ) : ℤ)).toNat = k + 1 := by omega
          rw [e2, e3, pow_zero, one_mul, hpow, ← mul_assoc, ← pow_add]
          ring_nf
    · refine ⟨(l : Acris l) ^ m * algebraMap (Ainf l) (Acris l) (tm (pw (-(m : ℤ) * h) x)),
        ?_, ?_⟩
      · have e4 : (-(m : ℤ)).natAbs = m := by omega
        rw [e4]
        exact Dvd.intro _ rfl
      · have e2 : (-(m : ℤ)).toNat = 0 := by omega
        have e3 : (-(-(m : ℤ))).toNat = m := by omega
        rw [e2, e3, pow_zero, one_mul]
  choose c hc1 hc2 using key
  exact ⟨c, hc1, hc2⟩

end GlobalTheory.PSer
