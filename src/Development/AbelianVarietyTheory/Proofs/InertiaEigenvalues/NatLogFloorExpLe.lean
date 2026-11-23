module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory.HubLoc

open NumberField IsDedekindDomain Module in
private lemma natLog_mul_log_two_le_log_of_le {l m : ℕ} {C : ℝ} (hl : 2 ≤ l) (hC : 1 ≤ C)
    (hm : (m : ℝ) ≤ C) : (Nat.log l m : ℝ) * Real.log 2 ≤ Real.log C := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simpa using Real.log_nonneg hC
  have h1 : Nat.log l m ≤ Nat.log 2 m := Nat.log_anti_left (by norm_num) hl
  have h2 : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hpos.ne'
  have h3 : (2 : ℝ) ^ Nat.log l m ≤ C :=
    calc (2 : ℝ) ^ Nat.log l m ≤ 2 ^ Nat.log 2 m := pow_le_pow_right₀ (by norm_num) h1
      _ ≤ m := by exact_mod_cast h2
      _ ≤ C := hm
  have h4 := Real.log_le_log (by positivity) h3
  rwa [Real.log_pow] at h4

open NumberField IsDedekindDomain Module in
private lemma natLog_le_add_two_mul_of_le_two_pow_mul_exp {l m k : ℕ} {L : ℝ} (hl : 2 ≤ l) (hL : 0 ≤ L)
    (hm : (m : ℝ) ≤ 2 ^ k * Real.exp L) : (Nat.log l m : ℝ) ≤ k + 2 * L := by
  have hC : (1 : ℝ) ≤ 2 ^ k * Real.exp L :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (Real.one_le_exp hL)
  have h := natLog_mul_log_two_le_log_of_le hl hC hm
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp] at h
  have hlog : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  by_contra hcon
  push_neg at hcon
  have : ((Nat.log l m : ℝ) - k) * Real.log 2 ≤ L := by linarith
  nlinarith


open NumberField IsDedekindDomain Module in
theorem _root_.GlobalTheory.HubLoc.cBnum_le_thirty : ∀ (l t N : ℕ) (L : ℝ), 2 ≤ l → 1 ≤ t → 1 ≤ N →
    1 ≤ L → (_root_.GlobalTheory.HubLoc.cBnum l ⌊2 * Real.exp L⌋₊ t N : ℝ) ≤ 30 * t * N * L := by
  intro l t N L hl ht hN hL
  have hfl : ((⌊2 * Real.exp L⌋₊ : ℕ) : ℝ) ≤ 2 * Real.exp L :=
    Nat.floor_le (by positivity)
  have hm : ((2 * ⌊2 * Real.exp L⌋₊ : ℕ) : ℝ) ≤ 2 ^ 2 * Real.exp L := by
    push_cast
    nlinarith
  have hK := natLog_le_add_two_mul_of_le_two_pow_mul_exp hl (by linarith) hm
  unfold _root_.GlobalTheory.HubLoc.cBnum
  push_cast at hK ⊢
  set K : ℝ := (Nat.log l (2 * ⌊2 * Real.exp L⌋₊) : ℝ)
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  have htN : (1 : ℝ) ≤ t * N := one_le_mul_of_one_le_of_one_le ht' hN'
  have htNL : (1 : ℝ) ≤ t * N * L := one_le_mul_of_one_le_of_one_le htN hL
  have hL1 : L ≤ t * N * L := by nlinarith
  have ht1 : (t : ℝ) ≤ t * N * L := by nlinarith
  have hA : (t : ℝ) * N * K ≤ t * N * (2 + 2 * L) := by
    apply mul_le_mul_of_nonneg_left hK; positivity
  nlinarith

end GlobalTheory.HubLoc
