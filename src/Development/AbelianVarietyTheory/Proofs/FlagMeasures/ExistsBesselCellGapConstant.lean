module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

namespace GlobalTheory.GapConstant


theorem gap_thresholds (k r : ℕ) (hk : 1 ≤ k) :
    Formalism.FourierDecayAlt.ThreeDimData.GapOK k r (1000 * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
              (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) ∧
      GlobalTheory.CellAmp.GapCell k r (1000 * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
        (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hs : ((2 * r + 2 : ℕ) : ℝ) = 2 * ((r : ℝ) + 1) := by push_cast; ring
  have h3 : ((3 * (r + 1) : ℕ) : ℝ) = 3 * ((r : ℝ) + 1) := by push_cast; ring
  have hNdef : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1 := by push_cast; ring
  rw [hs, h3]
  set P : ℝ := (r : ℝ) + 1 with hPdef
  set N : ℝ := ((2 * r + k + 1 : ℕ) : ℝ)
  have hP1 : 1 ≤ P := by rw [hPdef]; linarith only [hr0]
  have hP0 : 0 ≤ P := zero_le_one.trans hP1
  have hN1 : 1 ≤ N := by rw [hNdef]; linarith only [hr0, hk0]
  have hN0 : 0 ≤ N := zero_le_one.trans hN1
  have h2P1 : 1 ≤ 2 * P := by linarith only [hP1]
  have h2P : 0 < 2 * P := zero_lt_one.trans_le h2P1
  have hsq1 : 1 ≤ Real.sqrt (2 * P) := Real.one_le_sqrt.mpr h2P1
  have hrp : (2 * P) ^ ((9 : ℝ) / 2) = (2 * P) ^ 4 * Real.sqrt (2 * P) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add h2P]
    norm_num
  rw [hrp]
  set X : ℝ := 3 * P * N ^ 2 + N ^ 3 with hX
  have ha : Formalism.FourierDecayAlt.ThreeDimData.aOf r (1000 * ((2 * P) ^ 4 * Real.sqrt (2 * P)) * X) = 2000 * P ^ 4 * X := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.aOf
    rw [← hPdef]
    apply (div_eq_iff (mul_ne_zero (by norm_num) (ne_of_gt (Real.sqrt_pos.mpr h2P)))).2
    ring

  have hd0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.dN k r := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.dN
    linarith only [sq_nonneg (r : ℝ), mul_nonneg hr0 hk0, hr0]
  have hd : Formalism.FourierDecayAlt.ThreeDimData.dN k r ≤ 2 * P * N := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.dN
    rw [hPdef, hNdef]
    linarith only [sq_nonneg (r : ℝ), hr0, hk0]
  have hAS : Formalism.FourierDecayAlt.ThreeDimData.AS k r ≤ 2 * P * N ^ 2 := by
    have hm : ((2 * r + k : ℕ) : ℝ) ≤ N := Nat.cast_le.mpr (Nat.le_succ _)
    calc
      _ ≤ N * (2 * P * N) := mul_le_mul hm hd hd0 hN0
      _ = 2 * P * N ^ 2 := by ring
  have hAS0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AS k r :=
    mul_nonneg (Nat.cast_nonneg _) hd0
  have hAG : Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 4 * N * P := by
    have hkr : (k : ℝ) + r ≤ N := by rw [hNdef]; linarith only [hr0]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkr (by norm_num)) hP0
  have hAG0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r :=
    mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hk0 hr0)) hP0
  have hM : Formalism.FourierDecayAlt.ThreeDimData.Mexp r ≤ 2 * P ^ 2 := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp
    rw [hPdef]
    linarith only [hr0]

  have hP35 : P ^ 3 ≤ P ^ 5 := pow_le_pow_right₀ hP1 (by norm_num)
  have hP15 : P ≤ P ^ 5 := by
    simpa only [pow_one] using pow_le_pow_right₀ hP1 (show 1 ≤ 5 by norm_num)
  have hP5 : 1 ≤ P ^ 5 := one_le_pow₀ hP1
  have hN12 : N ≤ N ^ 2 := by
    simpa only [mul_one, pow_two] using mul_le_mul_of_nonneg_left hN1 hN0
  have hN3 : 0 ≤ N ^ 3 := pow_nonneg hN0 3
  have hP50 : 0 ≤ P ^ 5 := zero_le_one.trans hP5
  have hbig : 6000 * P ^ 5 * N ^ 2 ≤ 2000 * P ^ 4 * X := by
    rw [hX]
    linarith only [mul_nonneg (pow_nonneg hP0 4) hN3]
  have m1 : P ^ 3 * N ^ 2 ≤ P ^ 5 * N ^ 2 := mul_le_mul_of_nonneg_right hP35 (sq_nonneg N)
  have m2 : P ^ 3 * N ≤ P ^ 5 * N ^ 2 := mul_le_mul hP35 hN12 hN0 hP50
  have m3 : P * N ≤ P ^ 5 * N ^ 2 := mul_le_mul hP15 hN12 hN0 hP50
  have m4 : (1 : ℝ) ≤ P ^ 5 * N ^ 2 := one_le_mul_of_one_le_of_one_le hP5 (one_le_pow₀ hN1)
  have m5 : P * N ^ 2 ≤ P ^ 5 * N ^ 2 := mul_le_mul_of_nonneg_right hP15 (sq_nonneg N)
  have hsum : Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤
      2 * P * N ^ 2 + 4 * N * P := add_le_add hAS hAG
  have hprod : Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) ≤
      (2 * P ^ 2) * (2 * P * N ^ 2 + 4 * N * P) :=
    mul_le_mul hM hsum (add_nonneg hAS0 hAG0) (mul_nonneg (by norm_num) (sq_nonneg P))
  have hprod2 : ((r : ℝ) + 1) ^ 2 * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) ≤
      P ^ 2 * (2 * P * N ^ 2 + 4 * N * P) :=
    mul_le_mul_of_nonneg_left hsum (sq_nonneg P)
  refine ⟨⟨hk, ?_, ?_, ?_⟩, ?_⟩
  · have hX3 : N ^ 3 ≤ X := by
      rw [hX]
      exact le_add_of_nonneg_left (mul_nonneg (mul_nonneg (by norm_num) hP0) (sq_nonneg N))
    have hXmul : X ≤ ((2 * P) ^ 4 * Real.sqrt (2 * P)) * X :=
      le_mul_of_one_le_left (hN3.trans hX3) (one_le_mul_of_one_le_of_one_le (one_le_pow₀ h2P1) hsq1)
    linarith only [hX3, hXmul, hN3]
  · rw [ha]
    linarith only [hprod, hAG, m1, m2, m3, m4, hbig]
  · rw [ha]
    rw [← hPdef]
    linarith only [hAG, m3, m4, m5, hbig]
  · unfold GlobalTheory.CellAmp.GapCell
    rw [ha]
    linarith only [hprod2, hAG, m1, m2, m3, m4, hbig]

theorem gap_constant_exists : ∃ Cgf : ℝ, ∀ (D : Formalism.BasicNotions.D7) (ε : Fin (2 * D.R.rS + D.R.k + 1) → Bool) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ), Formalism.QuantumDeterminants.GapAtLeast ε lam (Cgf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3)) → ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h ∧ GlobalTheory.CellAmp.GapCell D.R.k D.R.rS h := by
  refine ⟨1000, fun D ε lam hg => ⟨_, hg, ?_⟩⟩
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  exact gap_thresholds D.R.k D.R.rS hk

end GlobalTheory.GapConstant
