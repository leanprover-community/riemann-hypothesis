module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LValEtaBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Real.Pi.Bounds
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
public import Mathlib.NumberTheory.ZetaValues
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

open Real

namespace GlobalTheory

theorem zetaTerm_tsum_le_two (i : ℕ) (hi : 2 ≤ i) :
    ∑' n : ℕ, 1/((n:ℝ)+1)^i ≤ 2 := by
  apply GlobalTheory.EtaValueBound.zeta_le_two <;> assumption

theorem volumeConstant_le (r : ℕ) (hr : 2 ≤ r) :
    √r * ∏ i ∈ Finset.Icc 2 r, (∑' n : ℕ, 1/((n:ℝ)+1)^i) ≤ 2^(r*(r-1)/2) * (2*π)^(r-1) * √r := by
  have hprod : ∏ i ∈ Finset.Icc 2 r, (∑' n : ℕ, 1/((n:ℝ)+1)^i) ≤ ∏ _i ∈ Finset.Icc 2 r, (2:ℝ) := by
    apply Finset.prod_le_prod₀
    · intro i _; exact tsum_nonneg (fun n => by positivity)
    · intro i hi; exact zetaTerm_tsum_le_two i (Finset.mem_Icc.mp hi).1
  rw [Finset.prod_const, Nat.card_Icc] at hprod
  have hexp : r + 1 - 2 ≤ r*(r-1)/2 := by
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have : k + 2 + 1 - 2 = k + 1 := by omega
    have h' : k + 2 - 1 = k + 1 := by omega
    rw [this, h']
    nlinarith
  have hpow : (2:ℝ)^(r+1-2) ≤ 2^(r*(r-1)/2) := pow_le_pow_right₀ (by norm_num) hexp
  have hpi : (1:ℝ) ≤ (2*π)^(r-1) := one_le_pow₀ (by linarith [Real.pi_gt_three])
  have hsq : 0 ≤ √(r:ℝ) := Real.sqrt_nonneg _
  have h2p : (0:ℝ) ≤ 2^(r*(r-1)/2) := by positivity
  calc √r * ∏ i ∈ Finset.Icc 2 r, (∑' n : ℕ, 1/((n:ℝ)+1)^i)
      ≤ √r * 2^(r*(r-1)/2) := mul_le_mul_of_nonneg_left (hprod.trans hpow) hsq
    _ ≤ √r * (2^(r*(r-1)/2) * (2*π)^(r-1)) := by
        apply mul_le_mul_of_nonneg_left _ hsq
        nlinarith
    _ = 2^(r*(r-1)/2) * (2*π)^(r-1) * √r := by ring

end GlobalTheory
