module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
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

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomNum

theorem mom_num : ∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (T : ℝ), Num k r lam u b bv ga h q0 → 0 < T → (((2 * r + k + 1) : ℝ) ^ 2 * (T * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) * (b ^ 2) ^ (2 * r) ≤ Hsq r T b := by
  intro k r lam u b bv ga h q0 T hN hT
  obtain ⟨-, -, -, -, -, -, h7, h8, -, -, -, -, -, -, h15⟩ := hN
  have ha := (h7 ⟨k, by omega⟩ (by simp)).2
  have hb := (abs_le.mp (h8 ⟨k, by omega⟩)).1
  have hbv : bv ≤ b := by linarith
  have hn1 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  have hn7 : ((2 * r + k + 1 : ℕ) : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 := le_self_pow₀ hn1 (by norm_num)
  have hcast : ((2 * r + k + 1 : ℕ) : ℝ) = ((2 * r + k + 1) : ℝ) := by push_cast; ring
  rw [hcast] at hn1 hn7 h15
  set n : ℝ := (2 * r + k + 1 : ℝ) with hn
  have hnb : n ≤ b := by linarith
  have hbv6 : 6 ≤ bv := by linarith
  have hb6 : 6 ≤ b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have h6 : 6 * bv ≤ b ^ 2 := by nlinarith
  have hb0 : 0 ≤ b := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hbv0 : 0 ≤ 6 * bv := by linarith
  have hTm : T ≤ max 1 T := le_max_right _ _
  have hm0 : 0 ≤ max 1 T := le_trans zero_le_one (le_max_left _ _)
  unfold Hsq
  calc n ^ 2 * (T * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2)) * (b ^ 2) ^ (2 * r)
      ≤ b ^ 2 * (max 1 T * b ^ 4) * (b ^ 2) ^ (2 * (2 * r + 2)) * (b ^ 2) ^ (2 * r) := by
        gcongr
    _ = max 1 T * b ^ (12 * r + 14) := by ring
    _ ≤ max 1 T * b ^ (20 * (r + 1)) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb1 (by omega)) hm0

end GlobalTheory.MomNum
