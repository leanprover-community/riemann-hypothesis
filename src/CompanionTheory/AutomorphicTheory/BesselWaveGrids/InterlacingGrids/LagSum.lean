module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

open Finset

theorem lag_abs_term_le {d : ℕ} (y : Fin (d + 1) → ℝ) (h : ∀ i j, i ≠ j → 5 ≤ |y i - y j|)
    (j : Fin (d + 1)) :
    |∏ i ∈ (univ : Finset (Fin (d + 1))).erase j, (y j - y i)⁻¹| ≤ (1 / 5 : ℝ) ^ d := by
  rw [abs_prod]
  have hcard : ((univ : Finset (Fin (d + 1))).erase j).card = d := by
    rw [Finset.card_erase_of_mem (mem_univ j)]; simp
  calc ∏ i ∈ (univ : Finset (Fin (d + 1))).erase j, |(y j - y i)⁻¹|
      ≤ ∏ _i ∈ (univ : Finset (Fin (d + 1))).erase j, (1 / 5 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i _; exact abs_nonneg _
        · intro i hi
          have hij : j ≠ i := (Finset.ne_of_mem_erase hi).symm
          rw [abs_inv]
          have hx : 0 < |y j - y i| := lt_of_lt_of_le (by norm_num) (h j i hij)
          simpa only [one_div] using
            (div_le_div_iff₀ (a := (1 : ℝ)) (b := |y j - y i|) (c := 1) (d := 5)
              hx (by norm_num : 0 < (5 : ℝ))).2 (by simpa using h j i hij)
    _ = (1 / 5 : ℝ) ^ d := by rw [Finset.prod_const, hcard]

theorem lag_abs_sum_le_one {d : ℕ} (y : Fin (d + 1) → ℝ) (h : ∀ i j, i ≠ j → 5 ≤ |y i - y j|) :
    ∑ j, |∏ i ∈ (univ : Finset (Fin (d + 1))).erase j, (y j - y i)⁻¹| ≤ 1 := by
  have hn : (d : ℝ) + 1 ≤ 5 ^ d := by
    have : d + 1 ≤ 5 ^ d := Nat.lt_pow_self (by norm_num)
    exact_mod_cast this
  calc ∑ j, |∏ i ∈ (univ : Finset (Fin (d + 1))).erase j, (y j - y i)⁻¹|
      ≤ ∑ _j : Fin (d + 1), (1 / 5 : ℝ) ^ d :=
        Finset.sum_le_sum (fun j _ => lag_abs_term_le y h j)
    _ = ((d : ℝ) + 1) / 5 ^ d := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_pow, one_pow]
        push_cast; ring
    _ ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact hn

end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
