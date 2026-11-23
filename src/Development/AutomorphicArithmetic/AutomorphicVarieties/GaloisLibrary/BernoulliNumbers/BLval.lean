module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Hurzero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Sumicc
import Mathlib.Algebra.Algebra.Field
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset UpperTheory.V.Bern

private theorem hurwitzZeta_one_sub_eq_bernoulli (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (h0 : 0 < x) (h1 : x ≤ 1) :
    HurwitzZeta.hurwitzZeta (x : UnitAddCircle) (1 - k) =
      -1 / k * ((Polynomial.bernoulli k).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have e : (1 : ℂ) - ((0 + 1 : ℕ) : ℂ) = 0 := by push_cast; ring
    rw [e, b_hurzero x h0 h1]
    simp [Polynomial.bernoulli_one]
  · have := HurwitzZeta.hurwitzZeta_neg_nat (k := m) (x := x) hm.ne' ⟨h0.le, h1⟩
    have e : (1 : ℂ) - ((m + 1 : ℕ) : ℂ) = -(m : ℂ) := by push_cast; ring
    rw [e, this]
    push_cast
    ring

theorem UpperTheory.V.Bern.b_lval :
    ∀ {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) (k : ℕ), 1 ≤ k → ZMod.LFunction Φ (1 - k) = -genB k Φ / k := by
  intro N _ Φ k hk
  have hN : (0:ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hpow : (N : ℂ) ^ (-(1 - (k:ℂ))) = (N:ℂ) ^ ((k:ℤ) - 1) := by
    rw [show -(1 - (k:ℂ)) = (((k:ℤ) - 1 : ℤ) : ℂ) by push_cast; ring, Complex.cpow_intCast]
  rw [ZMod.LFunction, hpow, ← b_sumicc, genB, Finset.mul_sum, neg_div, Finset.sum_div,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mem_Icc] at ha
  have hx0 : (0:ℝ) < a / N := div_pos (by exact_mod_cast ha.1) hN
  have hx1 : (a:ℝ) / N ≤ 1 := (div_le_one hN).mpr (by exact_mod_cast ha.2)
  rw [ZMod.toAddCircle_natCast, hurwitzZeta_one_sub_eq_bernoulli k hk _ hx0 hx1, bcoef, map_mul, map_zpow₀,
    map_natCast, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
  have hk0 : (k:ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hq : (algebraMap ℚ ℂ) ((a:ℚ) / N) = (((a:ℝ) / N : ℝ) : ℂ) := by push_cast; rfl
  rw [hq]
  field_simp
