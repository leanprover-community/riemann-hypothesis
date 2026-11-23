module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensVolT
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

namespace PositivityTheory.SiegelWeilFormula.OswLocFin

theorem eq_one_of_re_pow_two (w : ℂ) (hw : ‖w‖ = 1) (hre : ∀ k : ℕ, 1 / 2 < (w ^ (2 ^ k)).re) :
    w = 1 := by
  apply PI.VolStabSW.VolAAW.eq_one_of_pow <;> assumption

theorem no_small_subgroups {K : Type*} [NormedField K] [IsUltrametricDist K] [ProperSpace K]
    (χ : K → ℂ) (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1)
    (hn : ∀ x, ‖χ x‖ = 1) : ∃ ε > 0, ∀ t : K, ‖t‖ ≤ ε → χ t = 1 := by
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuous_iff.1 hc 0 (1 / 2) (by norm_num)
  refine ⟨δ / 2, half_pos hδ, fun t ht => ?_⟩
  have h2 : ‖(2 : K)‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (1 : K) 1
    rw [one_add_one_eq_two, norm_one, max_self] at this
    exact this
  have hsmall : ∀ k : ℕ, ‖(2 : K) ^ k * t‖ ≤ δ / 2 := fun k => by
    rw [norm_mul, norm_pow]
    calc ‖(2 : K)‖ ^ k * ‖t‖ ≤ 1 * ‖t‖ := by
          gcongr; exact pow_le_one₀ (norm_nonneg _) h2
      _ ≤ δ / 2 := by rw [one_mul]; exact ht
  have hpow : ∀ k : ℕ, χ ((2 : K) ^ k * t) = χ t ^ (2 ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show (2 : K) ^ (k + 1) * t = (2 : K) ^ k * t + (2 : K) ^ k * t by ring, hadd, ih, ← pow_add]
      congr 1
      ring
  have hre : ∀ k : ℕ, 1 / 2 < (χ t ^ (2 ^ k)).re := by
    intro k
    rw [← hpow k]
    have hd := hδc ((2 : K) ^ k * t) (by rw [dist_zero_right]; linarith [hsmall k])
    rw [h0, dist_eq_norm] at hd
    have := Complex.re_le_norm (1 - χ ((2 : K) ^ k * t))
    rw [norm_sub_rev] at this
    simp only [Complex.sub_re, Complex.one_re] at this
    linarith
  exact eq_one_of_re_pow_two (χ t) (hn t) hre

end PositivityTheory.SiegelWeilFormula.OswLocFin
