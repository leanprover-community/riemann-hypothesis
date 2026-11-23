module

public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Statements
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real MeasureTheory

universe u

theorem TailBound.proof (h1 : MeanCountBound.Statement.{u}) :
    TailBound.Statement.{u} := by
  intro X _ μ lam cnt a ka r hH x hx
  have hprob := hH.isProbability
  set t := exp (-x) * r with ht_def
  have ht_pos : 0 < t := mul_pos (exp_pos _) hH.r_pos
  have ht_le : t ≤ r := by
    have : exp (-x) ≤ 1 := exp_le_one_iff.mpr (by linarith)
    nlinarith [hH.r_pos]
  have hS : MeasurableSet {z | lam z < t} := measurableSet_lt hH.lam_meas measurable_const

  have hmarkov : μ.real {z | lam z < t} ≤ meanCount μ cnt t := by
    rw [← integral_indicator_one hS, meanCount]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator hS) (hH.integrable t ht_pos) ?_
    intro z
    by_cases hz : z ∈ {z | lam z < t}
    · rw [Set.indicator_of_mem hz]
      exact hH.one t ht_pos ht_le z hz
    · rw [Set.indicator_of_notMem hz]
      exact hH.cnt_nonneg t z

  have hscale : meanCount μ cnt t = exp (-x) ^ ka * meanCount μ cnt r :=
    hH.scaling (exp (-x)) r (exp_pos _) hH.r_pos
  have hpow : exp (-x) ^ ka = exp (-(ka * x)) := by
    rw [← exp_mul]; ring_nf
  have hmean := h1 X μ lam cnt a ka r hH
  have hbound : μ.real {z | lam z < t} ≤ 2 * 36 ^ a * exp (-(ka * x)) := by
    calc μ.real {z | lam z < t} ≤ meanCount μ cnt t := hmarkov
      _ = exp (-(ka * x)) * meanCount μ cnt r := by rw [hscale, hpow]
      _ ≤ exp (-(ka * x)) * (2 * 36 ^ a) :=
          mul_le_mul_of_nonneg_left hmean (exp_pos _).le
      _ = 2 * 36 ^ a * exp (-(ka * x)) := by ring
  have hone : μ.real {z | lam z < t} ≤ 1 := measureReal_le_one
  exact le_min hone hbound

end GroundTheory.Heights₂.Heights.LowerBound
