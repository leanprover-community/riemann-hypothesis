module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CapelliQdetStatement
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

theorem gapCentral (n : ℕ) : GapCentralStatement n := by
  intro ε lam h ⟨_, hg, hN⟩
  unfold hNeed at hN
  have hA := (le_max_left _ _).trans_lt hN
  have hB := (le_max_right _ _).trans_lt hN
  have hB1 := (le_max_left _ _).trans_lt hB
  have hB2 := (le_max_right _ _).trans_lt hB
  have hA1 : 1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) ≤
      max (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ)) := le_max_right _ _
  have hM : 2 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) ≤
      max (2 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ)) (2 * ((qOf ε : ℝ) - 1) * (n : ℝ) ^ 2) := le_max_left _ _
  have hs := Real.sqrt_nonneg (2 * (min (pOf ε) (qOf ε) : ℝ))
  have hn : (0 : ℝ) ≤ (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) := by positivity
  have hP := mul_nonneg hs (by linarith : (0 : ℝ) ≤
      4 * max (2 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ)) (2 * ((qOf ε : ℝ) - 1) * (n : ℝ) ^ 2) + 1 -
        (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ))
  exact ⟨hg, by linarith, by linarith, by nlinarith⟩

theorem hcV_of_centralChar (n : ℕ) (hCC : CentralCharStatement n) : HcVStatement n := by
  intro ε lam h H _ _ _ σ D E V hσ hD hV hc hVK hint hanti hgap hp hq ω y hy
  have hle : V ≤ genSub E V := le_sInf fun T hT => hT.1
  exact hCC ε lam h H σ D E V hσ hD hV hc hVK hint hanti hgap hp hq ω y (hle hy)

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
