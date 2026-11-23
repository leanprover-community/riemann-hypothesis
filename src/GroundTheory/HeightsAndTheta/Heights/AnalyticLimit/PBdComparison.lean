module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot logNormSec)
open ReciprocityTheory.AnForm.A (coordDiv)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

theorem BdComparison.proof (hCC : ChartCont.Statement) (hBI : BddOnInner.Statement) :
    BdComparison.Statement := by
  intro X _ D A R φ hφ c
  have hp : ∀ j, ∃ B : ℝ, ∀ y ∈ R.V'' j, |φ j y| ≤ B := fun j =>
    hBI D A R j (φ j) ((hCC D A (bdDom R j) (isOpen_bdDom R j)).1 _ (hφ.1 j))
  choose Bf hBf using R.f_bdd
  choose Bp hBp using hp
  refine ⟨∑ j, (|Bf j| + 2 * |Bp j|) + 2 * |c|, fun y hy => ?_⟩
  have hV := mem_V''_bdIdx R y
  have hdom := V''_subset_bdDom R _ hV
  set j := bdIdx R y with hj
  have hW : R.ψ j y ∈ R.W j := hdom.2
  have hsymm : (R.ψ j).symm (R.ψ j y) = y := (R.ψ j).left_inv hV.1
  have hnd : R.ψ j y ∉ coordDiv (R.S j) := by
    rw [← R.mem_Yo_iff j _ hW, hsymm]; exact hy
  have hz : ∀ i ∈ R.S j, R.ψ j y i ≠ 0 := fun i hi h => hnd ⟨i, hi, h⟩
  have hr := R.r_chart j (R.ψ j y) ⟨hW, hnd⟩
  rw [hsymm] at hr
  have hs : rSec (bdPot R φ c) (bdSec R) y =
      Real.exp 1 - ∑ i ∈ R.S j, Real.log (‖R.ψ j y i‖ ^ 2) + 2 * (φ j y + c) := by
    have hprod : ‖∏ i ∈ R.S j, R.ψ j y i‖ ≠ 0 :=
      norm_ne_zero_iff.2 (Finset.prod_ne_zero_iff.2 hz)
    simp only [rSec, logNormSec, bdPot, bdSec, bdEq, ← hj]
    rw [Real.log_mul hprod (Real.exp_pos _).ne', Real.log_exp, norm_prod,
      Real.log_prod (fun i hi => norm_ne_zero_iff.2 (hz i hi))]
    simp only [Real.log_pow, Nat.cast_ofNat, ← Finset.mul_sum]
    ring
  rw [hr, hs]
  have e : Real.exp 1 + R.f j (R.ψ j y) - ∑ i ∈ R.S j, Real.log (‖R.ψ j y i‖ ^ 2) -
      (Real.exp 1 - ∑ i ∈ R.S j, Real.log (‖R.ψ j y i‖ ^ 2) + 2 * (φ j y + c)) =
      R.f j (R.ψ j y) + (-2) * φ j y + (-2) * c := by ring
  rw [e]
  have h1 : |R.f j (R.ψ j y)| ≤ |Bf j| := (hBf j _ hW).trans (le_abs_self _)
  have h2 : |φ j y| ≤ |Bp j| := (hBp j y hV).trans (le_abs_self _)
  have h3 : |Bf j| + 2 * |Bp j| ≤ ∑ k, (|Bf k| + 2 * |Bp k|) :=
    Finset.single_le_sum (f := fun k => |Bf k| + 2 * |Bp k|)
      (fun k _ => by positivity) (Finset.mem_univ j)
  calc |R.f j (R.ψ j y) + (-2) * φ j y + (-2) * c|
      ≤ |R.f j (R.ψ j y)| + |(-2) * φ j y| + |(-2) * c| := abs_add_three _ _ _
    _ = |R.f j (R.ψ j y)| + 2 * |φ j y| + 2 * |c| := by
        rw [abs_mul, abs_mul]; norm_num
    _ ≤ ∑ k, (|Bf k| + 2 * |Bp k|) + 2 * |c| := by linarith

end GroundTheory.Heights₂.Heights.AnalyticLimit
