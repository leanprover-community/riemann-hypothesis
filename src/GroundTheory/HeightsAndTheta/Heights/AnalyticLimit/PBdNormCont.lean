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
import Mathlib.Tactic.Linter.Style
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

open Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas)

theorem BdNormCont.proof (hCC : ChartCont.Statement) (hEq : BdEqHolo.Statement) :
    BdNormCont.Statement := by
  intro X _ D A R φ hφ c
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  set j := bdIdx R y₀
  have hU : IsOpen (bdDom R j) := isOpen_bdDom R j
  have hy₀ : y₀ ∈ bdDom R j := mem_bdDom_bdIdx R y₀
  have hEqc : ContinuousOn (bdEq R j) (bdDom R j) := (hCC D A _ hU).2 _ (hEq D A R j).1
  have hφc : ContinuousOn (φ j) (bdDom R j) := (hCC D A _ hU).1 _ (hφ.1 j)
  have hg : ContinuousOn (fun y => ‖bdEq R j y‖ * Real.exp (-(φ j y + c))) (bdDom R j) :=
    hEqc.norm.mul ((hφc.add continuousOn_const).neg.rexp)
  have hgy : ContinuousAt (fun y => ‖bdEq R j y‖ * Real.exp (-(φ j y + c))) y₀ :=
    hg.continuousAt (hU.mem_nhds hy₀)
  refine hgy.congr ?_
  filter_upwards [hU.mem_nhds hy₀] with y hy
  have hk : y ∈ bdDom R (bdIdx R y) ∩ bdDom R j := ⟨mem_bdDom_bdIdx R y, hy⟩
  have h3 := hφ.2.2 (bdIdx R y) j y hk
  show ‖bdEq R j y‖ * Real.exp (-(φ j y + c)) = ‖bdSec R y y‖ * Real.exp (-(bdPot R φ c).φ y y)
  simp only [bdSec, bdPot]
  simp only [neg_add, Real.exp_add, ← mul_assoc, h3]

end GroundTheory.Heights₂.Heights.AnalyticLimit
