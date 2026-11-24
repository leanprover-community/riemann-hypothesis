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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.A (coordDiv)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)

theorem BdEqHolo.proof : BdEqHolo.Statement := by
  intro X _ D A R j
  refine ⟨fun m v hv => ?_, fun y hy => ?_⟩
  · have h : AnalyticAt ℂ (R.ψ j ∘ (A.chart m).symm) v := (R.compat j m).1 v ⟨hv.1, hv.2.1⟩
    have hi : ∀ i, AnalyticAt ℂ (fun w => (R.ψ j ∘ (A.chart m).symm) w i) v :=
      (analyticAt_pi_iff (f := fun i w => (R.ψ j ∘ (A.chart m).symm) w i)).1 h
    show AnalyticAt ℂ (fun w => ∏ i ∈ R.S j, (R.ψ j ∘ (A.chart m).symm) w i) v
    exact Finset.analyticAt_fun_prod _ fun i _ => hi i
  · have hmem := R.mem_Yo_iff j (R.ψ j y) hy.2
    rw [(R.ψ j).left_inv hy.1] at hmem
    rw [hmem, not_not]
    simp only [bdEq, Finset.prod_eq_zero_iff, coordDiv, Set.mem_ofPred_eq]

end GroundTheory.Heights₂.Heights.AnalyticLimit
