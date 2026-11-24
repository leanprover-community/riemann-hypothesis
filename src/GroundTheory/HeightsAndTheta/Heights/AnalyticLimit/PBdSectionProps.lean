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

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection)

theorem BdSectionProps.proof (hB : BdEqHolo.Statement) : BdSectionProps.Statement := by
  intro X _ D A R φ hφ c
  obtain ⟨h1, h2, h3⟩ := hφ
  refine ⟨⟨fun x j => ?_, fun x x' y hy => ?_⟩, ⟨fun x => (hB D A R _).1, fun x x' y hy => ?_⟩, ?_⟩
  · exact (h1 (bdIdx R x) j).add contDiffOn_const
  · obtain ⟨W, hW, hyW, G, hG, hGe⟩ := h2 (bdIdx R x) (bdIdx R x') y hy
    refine ⟨W, hW, hyW, G, hG, fun z hz => ?_⟩
    have h := hGe z ⟨hz.1.1, hz.1.2, hz.2⟩
    show (φ (bdIdx R x) z + c) - (φ (bdIdx R x') z + c) = (G z).re
    linarith
  · show ‖bdEq R (bdIdx R x) y‖ * Real.exp (-(φ (bdIdx R x) y + c)) =
      ‖bdEq R (bdIdx R x') y‖ * Real.exp (-(φ (bdIdx R x') y + c))
    simp only [neg_add, Real.exp_add, ← mul_assoc]
    rw [h3 _ _ y hy]
  · ext y
    have h := (hB D A R (bdIdx R y)).2 y (mem_bdDom_bdIdx R y)
    show bdEq R (bdIdx R y) y ≠ 0 ↔ y ∈ R.Yo
    rw [Ne, h, not_not]

end GroundTheory.Heights₂.Heights.AnalyticLimit
