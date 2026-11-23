module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffBoundaryParts
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeFormCompare
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
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A

noncomputable section

theorem EnergyDensNonneg.proof : EnergyDensNonneg.Statement := by
  intro n d s y v hs
  have hV : IsOpen {z | AnalyticAt ℂ s z} := isOpen_analyticAt ℂ s
  have hC : ∀ z ∈ {z | AnalyticAt ℂ s z}, ContDiffAt ℝ 2 (euclPot ∘ s) z := fun z hz =>
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp z
      (hz.restrictScalars (𝕜 := ℝ)).contDiffAt
  refine gradDensNonneg_thm d (fun _ => euclPot ∘ s) v _ hV
    (fun _ => fun z hz => (hC z hz).contDiffWithinAt) ?_ y hs
  intro _ z hz ξ
  rw [levi_comp ξ hz ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt,
    TubeFormComparison.levi_euclPot]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

end

end GroundTheory.Heights₂.Heights
