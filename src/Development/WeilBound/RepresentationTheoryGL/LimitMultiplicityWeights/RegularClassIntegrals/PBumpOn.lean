module

public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel

theorem bumpOn : BumpOn := by
  intro H _ _ _ _ _ _ _ _ n ι hemb C hC
  have hK : IsCompact (matCoord ι '' C) := hC.image hemb.continuous
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  let f : ContDiffBump (0 : Fin n → Fin n → ℂ) :=
    ⟨max r 1, max r 1 + 1, lt_of_lt_of_le one_pos (le_max_right _ _), by linarith⟩
  refine ⟨fun g => ((f (matCoord ι g) : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
  · refine HasCompactSupport.intro (hemb.isCompact_preimage (isCompact_closedBall (0 : Fin n → Fin n → ℂ) (max r 1 + 1))) ?_
    intro g hg
    simp only [Set.mem_preimage, Metric.mem_closedBall, not_le] at hg
    have : f (matCoord ι g) = 0 := f.zero_of_le_dist hg.le
    simp [this]
  · refine ⟨fun x => ((f x : ℝ) : ℂ), ?_, fun g => rfl⟩
    exact Complex.ofRealCLM.contDiff.comp f.contDiff
  · intro y hy
    have hm : matCoord ι y ∈ Metric.closedBall (0 : Fin n → Fin n → ℂ) (max r 1) :=
      Metric.closedBall_subset_closedBall (le_max_left _ _) (hr ⟨y, hy, rfl⟩)
    have : f (matCoord ι y) = 1 := f.one_of_mem_closedBall hm
    simp [this]

end MainStatements.WeightKernel

end
