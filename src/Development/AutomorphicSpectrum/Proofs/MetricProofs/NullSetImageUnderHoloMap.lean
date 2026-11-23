module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.MeasureTheory.Function.Jacobian
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

namespace GlobalTheory.CompanionTheory.Ar.PB.NullImage

theorem isNull_image_of_holoMap : ∀ (e : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (h : Y → X) (Z : Set Y),
    HoloMap B A h → IsNull B Z → IsNull A (h '' Z) := by
  intro e X Y _ _ A B h Z hh hZ k
  have key : ∀ j, volume ((A.chart k ∘ h ∘ (B.chart j).symm) ''
      (((B.chart j).target ∩ (B.chart j).symm ⁻¹' Z) ∩
        ((B.chart j).target ∩ (B.chart j).symm ⁻¹' (h ⁻¹' (A.chart k).source)))) = 0 := by
    intro j
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
      (measure_mono_null Set.inter_subset_left (hZ j))
    intro z hz
    exact (((hh.2 j k z hz.2).differentiableAt.restrictScalars ℝ).differentiableWithinAt)
  refine measure_mono_null ?_ (measure_iUnion_null key)
  rintro w ⟨hw, y, hy, hyw⟩
  obtain ⟨j, hj⟩ := B.cover y
  have hsymm : (B.chart j).symm (B.chart j y) = y := (B.chart j).left_inv hj
  have hsrc : h y ∈ (A.chart k).source := by
    rw [hyw]
    exact (A.chart k).map_target hw
  refine Set.mem_iUnion.2 ⟨j, B.chart j y, ⟨⟨(B.chart j).map_source hj, ?_⟩,
    ⟨(B.chart j).map_source hj, ?_⟩⟩, ?_⟩
  · simpa [hsymm] using hy
  · simpa [hsymm] using hsrc
  · simp only [Function.comp_apply, hsymm, hyw]
    exact (A.chart k).right_inv hw

end GlobalTheory.CompanionTheory.Ar.PB.NullImage
