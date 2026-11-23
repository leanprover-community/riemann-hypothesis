module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

namespace GlobalTheory.CompanionTheory.Ar.PB.NullLocal

theorem isNull_of_locally_in_zeros (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X)
    (Z : Set X)
    (hZ : ∀ x ∈ Z, ∃ (W : Set X) (f : X → ℂ), IsOpen W ∧ x ∈ W ∧ A.HoloOn W f ∧
      (∀ y ∈ W ∩ Z, f y = 0) ∧ ∀ V, IsOpen V → V.Nonempty → V ⊆ W → ∃ y ∈ V, f y ≠ 0) :
    IsNull A Z := by
  intro j
  refine measure_null_of_locally_null _ fun w hw => ?_
  obtain ⟨hwt, hwZ⟩ := hw
  obtain ⟨W, f, hWo, hxW, hf, hfZ, hne⟩ := hZ _ hwZ
  have hOo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) :=
    (A.chart j).isOpen_inter_preimage_symm hWo
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hOo w ⟨hwt, hxW⟩
  have hV : IsOpen ((A.chart j).symm '' Metric.ball w r) :=
    (A.chart j).isOpen_image_symm_of_subset_target Metric.isOpen_ball
      fun z hz => (hrO hz).1
  obtain ⟨y, ⟨z, hz, rfl⟩, hy⟩ := hne _ hV ⟨_, w, Metric.mem_ball_self hr, rfl⟩ (by
    rintro _ ⟨z, hz, rfl⟩
    exact (hrO hz).2)
  have hnull := ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd (U := Metric.ball w r)
    Metric.isOpen_ball (convex_ball w r).isPreconnected
    (f := f ∘ (A.chart j).symm) ((hf j).mono hrO) ⟨z, hz, hy⟩
  refine ⟨((A.chart j).target ∩ (A.chart j).symm ⁻¹' Z) ∩ Metric.ball w r,
    inter_mem_nhdsWithin _ (Metric.ball_mem_nhds w hr), measure_mono_null ?_ hnull⟩
  rintro v ⟨⟨-, hvZ⟩, hvb⟩
  exact ⟨hvb, hfZ _ ⟨(hrO hvb).2, hvZ⟩⟩

end GlobalTheory.CompanionTheory.Ar.PB.NullLocal
