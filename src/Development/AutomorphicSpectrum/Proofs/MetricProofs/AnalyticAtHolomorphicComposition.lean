module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem analyticAt_comp_of_holo_in_charts (e n : ℕ) (X : Type) [TopologicalSpace X]
    (A : FinHolAtlas n X) (Un : Set (Fin e → ℂ)) (bp : (Fin e → ℂ) → X) (w₀ : Fin e → ℂ)
    (W : Set X) (f : X → ℂ) (hUn : IsOpen Un) (hw₀ : w₀ ∈ Un) (hc : ContinuousOn bp Un)
    (hb : ∀ k, AnalyticOnNhd ℂ (A.chart k ∘ bp) (Un ∩ bp ⁻¹' (A.chart k).source))
    (_hW : IsOpen W) (hwW : bp w₀ ∈ W) (hf : A.HoloOn W f) : AnalyticAt ℂ (f ∘ bp) w₀ := by
  obtain ⟨k, hk⟩ := A.cover (bp w₀)
  have hca : ContinuousAt bp w₀ := hc.continuousAt (hUn.mem_nhds hw₀)
  have h1 : AnalyticAt ℂ (A.chart k ∘ bp) w₀ := hb k w₀ ⟨hw₀, hk⟩
  have h2 : AnalyticAt ℂ (f ∘ (A.chart k).symm) ((A.chart k ∘ bp) w₀) := by
    apply hf k
    refine ⟨(A.chart k).map_source hk, ?_⟩
    show (A.chart k).symm (A.chart k (bp w₀)) ∈ W
    rw [(A.chart k).left_inv hk]
    exact hwW
  have h3 := h2.comp h1
  refine h3.congr ?_
  have hev : ∀ᶠ w in 𝓝 w₀, bp w ∈ (A.chart k).source :=
    hca ((A.chart k).open_source.mem_nhds hk)
  filter_upwards [hev] with w hw
  simp only [Function.comp_apply, (A.chart k).left_inv hw]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
