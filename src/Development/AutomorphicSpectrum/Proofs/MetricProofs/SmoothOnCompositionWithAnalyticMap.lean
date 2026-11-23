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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
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

theorem contDiffOn_comp_of_analytic_in_charts :
    ∀ (e n : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas n X) (Un : Set (Fin e → ℂ))
      (bp : (Fin e → ℂ) → X) (W : Set X) (f : X → ℝ), IsOpen Un → ContinuousOn bp Un →
      (∀ k, AnalyticOnNhd ℂ (A.chart k ∘ bp) (Un ∩ bp ⁻¹' (A.chart k).source)) →
      (∀ w ∈ Un, bp w ∈ W) → A.SmoothOn W f →
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ bp) Un := by
  intro e n X _ A Un bp W f hUn hbp hana hW hf w hw
  obtain ⟨k, hk⟩ := A.cover (bp w)
  have hV : IsOpen (Un ∩ bp ⁻¹' (A.chart k).source) :=
    hbp.isOpen_inter_preimage hUn (A.chart k).open_source
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (A.chart k ∘ bp) (Un ∩ bp ⁻¹' (A.chart k).source) :=
    ((hana k).contDiffOn hV.uniqueDiffOn).restrict_scalars ℝ
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ (A.chart k).symm)
      ((A.chart k).target ∩ (A.chart k).symm ⁻¹' W) := hf k
  have h3 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((f ∘ (A.chart k).symm) ∘ (A.chart k ∘ bp))
      (Un ∩ bp ⁻¹' (A.chart k).source) := by
    refine h2.comp h1 ?_
    intro x hx
    refine ⟨(A.chart k).map_source hx.2, ?_⟩
    show (A.chart k).symm (A.chart k (bp x)) ∈ W
    rw [(A.chart k).left_inv hx.2]
    exact hW x hx.1
  have h4 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f ∘ bp) (Un ∩ bp ⁻¹' (A.chart k).source) := by
    refine h3.congr ?_
    intro x hx
    simp only [Function.comp_apply, (A.chart k).left_inv hx.2]
  exact (h4.contDiffAt (hV.mem_nhds ⟨hw, hk⟩)).contDiffWithinAt

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
