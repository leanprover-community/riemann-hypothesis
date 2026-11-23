module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralFibreSumChangeOfVariables
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
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.integral_fibre_sum_change_of_variables : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (q : X → Fin e → ℂ) (S : Set X) (G : X → ℝ), (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0) → (∀ x ∉ S, ∀ j, x ∈ (A.chart j).source → AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧ LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) → (∀ y, (q ⁻¹' {y} \ S).Finite) → (∀ x ∉ S, ∀ i k, x ∈ (A.chart k).source → ContDiffAt ℝ 2 ((Φ i).φ x ∘ (A.chart k).symm) (A.chart k x)) → MIntegrable A Φ G → Integrable (fun y => ∑ᶠ x ∈ q ⁻¹' {y} \ S, G x * pushDens A Φ q x) ∧ mInt A Φ G = ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} \ S, G x * pushDens A Φ q x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Push.integrable_mInt_fibreSum | exact GlobalTheory.CompanionTheory.Ar.Giv.Push.integrable_mInt_fibreSum | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Push.integrable_mInt_fibreSum <;> assumption)
