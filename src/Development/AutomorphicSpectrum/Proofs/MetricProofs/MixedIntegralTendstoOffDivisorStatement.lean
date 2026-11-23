module

public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralTendstoOffDivisor
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

theorem _root_.GlobalTheory.T.mixed_integral_tendsto_off_divisor : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) (Θ : LocPot X), IsPotential A Θ → IsPosPot A Θ → ∀ (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (fT : Fin e → ℝ → X → ℝ) (G : X → ℝ) (GT : ℝ → X → ℝ) (C : ℝ), (∀ i, IsPotential A (P i)) → (∀ i, A.SmoothOn R.Yo (f i)) → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, A.Smooth (fT i t) ∧ IsPsh A (P i + LocPot.ofFun (fT i t) + Θ) ∧ ∀ x ∈ R.Yo, |fT i t x| ≤ C + C * Real.log (R.r x) ∧ fT i t x ≤ C) → (∀ i, ∀ j, ∀ K' ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yo, IsCompact K' → TendstoUniformlyOn (fun t => fT i t ∘ (A.chart j).symm) (f i ∘ (A.chart j).symm) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fT i t ∘ (A.chart j).symm)) (fderiv ℝ (f i ∘ (A.chart j).symm)) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (fT i t ∘ (A.chart j).symm))) (fderiv ℝ (fderiv ℝ (f i ∘ (A.chart j).symm))) (𝓝[>] 0) K') → (∀ᶠ t in 𝓝[>] (0 : ℝ), @Measurable X ℝ (borel X) _ (R.Yo.indicator (GT t)) ∧ ∀ x ∈ R.Yo, |GT t x| ≤ C + C * Real.log (R.r x)) → (∀ K' ⊆ R.Yo, IsCompact K' → TendstoUniformlyOn GT G (𝓝[>] 0) K') → MIntegrable A (fun i => P i + LocPot.ofFun (f i)) G ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), MIntegrable A (fun i => P i + LocPot.ofFun (fT i t)) (GT t)) ∧ Tendsto (fun t => mInt A (fun i => P i + LocPot.ofFun (fT i t)) (GT t)) (𝓝[>] 0) (𝓝 (mInt A (fun i => P i + LocPot.ofFun (f i)) G)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.mixed_integral_tendsto_of_C2_off_divisor | exact GlobalTheory.CompanionTheory.Ar.Giv.mixed_integral_tendsto_of_C2_off_divisor | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.mixed_integral_tendsto_of_C2_off_divisor <;> assumption)
