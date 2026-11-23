module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereChartDensityIntegral
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
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.monge_ampere_chart_density_integral : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (V B : Set (Fin e → ℂ)) (Φ : (Fin e → ℂ) → X) (P : Fin e → LocPot X) (g : X → ℝ) (j : Fin A.n), IsParam A V Φ → MeasurableSet B → B ⊆ V → (∀ z ∈ B, Φ z ∈ (A.chart j).source) → (∀ z ∈ B, ∀ i, IsTwiceDifferentiableAt A (P i) (Φ z)) → MeasurableSet ((A.chart j ∘ Φ) '' B) ∧ (IntegrableOn (fun y => g ((A.chart j).symm y) * locDens A P j y) ((A.chart j ∘ Φ) '' B) ↔ IntegrableOn (fun z => g (Φ z) * paramDens P Φ z) B) ∧ ∫ y in (A.chart j ∘ Φ) '' B, g ((A.chart j).symm y) * locDens A P j y = ∫ z in B, g (Φ z) * paramDens P Φ z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.param_chart_changeOfVariables | exact GlobalTheory.CompanionTheory.Ar.PB.param_chart_changeOfVariables | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.param_chart_changeOfVariables <;> assumption)
