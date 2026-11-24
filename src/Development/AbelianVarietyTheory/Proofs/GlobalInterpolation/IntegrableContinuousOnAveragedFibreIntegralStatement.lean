module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FibOfZero
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegrableContinuousOnAveragedFibreIntegral
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

@[expose] public section

open MeasureTheory Topology

theorem _root_.GlobalTheory.T.integrable_continuousOn_averagedFibreIntegral : ∀ (K V : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] [MeasurableSpace K] [BorelSpace K] [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K), Continuous q → (∀ (c : K) (x : V), q (c • x) = c ^ 2 * q x) → ∀ (U : Set K) (s : K → K), GlobalTheory.QuadFibre.IsSqrtOn U s → ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → (∀ t : K, t ≠ 0 → Integrable φ (GlobalTheory.QuadFibre.fibOf μ ν q U s t)) ∧ ContinuousOn (fun t => ∫ x, φ x ∂(GlobalTheory.QuadFibre.fibOf μ ν q U s t)) {t : K | t ≠ 0} := by
  first | exact @GlobalTheory.QuadFibre.integrable_and_continuousOn_fibOf | exact GlobalTheory.QuadFibre.integrable_and_continuousOn_fibOf | (intros; apply GlobalTheory.QuadFibre.integrable_and_continuousOn_fibOf <;> assumption)
