module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsNormEmbId
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientIntegrableSquare
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.matrix_coefficient_integrable_square : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] (ρ : Γ → (B →L[ℂ] B)), IsU ρ → ∀ v : B, Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν → ∀ b : B,
    Integrable (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) ν ∧
    ∫ g, ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 ∂ν ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.GodementCoeff.sq_integrable_and_bound | exact GlobalTheory.CompanionTheory.GodementCoeff.sq_integrable_and_bound | (intros; apply GlobalTheory.CompanionTheory.GodementCoeff.sq_integrable_and_bound <;> assumption)
