module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicLocalQuotientMap
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

theorem _root_.GlobalTheory.T.holomorphic_local_quotient_map : ∀ (g' k g n : ℕ) (U : Set (Fin n → ℂ)) (e : Fin k → (Fin n → ℂ) → Fin g → ℂ) (t₀ : Fin n → ℂ), IsOpen U → t₀ ∈ U → k + g' = g → (∀ i, DifferentiableOn ℂ (e i) U) → LinearIndependent ℂ (fun i => e i t₀) → ∃ V : Set (Fin n → ℂ), IsOpen V ∧ t₀ ∈ V ∧ V ⊆ U ∧ ∃ q : (Fin n → ℂ) → (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), (∀ x, DifferentiableOn ℂ (fun t => q t x) V) ∧ ∀ t ∈ V, Function.Surjective (q t) ∧ LinearMap.ker (q t) = Submodule.span ℂ (Set.range fun i => e i t) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.QuotHol.exists_holomorphic_quotient | exact GlobalTheory.CompanionTheory.Metric.QuotHol.exists_holomorphic_quotient | (intros; apply GlobalTheory.CompanionTheory.Metric.QuotHol.exists_holomorphic_quotient <;> assumption)
