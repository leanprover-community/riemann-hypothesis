module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeightBruhatFundamentalDomainCentralizer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Set GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_weight_bruhat_fundamental_domain_centralizer : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [DiscreteTopology Γ] (γ : H), IsMulCommutative (cent γ) → ∀ (μ : Measure H) [μ.IsHaarMeasure] (dt : Measure (cent γ)) [dt.IsHaarMeasure] (𝓣 : Set (cent γ)), IsFundamentalDomain (Γ.subgroupOf (cent γ)) 𝓣 dt → ∃ α : H → ℝ≥0∞, Measurable α ∧ (∀ y, ∑' h : Γ.subgroupOf (cent γ), α (((h : cent γ) : H) * y) = 1) ∧ ∀ ψ : H → ℝ≥0∞, Measurable ψ → LeftInv (cent γ) ψ → ∫⁻ y, α y * ψ y ∂μ = dt 𝓣 * ∫⁻ q, descend (cent γ) ψ q ∂(quotMeas (cent γ) dt μ) := by
  exact @GlobalTheory.WeightUnfold.exists_weight
