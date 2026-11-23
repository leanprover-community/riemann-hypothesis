module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetLIntegralAverageAbelianQuotient
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

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.setLIntegral_average_abelian_quotient_alt : ∀ (G A : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableNeg A] (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant] (Γ U : Subgroup G) [DiscreteTopology Γ], IsClosed (U : Set G) → (∀ γ ∈ Γ, ∀ u ∈ U, γ⁻¹ * u * γ ∈ U) → (∃ K : Set G, IsCompact K ∧ ∀ u ∈ U, ∃ γ ∈ Γ, γ ∈ U ∧ γ * u ∈ K) → ∀ (ι : A → G), (∀ x y, ι (x + y) = ι x * ι y) → Measurable ι → (∀ x, ι x ∈ U) → ∀ (ν : Measure A) [SigmaFinite ν] [ν.IsAddLeftInvariant] (A₀ : AddSubgroup A) [Countable A₀], (∀ b ∈ A₀, ι b ∈ Γ) → ∀ (D : Set A), IsAddFundamentalDomain A₀ D ν → ν D = 1 → ∀ (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ (Φ : G → ENNReal), Measurable Φ → (∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) → (∀ u ∈ U, ∃ y : A, ∀ g, Φ (u * g) = Φ (ι y * g)) → ∫⁻ g in 𝓕, Φ g ∂μ = ∫⁻ g in 𝓕, ∫⁻ y in D, Φ (ι y * g) ∂ν ∂μ := by
  first | exact @GlobalTheory.UnipAvg.setLIntegral_average_abelian_quotient | exact GlobalTheory.UnipAvg.setLIntegral_average_abelian_quotient | (intros; apply GlobalTheory.UnipAvg.setLIntegral_average_abelian_quotient <;> assumption)
