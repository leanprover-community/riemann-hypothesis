module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFundamentalDomainEqSumDoubleCosetUnfold
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
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.integral_fundamentalDomain_eq_sum_doubleCoset_unfold : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant] (Γ Ω : Subgroup G) [Countable Γ] (𝓖 : Set G), IsFundamentalDomain Γ 𝓖 ν → IsOpen (Ω : Set G) → ∀ (ι : Type) [Fintype ι] (h : ι → G), (∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ Ω, x = γ * h i * k) → (∀ i, {γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ Ω}.Finite) → ∀ f : G → ℂ, (∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) → (∀ i, IntegrableOn (fun k => f (h i * k)) Ω ν) → IntegrableOn f 𝓖 ν ∧ ∫ x in 𝓖, f x ∂ν = ∑ i, (({γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ Ω}.ncard : ℕ) : ℂ)⁻¹ * ∫ k in (Ω : Set G), f (h i * k) ∂ν := by
  first | exact @GlobalTheory.Unfold.integral_fundamentalDomain_eq_sum_unfold | exact GlobalTheory.Unfold.integral_fundamentalDomain_eq_sum_unfold | (intros; apply GlobalTheory.Unfold.integral_fundamentalDomain_eq_sum_unfold <;> assumption)
