module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumSetIntegralEqZeroOfStabilizer
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

open MeasureTheory

theorem _root_.GlobalTheory.T.tsum_setIntegral_eq_zero_of_stabilizer_integrals : ∀ {G X : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (ν : Measure G) [ν.IsMulLeftInvariant], SFinite ν → ∀ (Λ : Subgroup G), Countable Λ → ∀ 𝓖 : Set G, IsFundamentalDomain Λ 𝓖 ν → ∀ (a : Λ → X → X), (∀ x, a 1 x = x) → (∀ γ δ x, a (γ * δ) x = a γ (a δ x)) → ∀ F : X → G → ℂ, (∀ γ x g, F (a γ x) g = F x ((γ : G)⁻¹ * g)) → (∀ x, AEStronglyMeasurable (F x) ν) → ∑' x, ∫⁻ g in 𝓖, ‖F x g‖ₑ ∂ν ≠ ⊤ → (∀ x (Γ : Subgroup G), (∀ g, g ∈ Γ ↔ ∃ h : g ∈ Λ, a ⟨g, h⟩ x = x) → ∀ 𝓓 : Set G, IsFundamentalDomain Γ 𝓓 ν → IntegrableOn (F x) 𝓓 ν → ∫ g in 𝓓, F x g ∂ν = 0) → ∑' x, ∫ g in 𝓖, F x g ∂ν = 0 := by
  first | exact @GlobalTheory.tsum_setIntegral_eq_zero_of_stabilizer | exact GlobalTheory.tsum_setIntegral_eq_zero_of_stabilizer | (intros; apply GlobalTheory.tsum_setIntegral_eq_zero_of_stabilizer <;> assumption)
