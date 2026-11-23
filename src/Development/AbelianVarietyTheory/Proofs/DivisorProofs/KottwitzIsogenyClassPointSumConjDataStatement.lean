module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PointSide
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzIsogenyClassPointSumConjData
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.kottwitzIsogenyClassPointSum_conj_data : ∀ {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ g₁ : G₁) (δ g₂ : G₂) (f : G₁ → ℂ) (φ : G₂ → ℂ), (∀ k ∈ K₁, ∀ x, f (k⁻¹ * x * k) = f x) → (∀ k ∈ K₂, ∀ x, φ (k⁻¹ * x * θ k) = φ x) → (∀ y, ι₁ y * γ = γ * ι₁ y) → (∀ y, ι₂ y * δ = δ * θ (ι₂ y)) → pointSum ((MulAut.conj g₁⁻¹).toMonoidHom.comp ι₁) ((MulAut.conj g₂⁻¹).toMonoidHom.comp ι₂) θ K₁ K₂ (g₁⁻¹ * γ * g₁) (g₂⁻¹ * δ * θ g₂) f φ = pointSum ι₁ ι₂ θ K₁ K₂ γ δ f φ := by
  first | (exact @GlobalTheory.PointSumConj.pointSum_conj_data) | (exact GlobalTheory.PointSumConj.pointSum_conj_data) | (intros; apply GlobalTheory.PointSumConj.pointSum_conj_data  <;> assumption)
