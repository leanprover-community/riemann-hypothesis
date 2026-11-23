module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PointSide
public import Mathlib.GroupTheory.Commensurable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPointCountOneClassCommensurable
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

theorem _root_.GlobalTheory.T.kottwitz_pointCount_one_class_commensurable : ∀ {Γ G₁ G₂ : Type} [Group Γ] [Group G₁] [Group G₂] (ι₁ : Γ →* G₁) (ι₂ : Γ →* G₂) (θ : G₂ →* G₂) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) (γ : G₁) (δ : G₂) (f₁ : G₁ → ℂ) (φ : G₂ → ℂ), (∀ g : G₁, Subgroup.Commensurable (K₁.map (MulAut.conj g).toMonoidHom) K₁) → (∀ g : G₂, Subgroup.Commensurable (K₂.map (MulAut.conj g).toMonoidHom) K₂) → K₂.map θ ≤ K₂ → (∀ k ∈ K₁, ∀ x, f₁ (k⁻¹ * x * k) = f₁ x) → (∀ k ∈ K₂, ∀ x, φ (k⁻¹ * x * θ k) = φ x) → (∀ g : Γ, ι₁ g * γ = γ * ι₁ g) → (∀ g : Γ, ι₂ g * δ = δ * θ (ι₂ g)) → Function.Injective (ι₁.prod ι₂) → (∀ x : G₁ × G₂, Finite (stab ι₁ ι₂ K₁ K₂ x)) → {q : DoubleCoset.Quotient ((ι₁.prod ι₂).range : Set (G₁ × G₂)) ((K₁.prod K₂ : Subgroup (G₁ × G₂)) : Set (G₁ × G₂)) | f₁ ((Quotient.out q).1⁻¹ * γ * (Quotient.out q).1) * φ ((Quotient.out q).2⁻¹ * δ * θ (Quotient.out q).2) ≠ 0}.Finite → pointSum ι₁ ι₂ θ K₁ K₂ γ δ f₁ φ = pointSide ι₁ ι₂ θ K₁ K₂ γ δ f₁ φ := by
  first | (exact @GlobalTheory.LKCountComm.pointSum_eq_pointSide_of_commensurable) | (exact GlobalTheory.LKCountComm.pointSum_eq_pointSide_of_commensurable) | (intros; apply GlobalTheory.LKCountComm.pointSum_eq_pointSide_of_commensurable  <;> assumption)
