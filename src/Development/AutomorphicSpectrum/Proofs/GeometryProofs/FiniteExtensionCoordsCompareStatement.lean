module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteExtensionCoordsCompare
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.finite_extension_coords_compare : ∀ (Ω₁ Ω₂ Ω : Type) [Field Ω₁] [Field Ω₂] [Field Ω] [CharZero Ω] (i₁ : Ω₁ →+* Ω) (i₂ : Ω₂ →+* Ω) (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (J₁ : K₁ → Type) (J₂ : K₂ → Type) [∀ k, Fintype (J₁ k)] [∀ k, Fintype (J₂ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (y₂ : (Σ k, J₂ k) → Ω₂) (X₁ X₂ : Scheme.{0}) (ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω₂) ⟶ X₂), (letI := i₁.toAlgebra; Module.Finite Ω₁ Ω) → (∀ q : X₁, genPt ξ₁ ⤳ q) → (∀ q : X₂, genPt ξ₂ ⤳ q) → CoordTie ℤ ξ₁ (fun c' : (k : K₁) → J₁ k => ∏ k, y₁ ⟨k, c' k⟩) → CoordTie ℤ ξ₂ (fun c' : (k : K₂) → J₂ k => ∏ k, y₂ ⟨k, c' k⟩) → ∃ (m : ℕ) (w : Fin m → Ω) (y : (Σ k : K₁ ⊕ K₂ ⊕ Unit, Sum.elim J₁ (Sum.elim J₂ fun _ => Fin m) k) → Ω) (Z : Scheme.{0}) (ξ : Spec (CommRingCat.of Ω) ⟶ Z) (h₁ : Z ⟶ X₁) (h₂ : Z ⟶ X₂), (∀ k a, y ⟨.inl k, a⟩ = i₁ (y₁ ⟨k, a⟩)) ∧ (∀ k a, y ⟨.inr (.inl k), a⟩ = i₂ (y₂ ⟨k, a⟩)) ∧ (∀ a, y ⟨.inr (.inr ()), a⟩ = w a) ∧ (∀ q : Z, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ (fun c' : (k : K₁ ⊕ K₂ ⊕ Unit) → Sum.elim J₁ (Sum.elim J₂ fun _ => Fin m) k => ∏ k, y ⟨k, c' k⟩) ∧ (∀ q : Z, IsDomain (Z.presheaf.stalk q) ∧ IsIntegrallyClosed (Z.presheaf.stalk q)) ∧ Dominates ξ ξ₁ h₁ i₁ ∧ Dominates ξ ξ₂ h₂ i₂ := by
  exact @GlobalTheory.CompanionTheory.Ar.HtJoin.exists_normal_join
