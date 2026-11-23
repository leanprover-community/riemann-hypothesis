module

public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalEigenIdempotentsOfSeparability
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_orthogonal_eigen_idempotents_of_separability : ∀ (R C K : Type) [CommRing R] [CommRing C] [CommRing K] (tR : R →+* C) (a : ℕ) (t : Fin a → (K →+* R)), (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) → ∀ (N : ℤ) (k : ℕ) (u v : Fin k → K), ∑ j, u j * v j = (N : K) → (∀ c : K, ∑ j, (c * u j) ⊗ₜ[ℤ] v j = ∑ j, u j ⊗ₜ[ℤ] (v j * c)) → IsUnit (N : C) → ∀ (H : Type*) [AddCommGroup H] [Module C H] (ρF : K →+* Module.End C H), ∃ φ : Fin a → Module.End C H, (∀ i c, ρF c * φ i = tR (t i c) • φ i) ∧ (∀ i j, φ i * φ j = if i = j then φ i else 0) ∧ (∀ g : Module.End C H, (∀ c, g * ρF c = ρF c * g) → ∀ i, g * φ i = φ i * g) ∧ (∀ F : Submodule C H, (∀ c, ∀ x ∈ F, ρF c x ∈ F) → ∀ i, ∀ x ∈ F, φ i x ∈ F) ∧ (∀ F : Submodule C H, (∀ c, ∀ x ∈ F, ρF c x ∈ F) → ∀ i w, (∀ c, ρF c w - tR (t i c) • w ∈ F) → ∀ j, φ j w - (if j = i then w else 0) ∈ F) := by
  first | exact @GlobalTheory.lie_idempotents | exact GlobalTheory.lie_idempotents | (intros; apply GlobalTheory.lie_idempotents <;> assumption)
