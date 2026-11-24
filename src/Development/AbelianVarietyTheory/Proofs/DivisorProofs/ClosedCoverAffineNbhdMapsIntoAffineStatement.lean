module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedCoverAffineNbhdMapsIntoAffine
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.exists_affine_nbhd_preimage_le_of_closed_cover : ∀ (Y Y₁ Y₂ X : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) [IsClosedImmersion j₁] [IsClosedImmersion j₂] (a₁ : Y₁ ⟶ X) (a₂ : Y₂ ⟶ X), (∀ y : Y, (∃ y₁, j₁ y₁ = y) ∨ ∃ y₂, j₂ y₂ = y) → (∀ (y₁ : Y₁) (y₂ : Y₂), j₁ y₁ = j₂ y₂ → a₁ y₁ = a₂ y₂) → ∀ y : Y, ∃ (W : Y.Opens) (U : X.affineOpens), IsAffineOpen W ∧ y ∈ W ∧ j₁ ⁻¹ᵁ W ≤ a₁ ⁻¹ᵁ U.1 ∧ j₂ ⁻¹ᵁ W ≤ a₂ ⁻¹ᵁ U.1 := by
  first | exact @GlobalTheory.closedCover_affine_nbhd_maps_into_affine | exact GlobalTheory.closedCover_affine_nbhd_maps_into_affine | (intros; apply GlobalTheory.closedCover_affine_nbhd_maps_into_affine <;> assumption)
