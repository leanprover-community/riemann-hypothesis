module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomDescendsToSubfieldContainingFinset
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.hom_descends_to_subfield_containing_finset_alt : ∀ (k K : Type) [Field k] [Field K] (σ : k →+* K) (X Y : Over (Sp K)) (X₀ Y₀ : Over (Sp k)) (φ : X.left ⟶ X₀.left) (ψ : Y.left ⟶ Y₀.left), IsPullback φ X.hom X₀.hom (spMap σ) → IsPullback ψ Y.hom Y₀.hom (spMap σ) → QuasiCompact X.hom → QuasiSeparated X.hom → LocallyOfFiniteType Y.hom → ∀ f : X ⟶ Y, ∃ s : Finset K, ∀ (k₁ : Type) [Field k₁] (α : k →+* k₁) (β : k₁ →+* K), β.comp α = σ → (s : Set K) ⊆ Set.range β → ∀ (X₁ Y₁ : Over (Sp k₁)) (φ₁ : X.left ⟶ X₁.left) (χ : X₁.left ⟶ X₀.left) (ψ₁ : Y.left ⟶ Y₁.left) (ω : Y₁.left ⟶ Y₀.left), IsPullback χ X₁.hom X₀.hom (spMap α) → IsPullback ω Y₁.hom Y₀.hom (spMap α) → φ₁ ≫ χ = φ → ψ₁ ≫ ω = ψ → φ₁ ≫ X₁.hom = X.hom ≫ spMap β → ψ₁ ≫ Y₁.hom = Y.hom ≫ spMap β → ∃ f₁ : X₁ ⟶ Y₁, φ₁ ≫ f₁.left = f.left ≫ ψ₁ := by
  first | exact @GlobalTheory.hom_descends_to_subfield_containing_finset | exact GlobalTheory.hom_descends_to_subfield_containing_finset | (intros; apply GlobalTheory.hom_descends_to_subfield_containing_finset <;> assumption)
