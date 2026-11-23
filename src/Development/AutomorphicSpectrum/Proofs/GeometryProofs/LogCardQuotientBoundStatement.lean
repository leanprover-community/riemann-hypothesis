module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogCardQuotientBound
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.log_card_quotient_bound : ∀ (L : Type) [Field L] [NumberField L] (Bc : Type) [AddCommGroup Bc] [Module (𝓞 L) Bc]
    (F₀ F₁ : Submodule (𝓞 L) Bc) (φ : F₁ →ₗ[𝓞 L] L) (s : F₁) (m : ℕ) (ρ : FinitePlace L → ℝ),
    F₁.FG → (∀ x, φ x = 0 ↔ (x : Bc) ∈ F₀) → φ s ≠ 0 → 0 < m → (∀ v, 0 < ρ v) → (Function.mulSupport ρ).Finite →
    (∀ v : FinitePlace L, (∀ x, v (φ x) ≤ (v (m : L))⁻¹ * ρ v) ∧ ∃ x, v (m : L) * ρ v ≤ v (φ x)) →
    |Real.log (Nat.card (F₁ ⧸ (F₀ ⊔ Submodule.span (𝓞 L) {(s : Bc)}).comap F₁.subtype)) -
      ∑ᶠ v : FinitePlace L, (Real.log (ρ v) - Real.log (v (φ s)))| ≤ Module.finrank ℚ L * Real.log m := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.log_index_le | exact GlobalTheory.CompanionTheory.Ar.RootHt.log_index_le | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.log_index_le <;> assumption)
