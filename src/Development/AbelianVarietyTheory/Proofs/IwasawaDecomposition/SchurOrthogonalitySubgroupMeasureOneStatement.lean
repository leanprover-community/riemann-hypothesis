module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurOrthogonalitySubgroupMeasureOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.schur_orthogonality_subgroup_measure_one : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G] (ν : Measure G) [ν.IsMulLeftInvariant] (Ω : Subgroup G), MeasurableSet (Ω : Set G) → ν (Ω : Set G) = 1 → ∀ {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (ρ : G →* Module.End ℂ W), (∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) → (∀ x y : W, Measurable fun g => ⟪x, ρ g y⟫_ℂ) → (∀ U : Submodule ℂ W, (∀ g ∈ Ω, U.map (ρ g) ≤ U) → U = ⊥ ∨ U = ⊤) → ∀ a a' x x' : W, IntegrableOn (fun g => star ⟪a, ρ g⁻¹ x⟫_ℂ * ⟪a', ρ g⁻¹ x'⟫_ℂ) Ω ν ∧ (Module.finrank ℂ W : ℂ) * ∫ g in (Ω : Set G), star ⟪a, ρ g⁻¹ x⟫_ℂ * ⟪a', ρ g⁻¹ x'⟫_ℂ ∂ν = ⟪a', a⟫_ℂ * ⟪x, x'⟫_ℂ := by
  first | exact @GlobalTheory.SchurOrthOnSubgroup.schur_orthogonality | exact GlobalTheory.SchurOrthOnSubgroup.schur_orthogonality | (intros; apply GlobalTheory.SchurOrthOnSubgroup.schur_orthogonality <;> assumption)
