module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteIrreducibleFixedVectors
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

theorem _root_.GlobalTheory.T.k_finite_irreducible_fixed_vectors : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (H : Submodule ℂ (L2 (latticeGL E a) μ)), H ≤ L2cusp μ → IsIrredSubrep (R (latticeGL E a) μ) H → ∀ F ∈ H, IsKFinL2 μ F → ∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧ IsCompact (U : Set (GL (Fin a) (Af E))) ∧ ∃ X : Submodule ℂ (L2 (latticeGL E a) μ), FiniteDimensional ℂ X ∧ F ∈ X ∧ X ≤ H ∧ (∀ (k : Kinf E a), ∀ v ∈ X, R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) v ∈ X) ∧ (∀ u ∈ U, ∀ v ∈ X, R (latticeGL E a) μ (finGL E a u) v = v) ∧ ∀ B : L2 (latticeGL E a) μ →ₗ[ℂ] L2 (latticeGL E a) μ, (∀ (k : Kinf E a) v, B (R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) v) = R (latticeGL E a) μ (infGL E a (Unitary.toUnits k)) (B v)) → (∀ v ∈ H, (∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v) → B v ∈ H ∧ ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) (B v) = B v) → ∀ v ∈ X, B v ∈ X := by
  first | exact @GlobalTheory.CompanionTheory.TypeSpace.exists_typeSpace | exact GlobalTheory.CompanionTheory.TypeSpace.exists_typeSpace | (intros; apply GlobalTheory.CompanionTheory.TypeSpace.exists_typeSpace <;> assumption)
