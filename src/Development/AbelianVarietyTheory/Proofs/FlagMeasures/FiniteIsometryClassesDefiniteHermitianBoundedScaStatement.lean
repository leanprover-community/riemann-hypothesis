module

public import Formalism.HermitianLattices.StatementLat
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteIsometryClassesDefiniteHermitianBoundedSca
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

open NumberField

theorem _root_.GlobalTheory.T.finite_isometryClasses_definiteHermitian_boundedScale : ∀ {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm → (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) → ∀ (d c : ℕ), 0 < d → 0 < c → ∃ s : Finset (Submodule (𝓞 K) V), (∀ M₀ ∈ s, Submodule.IsLattice K M₀) ∧ ∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M → (∀ x ∈ M, ∀ y ∈ M, (d : K) * h x y ∈ Set.range (algebraMap (𝓞 K) K)) → (∀ y : V, (∀ x ∈ M, h x y ∈ Set.range (algebraMap (𝓞 K) K)) → (c : K) • y ∈ M) → ∃ M₀ ∈ s, ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g M₀ = M := by
  first | exact @GlobalTheory.hermLat_boundedScaleDual_finite | exact GlobalTheory.hermLat_boundedScaleDual_finite | (intros; apply GlobalTheory.hermLat_boundedScaleDual_finite <;> assumption)
