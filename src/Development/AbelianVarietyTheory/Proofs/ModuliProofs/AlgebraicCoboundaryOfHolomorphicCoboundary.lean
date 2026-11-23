module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNonzeroLocusLeOpenPolarisationComplexStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSectionOfLocallyRegularStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimitiveRegularOnSectionNonzeroLocusStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem top_le_preimage_of_mem {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (p : Sp ℂ) (U : X.Opens)
    (hp : x p ∈ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro q _
  obtain rfl : q = p := Subsingleton.elim q p
  exact hp

theorem algebraic_coboundary_of_holomorphic_coboundary : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (I : Type) (O : I → P₀.A.left.Opens) (c : ∀ i i', Γ(P₀.A.left, O i ⊓ O i')) (h : I → (Fin P₀.g → ℂ) → ℂ), ⨆ i, O i = ⊤ → (∀ i, DifferentiableOn ℂ (h i) {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i} ∧ ∀ (l : u.Λ) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i → h i (z + l) = h i z) → (∀ i i' z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (O i ⊓ O i') → valAt' (u.ex z).left (O i ⊓ O i') (c i i') = h i' z - h i z) → ∀ i, ∃ a : Γ(P₀.A.left, O i), ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i → valAt' (u.ex z).left (O i) a = h i z := by
  intro hL P₀ u Hm χ hU I O c h hcov hhol hcoc i

  refine (GlobalTheory.T.existsUnique_section_of_locally_given_values P₀ u Hm χ hU (O i) (h i) ?_).exists
  intro z hz
  obtain ⟨p⟩ : Nonempty (Sp ℂ) := inferInstance
  have hy : (u.ex z).left p ∈ O i := hz (Set.mem_univ p)
  obtain ⟨n, σ, hyσ, hσ⟩ := GlobalTheory.T.exists_nonzeroLocus_le_open_polarisation_complex hL P₀ (O i) _ hy
  obtain ⟨a, ha⟩ := GlobalTheory.T.primitive_regular_on_section_nonzeroLocus P₀ u Hm χ hU I O c h hcov hhol hcoc i n σ hσ
  exact ⟨Out.nonzeroLocus σ, a, hσ, top_le_preimage_of_mem _ p _ hyσ, ha⟩

end GlobalTheory.KS
