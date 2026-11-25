module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQCoeffIffHasQExpansion
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
open Function

namespace GlobalTheory.FN

theorem hasQ_of_periodic_bounded : ∀ (N : ℕ) (f : ℍ → ℂ), 0 < N → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → (∀ τ : ℍ, f ((N : ℝ) +ᵥ τ) = f τ) → UpperHalfPlane.IsBoundedAtImInfty f → ∃ a, HasQ N f a := by
  intro N f hN hf hper hbdd
  refine ⟨fun n => PowerSeries.coeff n (UpperHalfPlane.qExpansion (N : ℝ) f), ?_⟩
  rw [GlobalTheory.QFam.hasQ_coeff_iff_hasQExpansion]
  exact GlobalTheory.HasQExpansion.of_periodic (by exact_mod_cast hN)
    (UpperHalfPlane.periodic_comp_ofComplex hper) hf hbdd

end GlobalTheory.FN
