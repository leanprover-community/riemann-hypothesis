module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqOfIsAlgebraic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.L2.Host GlobalTheory.Published GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain

namespace GlobalTheory.HilbertInClosure

theorem rayField_top_maximal_unramified : GlobalArtinReciprocity → ∀ (E : Type) [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] (j : E →ₐ[ℚ] Qb) (ι : Qb →+* ℂ) (M : IntermediateField ℚ ℂ),
    IsRayFieldIn (ι.comp j.toRingHom) ⊤ M →
    ∃ _ : NumberField (qb ι M),
      (j.fieldRange ≤ qb ι M ∧
        (∀ σ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → ∀ y ∈ qb ι M, σ y ∈ qb ι M) ∧
        ∀ σ τ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → (∀ x ∈ j.fieldRange, τ x = x) →
          ∀ y ∈ qb ι M, σ (τ y) = τ (σ y)) ∧
      (discr (qb ι M)).natAbs = (discr E).natAbs ^ (Module.finrank ℚ (qb ι M) / Module.finrank ℚ E) ∧
      ∀ (L : Fld) [NumberField L],
        (j.fieldRange ≤ L ∧ (∀ σ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → ∀ y ∈ L, σ y ∈ L) ∧
          ∀ σ τ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ j.fieldRange, σ x = x) → (∀ x ∈ j.fieldRange, τ x = x) →
            ∀ y ∈ L, σ (τ y) = τ (σ y)) →
        (discr L).natAbs = (discr E).natAbs ^ (Module.finrank ℚ L / Module.finrank ℚ E) → L ≤ qb ι M := by
  intro H E _ _ _ j ι M hM
  obtain ⟨hN, h, hst, hc, hd, hmax⟩ := hilbert_qb_aut H E j ι M hM
  have hm : ∀ σ : Qb ≃ₐ[ℚ] Qb, σ ∈ GalOf j.fieldRange ↔ ∀ x ∈ j.fieldRange, σ x = x := fun σ =>
    IntermediateField.mem_fixingSubgroup_iff _ _
  exact ⟨hN, ⟨h, fun σ hσ => hst σ ((hm σ).2 hσ), fun σ τ hσ hτ => hc σ ((hm σ).2 hσ) τ ((hm τ).2 hτ)⟩, hd,
    fun L _ hL => hmax L hL.1 fun σ hσ τ hτ => hL.2.2 σ τ ((hm σ).1 hσ) ((hm τ).1 hτ)⟩

end GlobalTheory.HilbertInClosure

end
