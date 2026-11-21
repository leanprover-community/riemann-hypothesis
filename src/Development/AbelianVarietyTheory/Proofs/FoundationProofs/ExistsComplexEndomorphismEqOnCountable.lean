import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableComb
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
import BuildAid.ForwardExisting

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.GalTheta

theorem exists_top_embedding_eq_on_countable (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (S : Set ℂ)
    (hS : S.Countable) :
    ∃ σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ, ∀ x ∈ S, x ∈ M → cj ⊤ σ x = cj M ρ x := by
  let A : Set M := {y | (y : ℂ) ∈ S}
  have hA : A.Countable := hS.preimage Subtype.val_injective
  let k : Subfield M := Subfield.closure A
  haveI : Countable k := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (Subfield.cardinalMk_closure_le_max A).trans (max_le ?_ le_rfl)
    exact Cardinal.mk_le_aleph0_iff.2 hA.to_subtype
  obtain ⟨τ, hτ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq (K := k)
    ((M.val : M →+* ℂ).comp k.subtype) ((ρ : M →+* ℂ).comp k.subtype)
  refine ⟨(τ.toRingHom.toRatAlgHom).comp (⊤ : IntermediateField ℚ ℂ).val, fun x hx hxM => ?_⟩
  have h := hτ ⟨⟨x, hxM⟩, Subfield.subset_closure hx⟩
  have h1 : liftM ⊤ x = ⟨x, IntermediateField.mem_top⟩ := dif_pos IntermediateField.mem_top
  have h2 : liftM M x = ⟨x, hxM⟩ := dif_pos hxM
  unfold cj
  rw [h1, h2]
  exact h

end GlobalTheory.GalTheta
end

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complexEndomorphism_eq_on_countable : ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (S : Set ℂ), S.Countable → ∃ σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ, ∀ x ∈ S, x ∈ M → cj ⊤ σ x = cj M ρ x := by
  atlas_forward_decl GlobalTheory.GalTheta.exists_top_embedding_eq_on_countable
