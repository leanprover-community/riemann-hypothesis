module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermRegularDimGe
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionSheetsDense
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolomorphicFibreInfinite

@[expose] public section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem IrreducibleGermRegularDimGe.proof (hS : FiniteProjectionSheetsDense.Statement) :
    IrreducibleGermRegularDimGe.Statement := by
  intro σ _ X w d A hX hirr hiso hnd
  obtain ⟨N, hN, hsub⟩ := hS σ X w d A hX hirr hiso hnd
  refine ⟨N, hN, ?_⟩
  intro x hx e A' O V g hO hV hxV hg hleft hXV
  by_contra hlt
  obtain ⟨y, hyV, hyX, O₁, V₁, g₁, hO₁, hV₁, hyV₁, hg₁, hleft₁, hXV₁⟩ :=
    mem_closure_iff.1 (hsub hx) V hV hxV
  obtain ⟨t₀, ht₀, rfl⟩ : y ∈ g₁ '' O₁ := hXV₁ ▸ ⟨hyX, hyV₁⟩
  let U : Set (Fin d → ℂ) := O₁ ∩ g₁ ⁻¹' V
  obtain ⟨z, hz⟩ := HolomorphicFibreInfinite.proof d e U (fun t => A' (g₁ t)) (lt_of_not_ge hlt)
    (hg₁.continuousOn.isOpen_inter_preimage hO₁ hV) ⟨t₀, ht₀, hyV⟩
    (A'.differentiable.comp_differentiableOn (hg₁.differentiableOn.mono Set.inter_subset_left))
  refine hz (Set.Subsingleton.finite ?_)
  have fibre_image (t : Fin d → ℂ) (ht : t ∈ U) (htz : A' (g₁ t) = z) : g₁ t = g z := by
    obtain ⟨u, hu, hgu⟩ : g₁ t ∈ g '' O := hXV ▸
      ⟨(show g₁ t ∈ X ∩ V₁ from hXV₁ ▸ Set.mem_image_of_mem g₁ ht.1).1, ht.2⟩
    simpa only [← hgu, hleft u hu] using congrArg g htz
  intro t₁ ht₁ t₂ ht₂
  rw [← hleft₁ t₁ ht₁.1.1, ← hleft₁ t₂ ht₂.1.1,
    fibre_image t₁ ht₁.1 ht₁.2, fibre_image t₂ ht₂.1 ht₂.2]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
