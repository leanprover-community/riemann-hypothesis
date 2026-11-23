module

public import Development.EtaleCohomology.CohomologicalPurity.LeafHensCutDef
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.CohomologicalPurity.Hz

theorem LeafColUniv_of : LeafColUniv := by
  intro A _ I Δ c hc η hη B _ J hJ ψ hψ
  have hu : ∀ j, ∃! χ : Δ.D.obj j →+* B, χ.comp (Δ.s j) = ψ := fun j => (Δ.good j).univ B J hJ ψ hψ
  choose χ hχ hχu using hu
  have hnat : ∀ {j k : Δ.J} (e : j ⟶ k), (χ k).comp (Δ.D.map e).hom = χ j := fun {j k} e => by
    apply hχu j
    rw [RingHom.comp_assoc, Δ.nat e, hχ k]
  let cB : Cocone Δ.D := ⟨CommRingCat.of B,
    ⟨fun j => CommRingCat.ofHom (χ j), fun _ _ e => CommRingCat.hom_ext (hnat e)⟩⟩
  let d := hc.desc cB
  have hfac : ∀ j, d.hom.comp (Δ.leg c j) = χ j := fun j =>
    congrArg CommRingCat.Hom.hom (hc.fac cB j)
  obtain ⟨j₀⟩ : Nonempty Δ.J := IsFiltered.nonempty
  refine ⟨d.hom, ?_, fun χ' h' => ?_⟩
  · show d.hom.comp η = ψ
    rw [← hη j₀, ← RingHom.comp_assoc, hfac, hχ]
  · have hd : CommRingCat.ofHom χ' = d := hc.hom_ext fun j => by
      apply CommRingCat.hom_ext
      change χ'.comp (Δ.leg c j) = d.hom.comp (Δ.leg c j)
      rw [hfac]
      apply hχu j
      rw [RingHom.comp_assoc, hη j, h']
    exact congrArg CommRingCat.Hom.hom hd

end LateralTheory.CohomologicalPurity.Hz
