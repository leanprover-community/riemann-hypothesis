import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjMemFixedPiN
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetProjectionSurjectiveHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterExistsUnique

section
open GlobalTheory.PRep PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.Cass

theorem sphericalProduct_A4 : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], PositivityTheory.SphericalProduct.A4 G := by
  intro G _ _ _
  unfold PositivityTheory.SphericalProduct.A4
  intro D V _ _ π hπ hex
  obtain ⟨t, ht⟩ := hex
  refine ⟨fun v => GlobalTheory.CompanionTheory.Cass.proj_mem_fixed_piN G D V π v, ?_⟩
  have hsm : GlobalTheory.PRep.IsSmooth π := by
    unfold GlobalTheory.PRep.IsAdmissible at hπ
    exact hπ.1
  have hH := GlobalTheory.T.hecke_character_exists_unique
  unfold PositivityTheory.Lbc.HeckeExistsUnique at hH
  obtain ⟨U, hU, -⟩ := hH G D.J D.isOpen_J D.isCompact_J V π hsm (t : G)
  exact GlobalTheory.T.jacquet_projection_surjective_holds G D V π hπ t ht U hU

end GlobalTheory.CompanionTheory.Cass
end

open GlobalTheory.PRep PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_lemma_holds : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], PositivityTheory.SphericalProduct.A4 G := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Cass.sphericalProduct_A4
