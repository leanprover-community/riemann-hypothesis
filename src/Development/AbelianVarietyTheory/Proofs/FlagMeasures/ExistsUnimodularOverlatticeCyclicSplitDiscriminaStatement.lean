module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnimodularOverlatticeCyclicSplitDiscrimina
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass

@[expose] public section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unimodular_overlattice_cyclic_split_discriminant : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (𝔓 : Ideal (𝓞 K)), 𝔓 ≠ ⊥ → IsCoprime 𝔓 (conjIdeal (K := K) 𝔓) → (∀ L : Submodule (𝓞 K) V, IsIntLat h L → Nonempty ((↥(dual h L) ⧸ L.comap (dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ 𝔓 * conjIdeal (K := K) 𝔓)) → ∃! M : Submodule (𝓞 K) V, Submodule.IsFullLattice K M ∧ IsUnimodular h M ∧ L ≤ M ∧ Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ 𝔓))) ∧ ∀ M L : Submodule (𝓞 K) V, Submodule.IsFullLattice K M → IsUnimodular h M → L ≤ M → Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ 𝔓)) → IsIntLat h L ∧ Nonempty ((↥(dual h L) ⧸ L.comap (dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ 𝔓 * conjIdeal (K := K) 𝔓)) := by
  first
  | exact @GlobalTheory.Mass.SplitOver.main
  | intro K V _ _ _ _ _ _ _ _ h hc hs hn P hp hcop
    obtain ⟨forward, backward⟩ := GlobalTheory.Mass.SplitOver.main K V h hc hs hn P hp hcop
    constructor
    · intro L hL he
      obtain ⟨M, ⟨hM, hu, hl, heM⟩, unique⟩ := forward L hL he
      exact ⟨M, ⟨full_of_unimodular h hs hM hu, hu, hl, heM⟩,
        fun N hN => unique N ⟨hN.1.toIsLattice, hN.2⟩⟩
    · intro M L hM hu hl he
      exact backward M L hM.toIsLattice hu hl he
