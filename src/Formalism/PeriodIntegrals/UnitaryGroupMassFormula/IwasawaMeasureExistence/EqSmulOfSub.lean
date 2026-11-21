import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.TBlkEqTFMulProdTV

noncomputable section

namespace PI.IwaMeasEx.LP

open MeasureTheory MeasureTheory.Measure Topology Set NumberField
open scoped ENNReal NNReal
open Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.L2.S.S7.WittLeviSubgroups PI.IwaMeasEx.AfT

section Uniq

variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem exists_coef (H : Subgroup G) (hc : IsClosed (H : Set G)) {μ : Measure G} (hs : μ (H : Set G)ᶜ = 0)
    (hcpt : ∀ s : Set G, IsCompact s → μ s ≠ ⊤) (hi : ∀ h ∈ H, μ.map (fun x => h * x) = μ) :
    haveI : LocallyCompactSpace H := hc.locallyCompactSpace
    ∃ a : ℝ≥0, μ = a • (Measure.haar : Measure H).map Subtype.val := by
  haveI : LocallyCompactSpace H := hc.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  have hme : MeasurableEmbedding (Subtype.val : H → G) := hc.isClosedEmbedding_subtypeVal.measurableEmbedding
  have hmap : (μ.comap (Subtype.val : H → G)).map Subtype.val = μ := by
    rw [hme.map_comap, Subtype.range_coe]
    exact restrict_eq_self_of_ae_mem ((ae_iff).2 hs)
  haveI : IsMulLeftInvariant (μ.comap (Subtype.val : H → G)) := ⟨fun h => by
    have e1 := map_val_mul' H h (μ.comap (Subtype.val : H → G))
    rw [hmap, hi (h : G) h.2] at e1
    calc (μ.comap (Subtype.val : H → G)).map (fun x => h * x)
        = (((μ.comap (Subtype.val : H → G)).map (fun x => h * x)).map Subtype.val).comap Subtype.val :=
          (hme.comap_map _).symm
      _ = μ.comap Subtype.val := by rw [e1]⟩
  haveI : IsFiniteMeasureOnCompacts (μ.comap (Subtype.val : H → G)) := ⟨fun K hK => by
    rw [hme.comap_apply]
    exact (hcpt _ (hK.image continuous_subtype_val)).lt_top⟩
  refine ⟨haarScalarFactor (μ.comap (Subtype.val : H → G)) Measure.haar, ?_⟩
  conv_lhs => rw [← hmap, isMulLeftInvariant_eq_smul (μ.comap (Subtype.val : H → G)) Measure.haar]
  rw [Measure.map_smul]


end Uniq



section Prod

variable {I : AutInst} {J : ℕ} (Fr : WittFrame I J) (c : Composition J)


end Prod

end PI.IwaMeasEx.LP

end
