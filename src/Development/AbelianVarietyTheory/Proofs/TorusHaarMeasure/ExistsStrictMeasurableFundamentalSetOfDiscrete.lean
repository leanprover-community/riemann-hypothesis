module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.LegendreSymbol
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSubgroupCountableAndExistsStrictFundamen

@[expose] public section

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory


open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
theorem _root_.GlobalTheory.exists_strict_measurable_fundamental_set_of_discrete :
    (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G), (∃ U ∈ 𝓝 (1 : G), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → Countable Γ ∧ ∃ F : Set G, MeasurableSet F ∧ ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ F) := by
  intro G _ _ _ _ _ _ _ _ Γ ⟨U, hU, hΓU⟩
  obtain ⟨t, htU, ht, h1t⟩ := mem_nhds_iff.1 hU
  have hopen : IsOpen ({1} : Set Γ) := by
    rw [isOpen_induced_iff]
    refine ⟨t, ht, ?_⟩
    ext x
    exact ⟨fun hx => Subtype.ext (hΓU _ x.2 (htU hx)), fun hx => hx ▸ h1t⟩
  have : DiscreteTopology Γ := discreteTopology_of_isOpen_singleton_one hopen
  exact discreteSubgroup_countable_and_exists_strict_fundamentalDomain Γ

end GlobalTheory
