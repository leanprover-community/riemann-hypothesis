import Mathlib
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.SubfieldClosureEqTopOfEpi
import BuildAid.ForwardExisting

section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ggeo

theorem epi_subfield_closure_range_eq_top : ∀ (O F : Type) [CommRing O] [Field F] (β : O →+* F),
    (∀ (T : Type) [CommRing T] (g₁ g₂ : F →+* T), g₁.comp β = g₂.comp β → g₁ = g₂) →
    Subfield.closure (Set.range β) = ⊤ :=
  PositivityTheory.UnitarySelfGeneration.subfield_closure_eq_top_of_epi

end GlobalTheory.CompanionTheory.Ggeo
end

open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.epi_ring_hom_field_closure : ∀ (O F : Type) [CommRing O] [Field F] (β : O →+* F), (∀ (T : Type) [CommRing T] (g₁ g₂ : F →+* T), g₁.comp β = g₂.comp β → g₁ = g₂) → Subfield.closure (Set.range β) = ⊤ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ggeo.epi_subfield_closure_range_eq_top
