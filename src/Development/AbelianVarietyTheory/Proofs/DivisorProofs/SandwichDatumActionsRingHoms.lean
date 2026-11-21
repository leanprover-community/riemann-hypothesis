import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
import BuildAid.ForwardExisting

section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory.Proof.sandwich_datum_actions_ring_homs

theorem actions_ringHom : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (h : ℕ) (D : Datum ε h Λ), (∃ ρ : Λ →+* Matrix (Fin h) (Fin h) O, ⇑ρ = actT D) ∧ (∃ ρ : Λ →+* Matrix (Fin h) (Fin h) O, ⇑ρ = actH D) := by
  intro p _ O _ _ _ ε Λ _ _ h D
  exact ⟨⟨(RingHom.mapMatrix (padicToO p O)).comp (D.ρT : Λ →+* Matrix (Fin h) (Fin h) ℤ_[p]), rfl⟩,
    ⟨(RingHom.mapMatrix (WittVector.fontaineTheta O p)).comp D.ρM, rfl⟩⟩

end GlobalTheory.Proof.sandwich_datum_actions_ring_homs
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sandwich_datum_actions_ring_homs : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (ε : PreTilt O p) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (h : ℕ) (D : Datum ε h Λ), (∃ ρ : Λ →+* Matrix (Fin h) (Fin h) O, ⇑ρ = actT D) ∧ (∃ ρ : Λ →+* Matrix (Fin h) (Fin h) O, ⇑ρ = actH D) := by
  atlas_forward_decl GlobalTheory.Proof.sandwich_datum_actions_ring_homs.actions_ringHom
