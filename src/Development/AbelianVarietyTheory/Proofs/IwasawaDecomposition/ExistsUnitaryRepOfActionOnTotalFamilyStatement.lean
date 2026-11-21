import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryRepOfActionOnTotalFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY
import BuildAid.ForwardExisting

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryRep_of_action_on_total_family : ∀ (G S H : Type) [Group G] [TopologicalSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (act : G → S → S) (E : S → H), (∀ p, act 1 p = p) → (∀ g h p, act (g * h) p = act g (act h p)) → Dense (Submodule.span ℂ (Set.range E) : Set H) → (∀ g p q, inner ℂ (E (act g p)) (E (act g q)) = inner ℂ (E p) (E q)) → (∀ p q, Continuous fun g => inner ℂ (E q) (E (act g p))) → ∃ π : G →* (H →L[ℂ] H), (∀ g x, ‖π g x‖ = ‖x‖) ∧ (∀ x, Continuous fun g => π g x) ∧ ∀ g p, π g (E p) = E (act g p) := by
  atlas_forward_decl GlobalTheory.TotalFamilyRep.exists_rep
