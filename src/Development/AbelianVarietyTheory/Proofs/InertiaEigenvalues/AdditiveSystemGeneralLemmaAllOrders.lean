import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemSurjectivityAndCountOrderZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemGeneralLemmaOrderOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemIntegralSurjectivityOfOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemIntegralSolutionCountOfOrderOne

section
open GlobalTheory.PMonE

namespace GlobalTheory

theorem PMonE.generalLemma_allOrders : ∀ N : ℕ, GLOnto N ∧ GLCount N := by
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact GlobalTheory.T.additiveSystem_surjectivity_and_count_order_zero
  · exact ⟨GlobalTheory.T.additiveSystemIntegralSurjectivity_of_one N hN GlobalTheory.T.additiveSystem_generalLemma_orderOne.1, GlobalTheory.T.additiveSystemIntegralSolutionCount_of_order_one N hN GlobalTheory.T.additiveSystem_generalLemma_orderOne.2⟩

end GlobalTheory
end

open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additiveSystem_generalLemma_all_orders : ∀ N : ℕ, GLOnto N ∧ GLCount N := by
  atlas_forward_decl GlobalTheory.PMonE.generalLemma_allOrders
