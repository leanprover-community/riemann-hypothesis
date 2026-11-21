import Formalism.SizeWindowBrackets.RealSlopeBoundsSplit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.BigOperators

namespace Formalism.LFunctionChainParameters.WeightedMeanLemmas

open Finset

section Means

variable {ι : Type*} [Fintype ι]





end Means



example : ∃ (d muMaxN muN muMaxM muM h dr BE : Bool → ℝ) (Sg0 A A' V : ℝ),
    (∀ u, 0 < d u) ∧ (∀ u, 0 ≤ dr u) ∧ Slopes2ge muMaxN muN muMaxM muM dr BE Sg0 ∧
    (∀ u, muMaxM u ≤ A) ∧ (∀ u, -A' ≤ muM u) ∧ (∀ u u', |h u - h u'| ≤ V) ∧ (∃ u, h u ≠ h (!u)) :=
  ⟨fun u => if u then 1 else 2, fun _ => 0, fun _ => -1, fun _ => 0, fun _ => 0,
    fun u => if u then 1 else 0, fun _ => 0, fun _ => 1, 0, 0, 0, 1,
    fun u => by cases u <;> norm_num, fun _ => le_rfl,
    ⟨fun _ => by norm_num, fun _ => by norm_num⟩, fun _ => le_rfl, fun _ => by norm_num,
    fun u u' => by cases u <;> cases u' <;> norm_num, ⟨true, by norm_num⟩⟩

end Formalism.LFunctionChainParameters.WeightedMeanLemmas
