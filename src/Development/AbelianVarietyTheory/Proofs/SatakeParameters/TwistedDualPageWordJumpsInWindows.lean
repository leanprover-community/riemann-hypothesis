import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordBox
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualJumpsMemWindows
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpsMemBoxNegMH

section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_T1_and_J1_mem_window_of_roomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → (pageWord L j ε τ φ).T1 ∧ ∀ i, ∀ u ∈ (pageWord L j ε τ φ).J1 i, -((pageWord L j ε τ φ).Mi i : ℤ) ≤ u ∧ u ≤ (pageWord L j ε τ φ).hi i := by
  intro D L C j ε τ φ hR
  have hT : (pageWord L j ε τ φ).T1 := by
    intro i u hu
    exact GlobalTheory.T.twistedDualJumps_mem_windows (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i)) L.Sc L.etaSz
      (fun a => L.cloud_v _ a) (fun a => L.be_close _ a j) u hu
  refine ⟨hT, GlobalTheory.T.jumps_mem_box_neg_M_h _ (fun i => ?_) hT⟩
  have h := (GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε τ φ hR).2.2.2.2.2 i
  exact le_trans (Int.natCast_nonneg _) h.le

end GlobalTheory.HTW
end

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDualPageWord_jumps_in_windows : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → (pageWord L j ε τ φ).T1 ∧ ∀ i, ∀ u ∈ (pageWord L j ε τ φ).J1 i, -((pageWord L j ε τ φ).Mi i : ℤ) ≤ u ∧ u ≤ (pageWord L j ε τ φ).hi i := by
  atlas_forward_decl GlobalTheory.HTW.pageWord_T1_and_J1_mem_window_of_roomy
