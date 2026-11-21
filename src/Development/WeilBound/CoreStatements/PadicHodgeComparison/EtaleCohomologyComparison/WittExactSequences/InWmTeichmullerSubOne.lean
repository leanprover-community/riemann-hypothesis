import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.DesAcrZero
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ForD

set_option backward.isDefEq.respectTransparency false

open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.D

variable (l : ℕ) [Fact l.Prime]

theorem out : Out l := out_of_rin l (CrystallineSemistableComparison.R.forD l)



theorem inWm_iff [IsLocalRing (Ob l)] (s : Ainf l) : InWm l s ↔ WittVector.map (IsLocalRing.residue (Ob l)) s = 0 := by
  rw [WittVector.ext_iff]
  refine forall_congr' fun i => ?_
  rw [WittVector.map_coeff, WittVector.zero_coeff, IsLocalRing.residue_eq_zero_iff]
  rfl

theorem isLocalRing_Ob (h : ObFacts l) : IsLocalRing (Ob l) := by
  obtain ⟨_, _, _⟩ := h
  infer_instance


theorem InWm.mul_left (h : ObFacts l) (a : Ainf l) {s : Ainf l} (hs : InWm l s) : InWm l (a * s) := by
  have := isLocalRing_Ob l h
  rw [inWm_iff] at hs ⊢
  rw [map_mul, hs, mul_zero]

end CrystallineSemistableComparison.D
