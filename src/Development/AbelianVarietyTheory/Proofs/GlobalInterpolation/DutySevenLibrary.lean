import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.DesignExistsOfChoices
import Formalism.SharpRestriction.SmoothDesignExistence.DesignExistsDes
import Formalism.SharpRestriction.PageFix
import Formalism.SharpRestriction.Divisibility.SmallFirstModulusBelowScale
import Formalism.SharpRestriction.GlobalSchurBounds.WeightVectorSmallSharesEight
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PageDutiesOfClassSeven

section
noncomputable section

namespace GlobalTheory.EX.DQ

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

theorem weightAdmissible_smallShares_at_point {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (h : AuxBlock8.admW D L X K) :
    ChW_at X K := by
  have h3 := h.2.2
  unfold AuxBlock8.WReq at h3
  unfold ChW_at
  refine le_of_eq_of_le (Finset.sum_congr rfl fun p _ => ?_) h3
  split_ifs <;> ring

end GlobalTheory.EX.DQ

end
end

section
namespace GlobalTheory.EX.DQ

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk GlobalTheory.EX GlobalTheory.Fc

theorem duty_seven_library : ∀ (eps : ℝ) (Fm : FamP eps), DQ.Duty7 Fm → Formalism.MainNotions.PageFix Fm ∧ Formalism.MainNotions.PageWin Fm ∧
    Formalism.MainNotions.DIV.Align.SmallFirstModulusBelowScale Fm ∧ Formalism.MainNotions.TameDistinctF Fm ∧ Formalism.MainNotions.ChosenWall Fm ∧ DQ.TupUsedF Fm ∧ DQ.TwAllF Fm := by
  intro eps Fm h
  obtain ⟨a, b, c, d, e, f, g⟩ := h
  refine ⟨a, b, fun x hx i => (c x hx i).2.2.2.2.1, ?_, ⟨Fm.x1 + 1, fun x hx i => ?_⟩, f, g⟩
  · unfold DC.TameDistinctF at d
    unfold Formalism.MainNotions.TameDistinctF
    simpa only [tameDistinct_iff] using d
  · exact weightAdmissible_smallShares_at_point _ _ (e x (by linarith) i)

end GlobalTheory.EX.DQ
end
