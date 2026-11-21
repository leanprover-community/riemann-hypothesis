import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedTorsionClassTheoremGoodCase
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiesAndInputsOfDualityEuler
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalAllOfTateDualityEulerChar

section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.TheoremTBRecords

theorem aux_of_blochKato_tateDuality_eulerChar :
    GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
      ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
        LocalSituation.Conclusion4 D HW F := by
  intro hBK hTD hEC D HW F _Cm
  obtain ⟨_J, hA⟩ := GlobalTheory.LocInputs.ties_and_inputs_of_duality_euler hTD hEC D HW F
  exact GlobalTheory.T.twistedTorsionClassTheorem_goodCase D HW F hA (GlobalTheory.T.blochKatoLocal_all_of_tateDuality_eulerChar hBK hTD hEC D)

end GlobalTheory.TheoremTBRecords
end

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theorem_tb_of_local_blochKato_duality_euler : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), LocalSituation.Conclusion4 D HW F := by
  atlas_forward_decl GlobalTheory.TheoremTBRecords.aux_of_blochKato_tateDuality_eulerChar
