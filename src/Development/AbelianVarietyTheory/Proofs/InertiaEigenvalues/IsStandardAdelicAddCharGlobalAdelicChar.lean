import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne

section
open NumberField Matrix GlobalTheory.CuspRep

namespace GlobalTheory.StdCharStd

theorem stdPsi_adelicChar : ∀ (E : Type) [Field E] [NumberField E],
    GlobalTheory.CuspGeneric.StdPsi (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) :=
  fun E _ _ => GlobalTheory.StdCharConductor.stdPsi_psi E

end GlobalTheory.StdCharStd
end

open NumberField Matrix GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStandardAdelicAddChar_global_adelicChar : ∀ (E : Type) [Field E] [NumberField E], GlobalTheory.CuspGeneric.StdPsi (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) := by
  atlas_forward_decl GlobalTheory.StdCharStd.stdPsi_adelicChar
