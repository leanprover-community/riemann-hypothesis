import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassC0PrimeExceedsSplitBound
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BernEqProd

section
namespace GlobalTheory.EX

theorem exists_tops : TopsChoice := TopsOfHost.topsChoice_of GlobalTheory.topsChoice

end GlobalTheory.EX
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tops_choice : TopsChoice := by
  atlas_forward_decl GlobalTheory.EX.exists_tops
