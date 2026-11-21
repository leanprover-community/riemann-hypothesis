import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowLStar
import BuildAid.ForwardExisting

section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_sizeLstar : SzRow (fun _ _ L => SizeLstar L) := szRow_lStar

end GlobalTheory.EX
end

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.explicitChoice_sizeLstar : SzRow (fun _ _ L => SizeLstar L) := by
  atlas_forward_decl GlobalTheory.EX.szRow_sizeLstar
