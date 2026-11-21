import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.WeylSplitting.WeylSplit

section
open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2

namespace GlobalTheory.CompanionTheory.CharInf

theorem chWMap : ChWMap := by
  intro E _ _ n lam P
  rfl

end GlobalTheory.CompanionTheory.CharInf
end

open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_weight_map : ChWMap := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CharInf.chWMap
