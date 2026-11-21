import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.LocalToGlobal.HermitianForms.BothSym
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RankConditionsOfLayerTwo
import BuildAid.ForwardExisting

section
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem mu0Tie_of_colsTiedSym : ∀ (D : D7), Formalism.L2.Forms.ColsTiedSym D → ∀ u : D.what₂.Word, StandardLattice.Mu0Tie D u :=
  fun _ C u => Formalism.MainNotions.Ext.Lw.mu0Tie_of_sym C u

end GlobalTheory
end

open Formalism.BasicNotions Formalism.MainNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankCondition_of_columns_equal_symmetricLevel : ∀ (D : D7), Formalism.L2.Forms.ColsTiedSym D → ∀ u : D.what₂.Word, StandardLattice.Mu0Tie D u := by
  atlas_forward_decl GlobalTheory.mu0Tie_of_colsTiedSym
