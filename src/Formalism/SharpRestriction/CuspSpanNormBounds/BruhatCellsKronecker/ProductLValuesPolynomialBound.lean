import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Bridge

variable {eps : ℝ}

theorem f_le_k (D : D7) : (D.R.f : ℝ) ≤ D.R.k := by
  have h := D.R.f_le_k
  exact_mod_cast h

theorem k_le_r (D : D7) : (D.R.k : ℝ) ≤ D.R.r := by
  have h := D.R.two_le_m
  have h' : D.R.k ≤ D.R.r := by
    unfold Formalism.BasicNotions.Ranks.r
    omega
  exact_mod_cast h'




end Formalism.MainNotions.BridgeLemma

end
