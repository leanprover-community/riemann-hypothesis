module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig

@[expose] public section

noncomputable section

namespace PI.AmpRootCommon

open Formalism.MainNotions.S

def pv : List (ℂ × ℕ) → ℕ → ℕ
  | [], i => i
  | (_, s) :: bs, i => if i < s then s - 1 - i else s + pv bs (i - s)

end PI.AmpRootCommon
