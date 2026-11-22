module

public import Mathlib
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.CyclotomicNorms.StatementI
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FewBadPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab NumberField GlobalTheory.EX

variable {R : Ranks}

def condE (H : Host R) : ℕ := H.QS * H.q * H.d

end GlobalTheory.IndefiniteRowSideFullHecke.FewBadPrimes

end
