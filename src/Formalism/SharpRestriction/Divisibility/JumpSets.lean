module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.JumpSetsAlt

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.UG TensorProduct Finset NumberField IsDedekindDomain

attribute [instance] Prov.instO Prov.domO Prov.dvrO Prov.czO Prov.algZ Prov.topO Prov.instGf Prov.instHk Prov.algHk
  Prov.modHk Prov.towHk

variable {D : D7}

def excSet (D : D7) : Finset ℕ := D.host.small ∪ {D.host.q, D.host.d, D.host.pde, D.host.pde'}

def ramSet (D : D7) : Finset ℕ := D.host.small ∪ {D.host.q, D.host.d}

end Formalism.MainNotions.JumpSetsAlt

end
