module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.LocalToGlobal.GlobalTheory.LinkTiesTh

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Jets

open NumberField Formalism.BasicNotions Formalism.MainNotions Classical

section Pieces

variable {R : Ranks} (host : Host R) {LL : Type} [Field LL] [NumberField LL] (embLL : LL →+* ℂ)
  {Tau : Type} [Fintype Tau] (eTau : Tau ≃ R.Psi)

attribute [instance] CurveDat.nf

variable {host embLL eTau}

end Pieces

end Formalism.L2.GlobalTheoryTheory.Jets
