module

public import Mathlib
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsUnitaryOfOrder

@[expose] public section

noncomputable section
section

open NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Chr

open Formalism.BasicNotions Formalism.FrobeniusOrbits

def embTau (D : D7) (τ : D.what₂.Tau) : D.host.E →+* ℂ := D.host.emb ((D.eTau τ : D.R.Psi) : D.R.GG)

end GlobalTheory.Mem.Chr

end
