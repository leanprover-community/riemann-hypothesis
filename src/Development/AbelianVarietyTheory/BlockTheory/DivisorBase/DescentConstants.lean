module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
public import Formalism.SharpRestriction.ElevenLe
public import Formalism.LocalRingCardinality.DataParamsT

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants

open Formalism.BasicNotions Formalism.MainNotions Finset

section Numbers

variable (D : D7) (L : SizeData₂ D)

def pp (j : ℕ) : ℕ := (D.R.sigW j).1

def qq (j : ℕ) : ℕ := (D.R.sigW j).2

end Numbers

section Run

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (Q : ParamsT D L P)

end Run

end GlobalTheory.IndefiniteRowSideFullHecke.DescentConstants

end
