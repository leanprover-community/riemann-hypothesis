module

public import Mathlib

@[expose] public section

namespace GroundTheory.LocalField

section Completion

variable (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

def openFiniteIndex : Set (Subgroup G) :=
  {H | IsOpen (H : Set G) ∧ H.FiniteIndex}

namespace openCompletion

variable {G}

theorem discreteTopology_quotient (H : openFiniteIndex G) : DiscreteTopology (G ⧸ (H : Subgroup G)) :=
  QuotientGroup.discreteTopology H.2.1

end openCompletion

end Completion

end GroundTheory.LocalField
