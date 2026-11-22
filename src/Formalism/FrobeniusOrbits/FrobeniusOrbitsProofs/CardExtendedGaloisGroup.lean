module

public import Mathlib
public import Formalism.FrobeniusOrbits.Statement
public import Formalism.FrobeniusOrbits.DiscrMaximalRealCyclotomic
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.FrobMulInertia
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CoprimeTwoPow

@[expose] public section

open NumberField IntermediateField Ideal

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

namespace Misc2

end Misc2

open Misc2

namespace Misc2

def conjHom {G : Type*} [Group G] (χ : G →* ℂˣ) : G →* ℂ :=
  (starRingEnd ℂ).toMonoidHom.comp ((Units.coeHom ℂ).comp χ)

end Misc2

end Formalism.FrobeniusOrbits
