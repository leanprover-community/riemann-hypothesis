module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

@[expose] public section

open Matrix MeasureTheory Finset Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Mom

abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

attribute [instance] HRep.nG HRep.iP

variable {k r : ℕ}

namespace Ex

open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Ex

end GlobalTheory.Mom
