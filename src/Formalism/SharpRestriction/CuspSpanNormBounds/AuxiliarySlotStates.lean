module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

@[expose] public section

open Matrix MeasureTheory
open scoped ContDiff InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.S.TopsChoicePartA

open Formalism.QuantumDeterminants

abbrev Vec (k0 r : ℕ) := Fin (2 * r + (k0 + 1) + 1) → ℂ

attribute [instance] Lev.nWp Lev.iWp Lev.fWp Lev.nWq Lev.iWq Lev.fWq

namespace Lev

end Lev

section OpMat

variable {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]

end OpMat

section Words

variable {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]

end Words

section Vectors

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

end Vectors

namespace Lev

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Lev

section Waves

variable {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]

end Waves

namespace Lev

end Lev

section Prods

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

end Prods

namespace Lev

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Lev

namespace Lev

end Lev

section Deg

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Deg

end Formalism.MainNotions.S.TopsChoicePartA
