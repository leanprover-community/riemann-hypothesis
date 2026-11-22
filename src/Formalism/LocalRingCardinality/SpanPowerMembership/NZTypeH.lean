module

public import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeE
public import Mathlib
public import Formalism.CyclotomicNorms.StatementT
public import Formalism.CyclotomicNorms.NonsquarefreeBounds.IrreducibilityOfRestriction
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleNewtypesIdempotentZero

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

attribute [local instance] neZero_g fact_g Classical.propDecidable

variable {R : Ranks} (H : Host R)

variable {H} (Lb : Lbl H)

variable (H) (what₂ : Rows.Data R) (h : NHyp H what₂)

section Field

variable (K : Type) [Field K] [CharZero K]

end Field

end Formalism.BasicNotions.Examples₂.NZ
