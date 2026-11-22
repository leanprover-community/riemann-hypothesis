module

public import Mathlib
public import Formalism.SatakeDualWeyl.Statement

@[expose] public section

noncomputable section

open Polynomial TensorProduct Matrix NumberField IsDedekindDomain Formalism.UG

namespace GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion

variable {F E : Type} [Field F] [Field E] [Algebra F E]

variable {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}

variable (k : Type) [Field k] [Algebra F k]

attribute [local instance] algLk

variable {k}

variable (k)

end GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
