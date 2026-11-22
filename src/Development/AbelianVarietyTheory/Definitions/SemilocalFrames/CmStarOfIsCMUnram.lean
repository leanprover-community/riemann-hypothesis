module

public import Mathlib
public import Formalism.LocalRingCardinality.DataSpaces
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces

@[expose] public section

noncomputable section

namespace GlobalTheory.SA

open NumberField Module Formalism.BasicNotions

def CMStar (E : Type) [Field E] [StarRing E] : Prop :=
  ∀ (τ : E →+* ℂ) (x : E), τ (star x) = starRingEnd ℂ (τ x)

section AnySpace

variable {E : Type} [Field E] [NumberField E] [StarRing E]
  {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

end AnySpace

variable {E : Type} [Field E] [NumberField E] [StarRing E]

structure Amb (S : HSpace E) (k r : ℕ) : Prop where
  cm : CMStar E
  dim : finrank E S.V = k + 2 * r + 1
  neg : ∀ (τ : E →+* ℂ) (U : Submodule E S.V), (∀ x ∈ U, (τ (S.hT x x)).re ≤ 0) → finrank E U ≤ r + 1

section Diagonal

open Formalism.BasicNotions.Examples₂

end Diagonal

end GlobalTheory.SA

end
