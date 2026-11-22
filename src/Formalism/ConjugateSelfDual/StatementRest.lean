module

public import Mathlib
public import Formalism.ConjugateSelfDual.Statement

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Polynomial Filter
open scoped ModularForm MatrixGroups

namespace Formalism.ConjugateSelfDual

section places
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

end places

section galois

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {n l : ℕ} [Fact l.Prime]

def UnramAt {R : Type*} [CommRing R] (ρ : G F Ω →* GL (Fin n) R) (v : HeightOneSpectrum (𝓞 F)) :
    Prop :=
  ∀ A, IsPlaceOver A v → ∀ σ ∈ Inertia A, ρ σ = 1

end galois

section polar

variable {n l : ℕ} [Fact l.Prime]

end polar

end Formalism.ConjugateSelfDual
