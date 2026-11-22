module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CupPair

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.PD

section Pull

variable {k : Type} [Field k] {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {E : Type} [AddCommGroup E] [Module k E]

end Pull

section Cross

variable {k : Type} [Field k] {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
  {E E' : Type} [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E']

def Disjoint₂ {E'' : Type} [AddCommGroup E''] [Module k E''] (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E)
    (B : Finset κ → Submodule k E') : Prop :=
  ∀ I J, Function.Injective (TensorProduct.lift (μ.compl₁₂ (A I).subtype (B J).subtype))

end Cross

end GlobalTheory.PD
