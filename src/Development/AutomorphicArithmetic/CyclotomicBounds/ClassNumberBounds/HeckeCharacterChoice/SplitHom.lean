import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.HeckeCharacterChoice.SplitDef

open NumberField

namespace KStar.Choice

variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] {p : ℕ}

def homsOver (E : Type*) [Field E] [Algebra K E] (ψ : 𝓞 K →+* ZMod p) :
    Set (𝓞 E →+* ZMod p) :=
  {φ | φ.comp (algebraMap (𝓞 K) (𝓞 E)) = ψ}

def conjHom (φ : 𝓞 E →+* ZMod p) (σ : E ≃ₐ[K] E) : 𝓞 E →+* ZMod p :=
  φ.comp (RingOfIntegers.mapRingHom (σ : E →+* E))


end KStar.Choice
