module

public import Mathlib

@[expose] public section

namespace ReciprocityTheory.Def

open IsLocalRing Matrix

universe u v w w'

attribute [instance] IsCNL.noeth IsCNL.complete IsCNL.localHom

namespace Pattern

variable {n : ℕ}

end Pattern

section Lift

variable (O : Type u) [CommRing O] [IsLocalRing O]
variable {G : Type v} [Group G] [TopologicalSpace G] {n : ℕ}

end Lift

end ReciprocityTheory.Def
