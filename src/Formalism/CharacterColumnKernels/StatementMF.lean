module

public import Formalism.CharacterColumnKernels.Statement
public import Formalism.CharacterColumnKernels.StatementX

@[expose] public section

open Finset

noncomputable section

namespace Formalism.NG

universe u

section EpsDual
variable (O OO Q : Type*) [CommRing O] [Ring OO] [Algebra O OO] [AddCommGroup Q] [Module O Q]
  (ε : OO)

end EpsDual

def StatMatlis : Prop :=
  ∀ (O N : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup N]
    [Module O N], IsFiniteLength O N →
    Module.length O (N →ₗ[O] KO O) = Module.length O N

end Formalism.NG
