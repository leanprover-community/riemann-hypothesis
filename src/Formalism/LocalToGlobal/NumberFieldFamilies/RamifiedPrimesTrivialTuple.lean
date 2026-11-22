module

public import Formalism.LocalToGlobal.UnitaryNorms.CharDiv
public import Mathlib
public import Formalism.LocalToGlobal.UnitaryNorms.UnrAe

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Fam.DivCQ

open Formalism.BasicNotions Formalism.L2.Host

variable {D : D7} {C : CharFrame D} {nch : NChoice D}

theorem unrAt_one {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) : (1 : HChar L).UnrAt w :=
  fun _ _ => rfl

attribute [instance] ConjAt.instM ConjAt.instMi ConjAt.instMf ConjAt.instT ConjAt.instTi ConjAt.instTf

end Formalism.L2.Fam.DivCQ

end
