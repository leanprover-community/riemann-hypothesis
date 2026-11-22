module

public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCF
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] (V : HSpace E) (δ : E) (hδ : star δ = -δ) (hδ0 : δ ≠ 0)

end Gen

variable {D : D7}

end Formalism.L2.Fam.ThC

end
