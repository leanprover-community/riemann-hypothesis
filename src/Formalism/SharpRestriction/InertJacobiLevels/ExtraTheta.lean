module

public import Formalism.LocalRingCardinality.DataTheta
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.BasicNotions.Examples₂ NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ext

variable {E : Type} [Field E] [NumberField E] [StarRing E]

end Ext

end Formalism.MainNotions.Inhab

end
