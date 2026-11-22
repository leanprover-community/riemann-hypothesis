module

public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace Formalism.IndefR.NX.Core

attribute [instance] RatCore.fieldBase RatCore.numberFieldBase RatCore.fKs RatCore.nfKs RatCore.algKs RatCore.crO RatCore.domO
  RatCore.grpG RatCore.finG RatCore.acgWL RatCore.modWL RatCore.modKsWL RatCore.towWL RatCore.modOLWL
  RatCore.towOLWL RatCore.modOKsWL RatCore.towOKsWL RatCore.nW RatCore.ipW

variable (C : RatCore)

end Formalism.IndefR.NX.Core
