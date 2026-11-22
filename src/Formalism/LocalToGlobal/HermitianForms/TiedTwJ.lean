module

public import Formalism.LocalToGlobal.HermitianForms.TiedTw

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}

end Formalism.L2.Forms

end
