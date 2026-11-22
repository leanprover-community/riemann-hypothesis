module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Upq

@[expose] public section

noncomputable section

namespace HcS.BasicNotions

open NumberField IsDedekindDomain
open scoped TensorProduct

attribute [instance] HSpace.acg HSpace.modE HSpace.modO HSpace.tower HSpace.fd

namespace HSpace

variable {E : Type} [Field E] [NumberField E] [StarRing E]

end HSpace

namespace Spaces

end Spaces

end HcS.BasicNotions

end
