import Formalism.DirichletDensity.DirichletDensityProofs.QuadDiscr
import Formalism.DirichletDensity.DirichletDensityProofs.MQDiscr
import Formalism.DirichletDensity.DirichletDensityProofs.APLogDensity
import Formalism.DirichletDensity.DirichletDensityProofs.LogToDir
import Formalism.DirichletDensity.DirichletDensityProofs.HostDensityArith
import Formalism.DirichletDensity.DirichletDensityProofs.HostDensity

namespace Formalism.HF.Final

theorem quadDiscr : Formalism.HF.QuadDiscr := Formalism.HF.quadDiscr
theorem mqDiscr : Formalism.HF.MQDiscr := Formalism.HF.mqDiscr_of quadDiscr
theorem apLogDensity : Formalism.HF.APLogDensity := Formalism.HF.apLogDensity

end Formalism.HF.Final
