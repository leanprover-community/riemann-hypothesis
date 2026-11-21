import Formalism.SobolevGaussianKernels.GaussianKernelBounds.EichlerEquivalenceHolds
import Mathlib
import Formalism.SobolevGaussianKernels.StatementCS
import Formalism.SobolevGaussianKernels.GaussianKernelBounds.LfProd
import Formalism.SobolevGaussianKernels.GaussianKernelBounds.NeighbourhoodHilbertSchmidtHolds
import Formalism.SobolevGaussianKernels.StatementMV
import Formalism.SobolevGaussianKernels.GaussianKernelBounds.HasDerivAtSphereChartLast
import Formalism.SobolevGaussianKernels.StatementNC

namespace Formalism.SL.Final

theorem primesOver : Formalism.SL.LF.PrimesOver := Formalism.SL.P.primes_over_holds
theorem frameGram : Formalism.SL.FU.FrameGram := Formalism.SL.P.frame_gram_holds

end Formalism.SL.Final
