import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ThetaIntegerIsSSubstitution
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.CoboundaryCommutesHomomorphism
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.TraceDualExists
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.FrobeniusOnRingA
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.FrobeniusExtensionOnInclusion
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.ExistsUnitFactorizationBounded
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.IntegralPartAtVariable

section
namespace Formalism.L2.Th1.D

theorem thmAEntryOfF : ThmAEntryOfF := theorem_a_entry_of_f
theorem thmAGaussOfF : ThmAGaussOfF := theorem_a_gauss_of_f
theorem oneLetterGaussOfF : OneLetterGaussOfF := one_letter_gauss_of_f
theorem kernelOfF : KernelOfF := kernel_of_f
theorem sigmaIsom : SigmaIsom := sigma_isometry
theorem fixedIsLimit : FixedIsLimit := fixed_is_limit
theorem transport_first_level : CoboundaryCocycleTransportAlongHom := transport_first_level_holds
theorem transportNorm : TransportNorm := transport_norm_relation
theorem trDualExists : TrDualExists := trace_dual_exists
theorem frobA : FrobA := frobenius_on_ring_a

end Formalism.L2.Th1.D
end

section
namespace Formalism.L2.Th1.D

theorem ringAFacts : RingAFacts := ring_a_facts
theorem kurIntegers : KurIntegers := KurIntegers_of ringAFacts
theorem kurUnram : KurUnram := KurUnram_of kurIntegers
theorem kurRoots : KurRoots := unramified_completion_roots
theorem kurComplete : KurComplete := unramified_completion_complete
theorem frobAIsom : FrobAIsom := FrobAIsom_of ringAFacts
theorem kurFrob : KurFrob := KurFrob_of frobA frobAIsom kurIntegers kurUnram
theorem fOfBetaHyp : FOfBetaHyp := f_of_beta_hypotheses

end Formalism.L2.Th1.D
end
