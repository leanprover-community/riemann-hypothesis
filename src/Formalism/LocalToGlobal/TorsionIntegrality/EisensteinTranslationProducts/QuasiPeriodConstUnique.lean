import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.AnalyticIdentityTheoremsZetaFacts
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaConv
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaBasic
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaLog
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.ZetaQuasi
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaQuasi
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.EtaEis
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Legendre
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstUniqueOf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.OperatorUComm
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SgStar
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.HermHalfRight

section
namespace Formalism.L2.Th1.F

theorem zetaSummable : ZetaSummable := zeta_summable
theorem zetaHasDeriv : ZetaHasDeriv := zeta_has_deriv
theorem zetaOdd : ZetaOdd := zeta_odd
theorem zetaQuasi : ZetaQuasi := zetaQuasi_of zetaHasDeriv zetaOdd
theorem sigmaSummable : SigmaSummable := sigma_summable
theorem sigmaProdLU : SigmaProdLU := sigma_product_locally_uniform
theorem sigmaEntire : SigmaEntire := sigmaEntire_of sigmaProdLU
theorem sigmaOdd : SigmaOdd := sigma_odd
theorem sigmaZero : SigmaZero := sigmaZero_of sigmaSummable
theorem sigmaLogDeriv : SigmaLogDeriv := sigmaLogDeriv_of sigmaProdLU sigmaSummable zetaSummable
theorem sigmaQuasi : SigmaQuasi := sigmaQuasi_of zetaQuasi sigmaLogDeriv sigmaEntire sigmaOdd sigmaZero
theorem sigmaSimple : SigmaSimple := sigmaSimple_of sigmaQuasi sigmaEntire (sigmaDerivZero_of sigmaProdLU)
theorem etaEisenstein : EtaEisenstein := etaEisenstein_of zetaSummable zetaOdd
theorem legendre : Legendre := legendre_of etaEisenstein

end Formalism.L2.Th1.F
end

section
namespace Formalism.L2.Th1.F

theorem areaPos : AreaPos := areaPos_thm
theorem etaSplit : EtaSplit := etaSplit_of legendre
theorem altEInt : AltEInt := alternating_form_integral
theorem altEBasis : AltEBasis := alternating_form_basis
theorem semiCharMul : SemiCharMul := semi_character_mul
theorem opUMul : OpUMul := operator_u_mul
theorem opUComm : OpUComm := operator_u_comm
theorem sgStarQuasi : SgStarQuasi := sgStarQuasi_of sigmaQuasi etaSplit
theorem sgStarFixed : SgStarFixed := sgStarFixed_of sgStarQuasi
theorem sigmaTaylorLow :
    ∀ L : PeriodPair, iteratedDeriv 2 (wSigma L) 0 = 0 ∧ iteratedDeriv 3 (wSigma L) 0 = 0 :=
  sigmaTaylorLow_of sigmaEntire sigmaSummable
theorem sgStarBasic : SgStarBasic :=
  sgStarBasic_of sigmaEntire sigmaOdd sigmaZero sigmaSimple sigmaTaylorLow
theorem th0Const : ThetaZeroConstant := th0Const_of sgStarBasic
theorem th0Basic : ThetaZeroBasic := th0Basic_of sgStarBasic sgStarQuasi altEInt
theorem th0Class : ThetaZeroClass := th0Class_of sgStarBasic sgStarQuasi
theorem th0LogDeriv : ThetaZeroLogDerivative := th0LogDeriv_of sigmaLogDeriv etaSplit zetaQuasi zetaOdd

end Formalism.L2.Th1.F
end
