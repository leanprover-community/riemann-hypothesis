import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.CommensurableHolds
import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.IdempotentCalculationHolds
import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.GlueSmulSame
import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.AsmOfMemComplF
import Formalism.LocalToGlobal.Columns.RecLevelHost
import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.EvaluationNeZeroHolds
import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.DetAddDiagonalCons
import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.ApproximationAdelicHolds
import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.Cayley
import Formalism.LocalToGlobal.GenusGluing.GenusApproximation.GenusApproximationProofs.WeakApproxAllOf

section
noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

theorem glueExists_holds : GlueExists := glueExists_of idempotentCalculation_holds

theorem genusToPoint_holds : GenusToPoint :=
  genusToPoint_of localEquality_holds memLocalizedStd_holds idempotentCofinite_holds idempotentCalculation_holds glueExists_holds commensurable_holds

theorem pointToGenus_holds : PointToGenus :=
  pointToGenus_of localEquality_holds memLocalizedStd_holds idempotentDenominator_holds idempotentCalculation_holds

theorem localToAdelic_holds : LocToAd := locToAd_of genusToPoint_holds

theorem adelicToLocal_holds : AdToLoc := adToLoc_of pointToGenus_holds

theorem localAdelicEquiv_holds : Bridge := bridge_of localToAdelic_holds adelicToLocal_holds

end Formalism.L2.GenusGluing.Gen
end
end

section
noncomputable section

namespace Formalism.L2.GenusGluing.Gen

open NumberField IsDedekindDomain Matrix Formalism.L2.Col
open scoped TensorProduct

theorem shiftDiagonal_holds : ShiftDiag := shiftDiag_of shiftOne_holds

theorem cayleyApproximation_holds : CayleyStep := cayleyStep_of evaluationNeZero_holds approximationAdelic_holds unitNearOne_holds

theorem weakApproximationAll_holds : WeakApproxAll := weakApproxAll_of shiftDiagonal_holds cayleyApproximation_holds integralAtInverse_holds

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem weakApproximation_unitary (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) : WeakApproxU hc n := weakApproximationAll_holds F E hc n

theorem unimodGenus_iff (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) : UnimodGenusLoc E n ↔ UnimodGenus hc n :=
  localAdelicEquiv_holds F E hc n (weakApproximation_unitary hc n)

end Formalism.L2.GenusGluing.Gen
end
end
