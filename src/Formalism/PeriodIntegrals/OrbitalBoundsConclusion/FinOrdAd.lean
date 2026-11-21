import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicFiniteOrder.Assembly
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitKronecker.EqZeroOfMulVec
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitKronecker.IntRootProp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerBoundedIntegrality.Imports
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerBoundedIntegrality.EvalIntMapEqZero
import Formalism.PeriodIntegrals.FinOrdAd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicCompactDensity.ExistsNatLocal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactTensorDensity.TensCpctDenOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PositiveDefiniteness.SplittingOfExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PositiveDefiniteness.PositiveDefiniteSecond

section
theorem unit_kronecker : PI.UnitKron :=
  PI.UnitKronW.unitKron_of PI.UnitKronW.stepA PI.UnitKronW.stepB PI.UnitKronW.stepC
end

section
theorem power_bounded_integral : PI.PowBddInt :=
  PI.PowBddIntWork.powBddInt_of PI.PowBddIntWork.stepA PI.PowBddIntWork.stepB
end

section
theorem compactBounded : PI.AdCpctDen := PI.adCpctDen
end

section
theorem tensor_compact_dense : PI.TensCpctDen := PI.tensCpctDen_of compactBounded
end

section
theorem positive_definite_form : PI.DefPosDef :=
  PI.DefPosDefWork.defPosDef_of PI.DefPosDefWork.splitting_of_extension PI.DefPosDefWork.positive_definite_second
end

section
theorem finite_order_adelic : PI.FinOrdAd :=
  PI.finOrdAd_of unit_kronecker power_bounded_integral tensor_compact_dense positive_definite_form
end
