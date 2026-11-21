import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinS2LimitFormula
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Taylor
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.TaylorWp
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.TaylorSigma
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaScale
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.WeierstrassNumeratorDenominator

noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism.L2.Th1.CM (wpNum wpDen uSer IsGoodModel)

namespace Formalism.L2.Th1.F

open PowerSeries TaylorWp

namespace USer

def num (L : PeriodPair) (z : ℂ) : ℂ := 1 + z ^ 2 * L.weierstrassPExcept 0 z

def den (L : PeriodPair) (z : ℂ) : ℂ := 1 + -(1 / 2) * z ^ 3 * deriv (L.weierstrassPExcept 0) z



theorem den_zero (L : PeriodPair) : den L 0 = 1 := by
  simp [den]




end USer





end Formalism.L2.Th1.F
