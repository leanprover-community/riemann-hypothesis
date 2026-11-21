import Mathlib
import Formalism.ThetaSupremumBounds.StatementC

open Finset
open scoped Real

namespace Formalism.DimensionVariation

open Formalism.LatticeIndexTer (ph)


theorem period_value : PeriodValue := by
  intro d v rdE A1 Z LL0 p_power_smul_sub_sum logOmK logOm hd hv hrd hZ1 hZ2 hFE hK hOm
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have hpi := Real.pi_pos
  have e1 : Real.log (2 / Real.sqrt d) = Real.log 2 - Real.log d / 2 := by
    rw [Real.log_div (by norm_num) hs.ne', Real.log_sqrt hd.le]
  have e2 : Real.log (2 * π) = Real.log 2 + Real.log π := Real.log_mul (by norm_num) hpi.ne'
  have e3 : Real.log (d / π) = Real.log d - Real.log π := Real.log_div hd.ne' hpi.ne'
  have e4 : Real.log (2 * π / Real.sqrt d) = Real.log 2 + Real.log π - Real.log d / 2 := by
    rw [Real.log_div (by positivity) hs.ne', e2, Real.log_sqrt hd.le]
  have e5 : Real.log (π / v) = Real.log π - Real.log v := Real.log_div hpi.ne' hv.ne'
  have e6 : Real.log rdE = Real.log 2 + Real.log v := by
    rw [hrd, Real.log_mul (by norm_num) hv.ne']
  have e7 : Real.log (Real.sqrt d) = Real.log d / 2 := Real.log_sqrt hd.le
  rw [e1] at hZ1; rw [e2] at hZ2; rw [e3] at hFE; rw [e6, e7] at hOm
  rw [e4, e5]
  refine ⟨by linarith, by linarith, by linarith⟩

end Formalism.DimensionVariation
