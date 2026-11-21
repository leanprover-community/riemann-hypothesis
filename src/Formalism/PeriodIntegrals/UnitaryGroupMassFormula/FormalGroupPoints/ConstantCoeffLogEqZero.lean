import Formalism.PeriodIntegrals.FglPtW

noncomputable section

namespace PI.UnitaryGroupMassFormula.FglPtW

open PI.FglPtW

theorem constantCoeff_log_eq_zero {K : Type} [CommRing K] {l ex : PowerSeries K}
    (h0 : PowerSeries.constantCoeff ex = 0) (hlex : PowerSeries.subst ex l = PowerSeries.X) :
    PowerSeries.constantCoeff l = 0 := by
  have hex : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have h := congrArg MvPowerSeries.constantCoeff hlex
  rw [PowerSeries.constantCoeff_subst hex, finsum_eq_single _ 0] at h
  · have h' := h.trans PowerSeries.constantCoeff_X
    simpa using h'
  · intro d hd
    have : MvPowerSeries.constantCoeff (ex ^ d) = 0 := by
      rw [map_pow]
      have h0' : MvPowerSeries.constantCoeff ex = 0 := h0
      rw [h0', zero_pow hd]
    rw [this, smul_zero]



end PI.UnitaryGroupMassFormula.FglPtW

end
