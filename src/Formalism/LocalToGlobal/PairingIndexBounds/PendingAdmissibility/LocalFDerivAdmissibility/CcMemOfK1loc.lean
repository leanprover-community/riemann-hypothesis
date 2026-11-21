import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem

namespace Formalism.L2.PairingIndexBounds.PowerSeriesNecessity

variable {p : ℕ} [Fact p.Prime]

theorem cc_subst {σ τ R : Type} [CommRing R] {a : σ → MvPowerSeries τ R} (ha : MvPowerSeries.HasSubst a)
    (h0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by
  classical
  rw [MvPowerSeries.constantCoeff_subst ha, finsum_eq_single _ 0]
  · simp
  · intro d hd
    obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push Not at h
      exact hd (Finsupp.ext h)
    have hs' : s ∈ d.support := Finsupp.mem_support_iff.2 hs
    rw [Finsupp.prod, map_prod, Finset.prod_eq_zero hs']
    · simp
    · rw [map_pow, h0 s, zero_pow hs]

theorem cc_expS {ι : Type} (f : MvPowerSeries ι (K0 p)) : MvPowerSeries.constantCoeff (expS p f) = 1 := by
  show expS p f 0 = 1
  simp [expS]

theorem cc_logF : PowerSeries.constantCoeff (logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [logF, PowerSeries.coeff_mk]

theorem cc_logX {ι : Type} (K1 : Type) [Field K1] [Algebra (K0 p) K1] (i : ι) :
    MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι K1)
      (PowerSeries.map (algebraMap (K0 p) K1) (logF p))) = 0 := by
  refine PowerSeries.constantCoeff_subst_eq_zero (by simp) _ ?_
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, cc_logF, map_zero]

theorem hasSubst_logX {ι : Type} [Finite ι] (K1 : Type) [Field K1] [Algebra (K0 p) K1] :
    MvPowerSeries.HasSubst (fun i : ι => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι K1)
      (PowerSeries.map (algebraMap (K0 p) K1) (logF p))) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (cc_logX K1)




end Formalism.L2.PairingIndexBounds.PowerSeriesNecessity
