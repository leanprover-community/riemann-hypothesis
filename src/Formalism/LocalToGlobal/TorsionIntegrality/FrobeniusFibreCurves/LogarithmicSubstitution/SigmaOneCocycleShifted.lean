import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalB
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementC

noncomputable section

namespace Formalism.L2.Th1.B.Cor

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)



theorem cc_Dinv {K : Type} [Field K] [CharZero K] (l f : PowerSeries K)
    (h1 : PowerSeries.coeff 1 l = 1) :
    PowerSeries.constantCoeff (Dinv l f) = PowerSeries.coeff 1 f := by
  have key : ∀ g : PowerSeries K, PowerSeries.constantCoeff (PowerSeries.derivative K g) =
      PowerSeries.coeff 1 g := by
    intro g
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
    simp
  unfold Dinv
  rw [map_mul, PowerSeries.constantCoeff_inv, key, key, h1, inv_one, one_mul]

theorem first_jet_of_formal_law : JetOne := by
  intro K _ _ _ l i f hl0 hl1 hi hS
  obtain ⟨hi0, -, hil⟩ := hi
  obtain ⟨hg0, hE⟩ := hS
  have hi1 : PowerSeries.coeff 1 i = -1 := by
    have e := law_coeff_one_subst l i hi0
    rw [hil, map_neg, hl1, one_mul] at e
    exact e.symm
  have hE1 : PowerSeries.coeff 1
      (PowerSeries.subst (PowerSeries.subst i f - f : PowerSeries K) (PowerSeries.exp K) :
        PowerSeries K) = PowerSeries.coeff 1 (PowerSeries.subst i f - f : PowerSeries K) := by
    rw [law_coeff_one_subst _ _ hg0, PowerSeries.coeff_exp]
    simp
  have hn : ‖PowerSeries.coeff 1 (PowerSeries.subst i f - f : PowerSeries K)‖ ≤ 1 := by
    rw [← hE1]
    exact hE (Finsupp.single () 1)
  rw [map_sub, law_coeff_one_subst f i hi0, hi1] at hn
  rw [cc_Dinv l f hl1, ← norm_neg]
  have : -(2 * PowerSeries.coeff 1 f) = PowerSeries.coeff 1 f * -1 - PowerSeries.coeff 1 f := by
    ring
  rw [this]
  exact hn


end Formalism.L2.Th1.B.Cor
