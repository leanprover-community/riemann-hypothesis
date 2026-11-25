module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GrowthUnitaryGroupRpowNegIntegrable
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingExistence
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemma3
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.MeasurableSpace

@[expose] public section

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.QuantumDeterminants

theorem gN_nonneg_bessel_integrability {k r : ℕ} (x : Formalism.FourierDecayAlt.B.Mat k r) : 0 ≤ Formalism.FourierDecayAlt.B.gN x := Real.sqrt_nonneg _

theorem gN_eq_one_of_zero_dim (x : Formalism.FourierDecayAlt.B.Mat 0 0) (hx : x ∈ UH (Hpk 0 0)) : Formalism.FourierDecayAlt.B.gN x = 1 := by
  have h := congrFun (congrFun (show xᴴ * Hpk 0 0 * x = Hpk 0 0 from hx) 0) 0
  simp [Matrix.mul_apply, Hpk] at h
  have h1 : Complex.normSq (x 0 0) = 1 := by
    have h4 : ((Complex.normSq (x 0 0) : ℝ) : ℂ) = 1 := by rw [Complex.normSq_eq_conj_mul_self, h]
    exact_mod_cast h4
  unfold Formalism.FourierDecayAlt.B.gN
  simp [h1]

theorem integrable_gN_rpow_of_lintegral_lt_top {k r : ℕ} {μ : Measure (Mt k r)} {A : ℝ}
    (h : (∫⁻ x : Mt k r, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-A)) ∂μ) < ∞) :
    Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-A)) μ := by
  have hmeas : Measurable fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-A) := by
    unfold Formalism.FourierDecayAlt.B.gN
    fun_prop
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x =>
    Real.rpow_nonneg (gN_nonneg_bessel_integrability _) _)).2 h

theorem growth_group_bound : Formalism.FourierDecayAlt.ThreeDimData.GrowthG := by
  apply _root_.GlobalTheory.gN_rpow_neg_integrable_haar <;> assumption

end Formalism.FourierDecayAlt.P
