import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.ChartLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushCut

section
noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace PI.RhsWLim.W

theorem chartJac : ChartJac := by
  intro E _ _ _ _ _ _ Φ ν δ hΦ hdet hδ hδtop hU
  obtain ⟨U, hU, hνU⟩ := hU
  have hstrict : HasStrictFDerivAt Φ
      ((ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero (fderiv ℝ Φ 0) hdet : E ≃L[ℝ] E) :
        E →L[ℝ] E) 0 := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact hΦ.hasStrictFDerivAt (by norm_num)
  have hsrc : (hstrict.toOpenPartialHomeomorph Φ).source ∈ 𝓝 (0 : E) :=
    (hstrict.toOpenPartialHomeomorph Φ).open_source.mem_nhds hstrict.mem_toOpenPartialHomeomorph_source
  have hev : ∀ᶠ y in 𝓝 (0 : E), ContDiffAt ℝ 1 Φ y := hΦ.eventually (by simp)
  have hUpre : Φ ⁻¹' U ∈ 𝓝 (0 : E) := hΦ.continuousAt.preimage_mem_nhds hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (Filter.inter_mem hsrc hev) hUpre)
  have hcont : ContinuousAt (fun x => ENNReal.ofReal |(fderiv ℝ Φ x).det| * δ (Φ x)) 0 := by
    have hA : ContinuousAt (fun x => ENNReal.ofReal |(fderiv ℝ Φ x).det|) 0 :=
      ENNReal.continuous_ofReal.continuousAt.comp (continuous_abs.continuousAt.comp
        (ContinuousLinearMap.continuous_det.continuousAt.comp (hΦ.continuousAt_fderiv (by norm_num))))
    have hB : ContinuousAt (fun x => δ (Φ x)) 0 := hδ.comp hΦ.continuousAt
    exact ENNReal.Tendsto.mul hA (Or.inr hδtop) hB (Or.inr ENNReal.ofReal_ne_top)
  have hntop : ENNReal.ofReal |(fderiv ℝ Φ 0).det| * δ (Φ 0) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hδtop
  have heq : ∀ ρ : ℝ, 0 < ρ → ρ < ε → ν (Φ '' Metric.ball 0 ρ) =
      ∫⁻ x in Metric.ball 0 ρ, ENNReal.ofReal |(fderiv ℝ Φ x).det| * δ (Φ x) := by
    intro ρ _ hρε
    have hsub : Metric.ball (0 : E) ρ ⊆ Metric.ball 0 ε := Metric.ball_subset_ball hρε.le
    have hinj : Set.InjOn Φ (Metric.ball 0 ρ) := by
      rw [← hstrict.toOpenPartialHomeomorph_coe]
      exact (hstrict.toOpenPartialHomeomorph Φ).injOn.mono fun x hx => (hball (hsub hx)).1.1
    have hcd : ∀ x ∈ Metric.ball (0 : E) ρ, ContDiffAt ℝ 1 Φ x := fun x hx => (hball (hsub hx)).1.2
    have hdiff : ∀ x ∈ Metric.ball (0 : E) ρ,
        HasFDerivWithinAt Φ (fderiv ℝ Φ x) (Metric.ball 0 ρ) x := fun x hx =>
      ((hcd x hx).differentiableAt one_ne_zero).hasFDerivAt.hasFDerivWithinAt
    have hcon : ContinuousOn Φ (Metric.ball 0 ρ) := fun x hx =>
      (hcd x hx).continuousAt.continuousWithinAt
    have hmeas : MeasurableSet (Φ '' Metric.ball 0 ρ) :=
      Metric.isOpen_ball.measurableSet.image_of_continuousOn_injOn hcon hinj
    have himg : Φ '' Metric.ball 0 ρ ⊆ U := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hball (hsub hx)).2
    rw [hνU _ himg hmeas]
    exact MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
      Metric.isOpen_ball.measurableSet hdiff hinj δ
  have hlim := chartLim E E Φ ν (fun x => ENNReal.ofReal |(fderiv ℝ Φ x).det| * δ (Φ x)) hcont hntop
    ⟨ε, hε, heq⟩
  have h0 : (ENNReal.ofReal |(fderiv ℝ Φ 0).det| * δ (Φ 0)).toReal =
      (δ (Φ 0)).toReal * |(fderiv ℝ Φ 0).det| := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), mul_comm]
  rw [← h0]
  exact hlim

end PI.RhsWLim.W
end
end

section
noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

def psiE (k r : ℕ) (T' : ℝ) (q : TrE k) : (Fin k → ℂ) × ℂ :=
  opCo k r (NormedSpace.exp (opGen k r q) *ᵥ opBase k r T')

def kapT (k : ℕ) (v : (Fin k → ℂ) × ℂ) : TrE k :=
  (WithLp.equiv 2 (Option (Fin k × Bool) → ℝ)).symm (fun o => match o with
    | none => Complex.arg v.2
    | some (a, b) => if b then (v.1 a).im else (v.1 a).re)

def phiT (k r : ℕ) (T' : ℝ) (q : TrE k) : TrE k := kapT k (psiE k r T' q)

def HypChart : Prop :=
  ∀ (k r : ℕ) (T' : ℝ), 1 ≤ k → 0 < T' → ∃ ε > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ε →
    hypM k T' (opE k r T' ρ) = (1 / 2) * volume (phiT k r T' '' Metric.ball 0 ρ)

def PhiDiff : Prop :=
  ∀ (k r : ℕ) (T' : ℝ), 1 ≤ k → 0 < T' →
    ContDiffAt ℝ 1 (phiT k r T') 0 ∧ (fderiv ℝ (phiT k r T') 0).det = (T' / 2) ^ k

theorem hypLocal_of (hJ : ChartJac) (hC : HypChart) (hD : PhiDiff) : HypLocal := by
  intro k r T' hk hT
  obtain ⟨hcd, hdet⟩ := hD k r T' hk hT
  obtain ⟨ε, hε, hV⟩ := hC k r T' hk hT
  have hdet0 : (fderiv ℝ (phiT k r T') 0).det ≠ 0 := by
    rw [hdet]; exact pow_ne_zero _ (by positivity)
  have hlim := hJ (TrE k) (phiT k r T') volume (fun _ => 1) hcd hdet0
    continuousAt_const ENNReal.one_ne_top ⟨Set.univ, Filter.univ_mem, fun A _ _ => by simp⟩
  have key := hlim.const_mul (1 / 2 : ℝ)
  have hval : (1 / 2 : ℝ) * ((1 : ℝ≥0∞).toReal * |(fderiv ℝ (phiT k r T') 0).det|) =
      T' ^ k / 2 ^ (k + 1) := by
    rw [hdet, ENNReal.toReal_one, one_mul, abs_of_pos (by positivity), div_pow, pow_succ]
    field_simp
    try ring
  rw [hval] at key
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hε)] with ρ hρ0 hρε
  rw [hV ρ hρ0 hρε, tVol, ENNReal.toReal_mul, mul_div_assoc]
  congr 1
  simp

end PI.RhsWLim.W
end
end
