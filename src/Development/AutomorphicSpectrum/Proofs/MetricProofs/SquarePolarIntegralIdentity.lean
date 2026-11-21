import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereSingularTotalMassDegree
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralMultilinearExpansion
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSystemRegularityProperties
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralParametrizedCover
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ContDiffAtFrameEntry
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogSineMongeAmpereNormalized
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsHolomorphicNormalFrame
import Development.WeilBound.CoreStatements.PluriharmonicCharts.ProjectiveLineNormalFrame
import BuildAid.ForwardExisting
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XSqDens
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSquareRegularizedConvergence

section
section
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem normal_holomorphic_frame : ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y₀ : Fin d → ℂ), (G y₀).PosDef → (∀ y, (G y).IsHermitian) → (∀ p q, ContDiffAt ℝ 2 (fun y => G y p q) y₀) → ∃ g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ, (∀ p q, Differentiable ℂ fun y => g y p q) ∧ IsUnit (g y₀).det ∧ (g y₀)ᴴ * G y₀ * g y₀ = 1 ∧ ∀ p q, fderiv ℝ (fun y => ((g y)ᴴ * G y * g y) p q) y₀ = 0 :=
  PositivityTheory.Xgp.projective_line_normal_frame

end GlobalTheory.CompanionTheory.Ar.PB
end

open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_normal_frame : ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y₀ : Fin d → ℂ), (G y₀).PosDef → (∀ y, (G y).IsHermitian) → (∀ p q, ContDiffAt ℝ 2 (fun y => G y p q) y₀) → ∃ g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ, (∀ p q, Differentiable ℂ fun y => g y p q) ∧ IsUnit (g y₀).det ∧ (g y₀)ᴴ * G y₀ * g y₀ = 1 ∧ ∀ p q, fderiv ℝ (fun y => ((g y)ᴴ * G y * g y) p q) y₀ = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.normal_holomorphic_frame
end

section
section
open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

theorem GlobalTheory.CompanionTheory.Ar.PB.FibPt.exists_frame_normal_near :
    ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) →
      (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) →
      ∃ g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ, (∀ p q, Differentiable ℂ fun y' => g y' p q) ∧
        IsUnit (g y).det ∧ (∀ᶠ y' in 𝓝 y, ((g y')ᴴ * G y' * g y').PosDef) ∧
        (∀ p q, ContDiffAt ℝ 2 (fun y' => ((g y')ᴴ * G y' * g y') p q) y) ∧
        (g y)ᴴ * G y * g y = 1 ∧ ∀ p q, fderiv ℝ (fun y' => ((g y')ᴴ * G y' * g y') p q) y = 0 := by
  intro d G y hpd hC
  let Gh : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ := fun y' => (1 / 2 : ℂ) • (G y' + (G y')ᴴ)
  have hent : ∀ y' p q, Gh y' p q = (1 / 2 : ℂ) * (G y' p q + (starRingEnd ℂ) (G y' q p)) := by
    intro y' p q
    simp [Gh, Matrix.smul_apply, Matrix.add_apply, Matrix.conjTranspose_apply]
    ring
  have hherm : ∀ y', (Gh y').IsHermitian := by
    intro y'
    ext p q
    rw [Matrix.conjTranspose_apply, hent, hent]
    have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
      apply Complex.ext <;> simp
    simp only [RCLike.star_def, map_mul, map_add, Complex.conj_conj, hhalf]
    ring
  have hEq : ∀ᶠ y' in 𝓝 y, Gh y' = G y' := by
    filter_upwards [hpd] with y' h
    have e : (G y')ᴴ = G y' := h.isHermitian.eq
    ext p q
    simp only [Gh, e, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  have hy : Gh y = G y := hEq.self_of_nhds
  have hpdy : (Gh y).PosDef := by
    rw [hy]
    exact hpd.self_of_nhds
  have hCh : ∀ p q, ContDiffAt ℝ 2 (fun y' => Gh y' p q) y := by
    intro p q
    have h1 := hC p q
    have h2 : ContDiffAt ℝ 2 (fun y' => (starRingEnd ℂ) (G y' q p)) y :=
      Complex.conjCLE.contDiff.contDiffAt.comp y (hC q p)
    have e : (fun y' => Gh y' p q) = fun y' => (1 / 2 : ℂ) * (G y' p q + (starRingEnd ℂ) (G y' q p)) :=
      funext fun y' => hent y' p q
    rw [e]
    exact contDiffAt_const.mul (h1.add h2)
  obtain ⟨g, hg, hu, h1, hd⟩ := GlobalTheory.T.exists_holomorphic_normal_frame d Gh y hpdy hherm hCh
  refine ⟨g, hg, hu, ?_, GlobalTheory.CompanionTheory.Ar.PB.FibPt.contDiffAt_frame_entry G g y hC hg, ?_, ?_⟩
  · have hc : ∀ p q, ContinuousAt (fun y' => g y' p q) y := fun p q => (hg p q).continuous.continuousAt
    have hdetc : ContinuousAt (fun y' => (g y').det) y := by
      simp only [Matrix.det_fin_two]
      exact ((hc 0 0).mul (hc 1 1)).sub ((hc 0 1).mul (hc 1 0))
    have hne : ∀ᶠ y' in 𝓝 y, (g y').det ≠ 0 := hdetc.eventually_ne hu.ne_zero
    filter_upwards [hpd, hne] with y' ha hb
    exact (GlobalTheory.T.log_sine_mobius_transform (G y') (g y') ha (isUnit_iff_ne_zero.mpr hb)).1
  · rw [← hy]
    exact h1
  · intro p q
    have hev : (fun y' => ((g y')ᴴ * G y' * g y') p q) =ᶠ[𝓝 y] fun y' => ((g y')ᴴ * Gh y' * g y') p q := by
      filter_upwards [hEq] with y' h
      rw [h]
    rw [hev.fderiv_eq]
    exact hd p q
end

open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_unitary_normal_frame_2x2 : ∀ (d : ℕ) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) → (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) → ∃ g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ, (∀ p q, Differentiable ℂ fun y' => g y' p q) ∧ IsUnit (g y).det ∧ (∀ᶠ y' in 𝓝 y, ((g y')ᴴ * G y' * g y').PosDef) ∧ (∀ p q, ContDiffAt ℝ 2 (fun y' => ((g y')ᴴ * G y' * g y') p q) y) ∧ (g y)ᴴ * G y * g y = 1 ∧ ∀ p q, fderiv ℝ (fun y' => ((g y')ᴴ * G y' * g y') p q) y = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.FibPt.exists_frame_normal_near
end

section
section
open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.FibPt

theorem subsingleton_affine_zero {p q : ℂ} (h : p ≠ 0 ∨ q ≠ 0) :
    {a : ℂ | p + q * a = 0}.Subsingleton := by
  intro a ha b hb
  have ha' : p + q * a = 0 := ha
  have hb' : p + q * b = 0 := hb
  have hq : q ≠ 0 := by
    rcases h with hp | hq
    · intro hq0
      rw [hq0, zero_mul, add_zero] at ha'
      exact hp ha'
    · exact hq
  exact mul_left_cancel₀ hq (by linear_combination ha' - hb')

theorem det_smulRight_restrictScalars (w : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) w).restrictScalars ℝ).det = Complex.normSq w := by
  have e : ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) w = w • ContinuousLinearMap.id ℂ ℂ := by
    ext
    simp
  rw [e, ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
    ReciprocityTheory.AnForm.A.det_restrictScalars_real]
  simp

theorem hasDerivAt_mob (g : Matrix (Fin 2) (Fin 2) ℂ) {a : ℂ} (ha : den g a ≠ 0) :
    HasDerivAt (mob g) (mobD g a) a := by
  unfold mob mobD
  unfold den at *
  have h1 : HasDerivAt (fun a => g 1 0 + g 1 1 * a) (g 1 1) a := by
    simpa using ((hasDerivAt_id a).const_mul (g 1 1)).const_add (g 1 0)
  have h2 : HasDerivAt (fun a => g 0 0 + g 0 1 * a) (g 0 1) a := by
    simpa using ((hasDerivAt_id a).const_mul (g 0 1)).const_add (g 0 0)
  refine (h1.div h2 ha).congr_deriv ?_
  rw [det_fin_two]
  congr 1
  ring

theorem injOn_mob (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g.det ≠ 0) :
    Set.InjOn (mob g) {a | den g a ≠ 0} := by
  intro a ha b hb hab
  have ha' : den g a ≠ 0 := ha
  have hb' : den g b ≠ 0 := hb
  unfold mob at hab
  rw [div_eq_div_iff ha' hb'] at hab
  unfold den at hab
  rw [det_fin_two] at hg
  have h : (a - b) * (g 0 0 * g 1 1 - g 0 1 * g 1 0) = 0 := by linear_combination hab
  rcases mul_eq_zero.1 h with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h hg

theorem mem_image_mob (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : g.det ≠ 0) {b : ℂ}
    (hb : g 1 1 + (-g 0 1) * b ≠ 0) : b ∈ mob g '' {a | den g a ≠ 0} := by
  have hd : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0 := by rwa [det_fin_two] at hg
  have hci : (g 1 1 + -g 0 1 * b) * (g 1 1 + -g 0 1 * b)⁻¹ = 1 := mul_inv_cancel₀ hb
  have hden : den g ((g 0 0 * b - g 1 0) / (g 1 1 + (-g 0 1) * b)) =
      (g 0 0 * g 1 1 - g 0 1 * g 1 0) * (g 1 1 + (-g 0 1) * b)⁻¹ := by
    unfold den
    rw [div_eq_mul_inv]
    linear_combination (-g 0 0) * hci
  refine ⟨(g 0 0 * b - g 1 0) / (g 1 1 + (-g 0 1) * b), ?_, ?_⟩
  · show den g _ ≠ 0
    rw [hden]
    exact mul_ne_zero hd (inv_ne_zero hb)
  · unfold mob
    rw [hden, div_eq_iff (mul_ne_zero hd (inv_ne_zero hb)), div_eq_mul_inv (g 0 0 * b - g 1 0)]
    linear_combination (-g 1 0) * hci

theorem integral_normSq_mobD_mul_comp_mob (g : Matrix (Fin 2) (Fin 2) ℂ) (hu : IsUnit g.det)
    (f : ℂ → ℝ) :
    ∫ a : ℂ, Complex.normSq (mobD g a) * f (mob g a) = ∫ b : ℂ, f b := by
  have hdet : g.det ≠ 0 := hu.ne_zero
  have hcont : Continuous (den g) := by
    unfold den
    fun_prop
  have hs : MeasurableSet {a : ℂ | den g a ≠ 0} := (isOpen_ne_fun hcont continuous_const).measurableSet
  have hderiv : ∀ a ∈ {a : ℂ | den g a ≠ 0}, HasFDerivWithinAt (mob g)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (mobD g a)).restrictScalars ℝ)
      {a : ℂ | den g a ≠ 0} a :=
    fun a ha => ((hasDerivAt_mob g ha).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume hs hderiv (injOn_mob g hdet) f
  simp only [det_smulRight_restrictScalars, abs_of_nonneg (Complex.normSq_nonneg _), smul_eq_mul] at hcv
  rw [det_fin_two] at hdet
  have hnull1 : ∀ᵐ a ∂(volume : Measure ℂ), a ∈ {a : ℂ | den g a ≠ 0} := by
    have h01 : g 0 0 ≠ 0 ∨ g 0 1 ≠ 0 := by
      by_contra hc
      rw [not_or, not_not, not_not] at hc
      apply hdet
      rw [hc.1, hc.2]
      ring
    refine mem_ae_iff.2 (measure_mono_null ?_ ((subsingleton_affine_zero h01).countable.measure_zero _))
    intro a ha
    have ha' : ¬ den g a ≠ 0 := ha
    rw [not_not] at ha'
    exact ha'
  have hnull2 : ∀ᵐ b ∂(volume : Measure ℂ), b ∈ mob g '' {a : ℂ | den g a ≠ 0} := by
    have h11 : g 1 1 ≠ 0 ∨ -g 0 1 ≠ 0 := by
      by_contra hc
      rw [not_or, not_not, not_not, neg_eq_zero] at hc
      apply hdet
      rw [hc.1, hc.2]
      ring
    refine mem_ae_iff.2 (measure_mono_null ?_ ((subsingleton_affine_zero h11).countable.measure_zero _))
    intro b hb
    by_contra hne
    exact hb (mem_image_mob g hu.ne_zero hne)
  rw [Measure.restrict_eq_self_of_ae_mem hnull1, Measure.restrict_eq_self_of_ae_mem hnull2] at hcv
  exact hcv.symm

end GlobalTheory.CompanionTheory.Ar.PB.FibPt
end

open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_normSq_mobD_mul_comp_mob' : ∀ (g : Matrix (Fin 2) (Fin 2) ℂ), IsUnit g.det → ∀ f : ℂ → ℝ, ∫ a : ℂ, Complex.normSq (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g a) * f (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g a) = ∫ b : ℂ, f b := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.FibPt.integral_normSq_mobD_mul_comp_mob
end

section
section
open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq

variable (g : Matrix (Fin 2) (Fin 2) ℂ)

def dom : Set ℂ := {a | den g a ≠ 0}

def cod : Set ℂ := {b | g 1 1 - g 0 1 * b ≠ 0}

variable {g}

theorem det_eq : g.det = g 0 0 * g 1 1 - g 0 1 * g 1 0 := Matrix.det_fin_two g

theorem isOpen_dom : IsOpen (dom g) := by
  have hc : Continuous fun a : ℂ => GlobalTheory.CompanionTheory.Ar.PB.FibPt.den g a := by
    show Continuous fun a : ℂ => g 0 0 + g 0 1 * a
    fun_prop
  exact isOpen_ne_fun hc continuous_const

theorem hasDerivAt_mob {a : ℂ} (ha : a ∈ dom g) : HasDerivAt (mob g) (mobD g a) a := by
  have hden : g 0 0 + g 0 1 * a ≠ 0 := ha
  have h1 : HasDerivAt (fun z : ℂ => g 1 0 + g 1 1 * z) (g 1 1) a := by
    simpa using ((hasDerivAt_id a).const_mul (g 1 1)).const_add (g 1 0)
  have h2 : HasDerivAt (fun z : ℂ => g 0 0 + g 0 1 * z) (g 0 1) a := by
    simpa using ((hasDerivAt_id a).const_mul (g 0 1)).const_add (g 0 0)
  have h := h1.div h2 hden
  have heq : GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g
      = (fun z : ℂ => g 1 0 + g 1 1 * z) / (fun z : ℂ => g 0 0 + g 0 1 * z) := by
    funext z
    rfl
  have hval : GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g a
      = (g 1 1 * (g 0 0 + g 0 1 * a) - (g 1 0 + g 1 1 * a) * g 0 1) / (g 0 0 + g 0 1 * a) ^ 2 := by
    rw [show GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g a = g.det / (g 0 0 + g 0 1 * a) ^ 2 from rfl,
      GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_eq]
    ring
  rw [heq, hval]
  exact h

theorem injOn_mob (hg : IsUnit g.det) : Set.InjOn (mob g) (dom g) := by
  intro a ha b hb hab
  have ha' : g 0 0 + g 0 1 * a ≠ 0 := ha
  have hb' : g 0 0 + g 0 1 * b ≠ 0 := hb
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0 := by
    rw [← GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_eq]
    exact hg.ne_zero
  have h : (g 1 0 + g 1 1 * a) / (g 0 0 + g 0 1 * a)
      = (g 1 0 + g 1 1 * b) / (g 0 0 + g 0 1 * b) := hab
  rw [div_eq_div_iff ha' hb'] at h
  have h2 : (g 0 0 * g 1 1 - g 0 1 * g 1 0) * (a - b) = 0 := by
    linear_combination h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 hdet
  · exact sub_eq_zero.1 h3

theorem image_mob (hg : IsUnit g.det) : mob g '' dom g = cod g := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0 := by
    rw [← GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_eq]
    exact hg.ne_zero
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' : g 0 0 + g 0 1 * a ≠ 0 := ha
    show g 1 1 - g 0 1 * ((g 1 0 + g 1 1 * a) / (g 0 0 + g 0 1 * a)) ≠ 0
    have hval : g 1 1 - g 0 1 * ((g 1 0 + g 1 1 * a) / (g 0 0 + g 0 1 * a))
        = (g 0 0 * g 1 1 - g 0 1 * g 1 0) / (g 0 0 + g 0 1 * a) := by
      field_simp
      ring
    rw [hval]
    exact div_ne_zero hdet ha'
  · intro hb
    have hb' : g 1 1 - g 0 1 * b ≠ 0 := hb
    have hx : (g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b) * (g 1 1 - g 0 1 * b)
        = g 0 0 * b - g 1 0 := div_mul_cancel₀ _ hb'
    have hden : g 0 0 + g 0 1 * ((g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b))
        = (g 0 0 * g 1 1 - g 0 1 * g 1 0) / (g 1 1 - g 0 1 * b) := by
      rw [eq_div_iff hb']
      linear_combination g 0 1 * hx
    have hnum : g 1 0 + g 1 1 * ((g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b))
        = b * (g 0 0 * g 1 1 - g 0 1 * g 1 0) / (g 1 1 - g 0 1 * b) := by
      rw [eq_div_iff hb']
      linear_combination g 1 1 * hx
    refine ⟨(g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b), ?_, ?_⟩
    · show g 0 0 + g 0 1 * ((g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b)) ≠ 0
      rw [hden]
      exact div_ne_zero hdet hb'
    · show (g 1 0 + g 1 1 * ((g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b))) /
          (g 0 0 + g 0 1 * ((g 0 0 * b - g 1 0) / (g 1 1 - g 0 1 * b))) = b
      rw [hnum, hden, div_div_div_cancel_right₀ hb', mul_div_assoc, div_self hdet, mul_one]

theorem null_affine {c d : ℂ} (h : c ≠ 0 ∨ d ≠ 0) : volume {a : ℂ | c + d * a = 0} = 0 := by
  refine Set.Subsingleton.measure_zero ?_ _
  intro x hx y hy
  have hx' : c + d * x = 0 := hx
  have hy' : c + d * y = 0 := hy
  have hd : d ≠ 0 := by
    rintro rfl
    rcases h with hc | hd
    · exact hc (by simpa using hx')
    · exact hd rfl
  have hxy : d * (x - y) = 0 := by
    linear_combination hx' - hy'
  exact sub_eq_zero.1 ((mul_eq_zero.1 hxy).resolve_left hd)

theorem ae_prod_self {V : Set ℂ} (hV : volume Vᶜ = 0) :
    (V ×ˢ V : Set (ℂ × ℂ)) =ᵐ[(volume : Measure (ℂ × ℂ))] (Set.univ : Set (ℂ × ℂ)) := by
  rw [ae_eq_univ]
  have h1 : (volume : Measure (ℂ × ℂ)) (Prod.fst ⁻¹' Vᶜ) = 0 := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_fst.preimage_null hV
  have h2 : (volume : Measure (ℂ × ℂ)) (Prod.snd ⁻¹' Vᶜ) = 0 := by
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_snd.preimage_null hV
  refine measure_mono_null (fun p hp => ?_) (measure_union_null h1 h2)
  simp only [Set.mem_compl_iff, Set.mem_prod, not_and_or] at hp
  simpa only [Set.mem_union, Set.mem_preimage, Set.mem_compl_iff] using hp

theorem null_dom (hg : IsUnit g.det) : volume (dom g)ᶜ = 0 := by
  have hne : g 0 0 ≠ 0 ∨ g 0 1 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hg.ne_zero
    rw [GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_eq, h.1, h.2]
    ring
  refine measure_mono_null (fun a ha => ?_) (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.null_affine hne)
  have ha' : ¬ (g 0 0 + g 0 1 * a ≠ 0) := ha
  exact not_not.1 ha'

theorem null_cod (hg : IsUnit g.det) : volume (cod g)ᶜ = 0 := by
  have hne : g 1 1 ≠ 0 ∨ -g 0 1 ≠ 0 := by
    by_contra h
    push_neg at h
    have h01 : g 0 1 = 0 := neg_eq_zero.1 h.2
    apply hg.ne_zero
    rw [GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_eq, h.1, h01]
    ring
  refine measure_mono_null (fun b hb => ?_) (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.null_affine hne)
  have hb' : ¬ (g 1 1 - g 0 1 * b ≠ 0) := hb
  show g 1 1 + -g 0 1 * b = 0
  linear_combination not_not.1 hb'

theorem det_smul_one (z : ℂ) :
    LinearMap.det ((z • (1 : ℂ →L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = Complex.normSq z := by
  have hmul : ((z • (1 : ℂ →L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = Algebra.lmul ℝ ℂ z := by
    refine LinearMap.ext fun w => ?_
    rw [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
    simp
  rw [hmul, ← Algebra.norm_apply, Algebra.norm_complex_apply]

theorem det_prodMap (z w : ℂ) :
    ((z • (1 : ℂ →L[ℝ] ℂ)).prodMap (w • (1 : ℂ →L[ℝ] ℂ))).det
      = Complex.normSq z * Complex.normSq w := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_prodMap, LinearMap.det_prodMap,
    GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_smul_one, GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_smul_one]

theorem integral_mob_sq (hg : IsUnit g.det) (f : ℂ × ℂ → ℝ) :
    ∫ p : ℂ × ℂ, (Complex.normSq (mobD g p.1) * Complex.normSq (mobD g p.2)) * f (mob g p.1, mob g p.2)
      = ∫ q : ℂ × ℂ, f q := by
  haveI : Measure.IsAddHaarMeasure (volume : Measure (ℂ × ℂ)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hUo : IsOpen (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g) := GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.isOpen_dom
  have hUm : MeasurableSet (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g ×ˢ GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g) :=
    hUo.measurableSet.prod hUo.measurableSet
  have hderiv : ∀ p ∈ GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g ×ˢ GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g,
      HasFDerivWithinAt (Prod.map (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g) (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g))
        ((GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g p.1 • (1 : ℂ →L[ℝ] ℂ)).prodMap
          (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g p.2 • (1 : ℂ →L[ℝ] ℂ)))
        (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g ×ˢ GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g) p := by
    intro p hp
    exact (HasFDerivAt.prodMap p
      (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.hasDerivAt_mob hp.1).complexToReal_fderiv
      (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.hasDerivAt_mob hp.2).complexToReal_fderiv).hasFDerivWithinAt
  have hinj : Set.InjOn (Prod.map (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g) (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g))
      (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g ×ˢ GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.dom g) := by
    intro p hp q hq hpq
    exact Prod.ext (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.injOn_mob hg hp.1 hq.1 (congrArg Prod.fst hpq))
      (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.injOn_mob hg hp.2 hq.2 (congrArg Prod.snd hpq))
  have hcv := integral_image_eq_integral_abs_det_fderiv_smul volume hUm hderiv hinj f
  rw [Set.prodMap_image_prod, GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.image_mob hg,
    setIntegral_congr_set (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.ae_prod_self (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.null_cod hg)),
    setIntegral_congr_set (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.ae_prod_self (GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.null_dom hg)),
    setIntegral_univ, setIntegral_univ] at hcv
  rw [hcv]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.det_prodMap, Prod.map_apply, smul_eq_mul]
  rw [abs_of_nonneg (mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))]
  rfl

end GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq

theorem GlobalTheory.CompanionTheory.Ar.PB.FibPt.integral_mob_sq_main :
    ∀ (g : Matrix (Fin 2) (Fin 2) ℂ), IsUnit g.det → ∀ f : ℂ × ℂ → ℝ, ∫ p : ℂ × ℂ, (Complex.normSq (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g p.1) * Complex.normSq (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g p.2)) * f (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g p.1, GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g p.2) = ∫ q : ℂ × ℂ, f q :=
  fun _ hg f => GlobalTheory.CompanionTheory.Ar.PB.FibPt.CovSq.integral_mob_sq hg f
end

open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mobius_change_of_variables_pair : ∀ (g : Matrix (Fin 2) (Fin 2) ℂ), IsUnit g.det → ∀ f : ℂ × ℂ → ℝ, ∫ p : ℂ × ℂ, (Complex.normSq (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g p.1) * Complex.normSq (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD g p.2)) * f (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g p.1, GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob g p.2) = ∫ q : ℂ × ℂ, f q := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.FibPt.integral_mob_sq_main
end

section
section
open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.FibPt

theorem analyticAt_entry_tail {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (z : Fin (d + 1) → ℂ) (p q : Fin 2) :
    AnalyticAt ℂ (fun z' : Fin (d + 1) → ℂ => g (Fin.tail z') p q) z := by
  have hT : AnalyticAt ℂ (fun z' : Fin (d + 1) → ℂ => (Fin.tail z' : Fin d → ℂ)) z := by
    rw [analyticAt_pi_iff]
    intro i
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) i.succ).analyticAt z
  have hA : AnalyticAt ℂ (fun y' => g y' p q) (Fin.tail z) :=
    ReciprocityTheory.AnForm.Osgood.osgood d Set.univ _ isOpen_univ (hg p q).differentiableOn _ (Set.mem_univ _)
  exact hA.comp hT

theorem analyticAt_mobius_first {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (z : Fin (d + 1) → ℂ)
    (h : den (g (Fin.tail z)) (z 0) ≠ 0) : AnalyticAt ℂ (mob1 g) z := by
  have hc0 : AnalyticAt ℂ (fun z' : Fin (d + 1) → ℂ => z' 0) z :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) 0).analyticAt z
  have e := analyticAt_entry_tail g hg z
  have hnum : AnalyticAt ℂ (fun z' : Fin (d + 1) → ℂ =>
      g (Fin.tail z') 1 0 + g (Fin.tail z') 1 1 * z' 0) z := (e 1 0).add ((e 1 1).mul hc0)
  have hden : AnalyticAt ℂ (fun z' : Fin (d + 1) → ℂ => den (g (Fin.tail z')) (z' 0)) z :=
    (e 0 0).add ((e 0 1).mul hc0)
  rw [analyticAt_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hnum.div hden h
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) j.succ).analyticAt z

theorem hasDerivAt_mob_shift (m : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) (h : den m a ≠ 0) :
    HasDerivAt (fun t : ℂ => mob m (a + t)) (mobD m a) 0 := by
  have hl : HasDerivAt (fun t : ℂ => a + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_add a
  have hn : HasDerivAt (fun t : ℂ => m 1 0 + m 1 1 * (a + t)) (m 1 1 * 1) 0 :=
    (hl.const_mul (m 1 1)).const_add (m 1 0)
  have hd : HasDerivAt (fun t : ℂ => den m (a + t)) (m 0 1 * 1) 0 :=
    (hl.const_mul (m 0 1)).const_add (m 0 0)
  have h0 : den m (a + 0) ≠ 0 := by simpa using h
  have hq := hn.div hd h0
  have e1 : (m 1 1 * 1 * den m (a + 0) - (m 1 0 + m 1 1 * (a + 0)) * (m 0 1 * 1)) / den m (a + 0) ^ 2 =
      mobD m a := by
    simp only [add_zero, mobD, Matrix.det_fin_two]
    congr 1
    simp only [den]
    ring
  rw [e1] at hq
  exact hq

theorem det_jacobian_mobius_first {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (y : Fin d → ℂ) (a : ℂ)
    (h : den (g y) a ≠ 0) :
    (ReciprocityTheory.AnForm.A.jacC (mob1 g) (Fin.cons a y : Fin (d + 1) → ℂ)).det = mobD (g y) a := by
  set z : Fin (d + 1) → ℂ := Fin.cons a y with hz
  have htail : (Fin.tail z : Fin d → ℂ) = y := Fin.tail_cons _ _
  have hz0 : z 0 = a := Fin.cons_zero _ _
  have hF : HasFDerivAt (mob1 g) (fderiv ℂ (mob1 g) z) z :=
    (analyticAt_mobius_first g hg z (by rwa [htail, hz0])).differentiableAt.hasFDerivAt

  have hrow : ∀ (i : Fin d) (v : Fin (d + 1) → ℂ), fderiv ℂ (mob1 g) z v i.succ = v i.succ := by
    intro i v
    have h1 := (hasFDerivAt_pi'.1 hF) i.succ
    have h2 : HasFDerivAt (fun z' : Fin (d + 1) → ℂ => mob1 g z' i.succ)
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) i.succ) z :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) i.succ).hasFDerivAt
    exact DFunLike.congr_fun (h1.unique h2) v

  have hcorner : fderiv ℂ (mob1 g) z (Pi.single 0 1) 0 = mobD (g y) a := by
    have hc : HasDerivAt (fun t : ℂ => z + t • (Pi.single 0 1 : Fin (d + 1) → ℂ))
        (Pi.single 0 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (Pi.single 0 1 : Fin (d + 1) → ℂ)).const_add z
    have hF' : HasFDerivAt (mob1 g) (fderiv ℂ (mob1 g) z)
        (z + (0 : ℂ) • (Pi.single 0 1 : Fin (d + 1) → ℂ)) := by simpa using hF
    have hcomp := hF'.comp_hasDerivAt (0 : ℂ) hc
    have h0 := (hasDerivAt_pi.1 hcomp) 0
    have hline : ∀ t : ℂ, (mob1 g ∘ fun t : ℂ => z + t • (Pi.single 0 1 : Fin (d + 1) → ℂ)) t 0 =
        mob (g y) (a + t) := by
      intro t
      have ht : (Fin.tail (z + t • (Pi.single 0 1 : Fin (d + 1) → ℂ)) : Fin d → ℂ) = y := by
        rw [← htail]
        funext i
        simp [Fin.tail, Pi.single_apply, Fin.succ_ne_zero]
      simp only [Function.comp, mob1, Fin.cons_zero, ht]
      simp [hz0]
    have h3 : HasDerivAt (fun t : ℂ => (mob1 g ∘ fun t : ℂ => z + t • (Pi.single 0 1 : Fin (d + 1) → ℂ)) t 0)
        (mobD (g y) a) 0 := by
      simpa only [hline] using hasDerivAt_mob_shift (g y) a h
    exact h0.unique h3
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hz1 : ∀ i : Fin d, ReciprocityTheory.AnForm.A.jacC (mob1 g) z i.succ 0 = 0 := by
    intro i
    simp [ReciprocityTheory.AnForm.A.jacC, hrow, Pi.single_apply, Fin.succ_ne_zero]
  have hminor : (ReciprocityTheory.AnForm.A.jacC (mob1 g) z).submatrix (Fin.succAbove 0) Fin.succ = 1 := by
    ext i j
    simp [ReciprocityTheory.AnForm.A.jacC, hrow, Pi.single_apply, Matrix.one_apply, Fin.succ_inj]
  simp only [hz1, hminor]
  simp [ReciprocityTheory.AnForm.A.jacC, hcorner]

theorem analyticAt_mobius_and_det_jacobian : ∀ (d : ℕ) (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ p q, Differentiable ℂ fun y' => g y' p q) → ∀ (y : Fin d → ℂ) (a : ℂ),
    GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a ≠ 0 →
    AnalyticAt ℂ (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob1 g) (Fin.cons a y) ∧
      (ReciprocityTheory.AnForm.A.jacC (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob1 g) (Fin.cons a y)).det =
        GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a := by
  intro d g hg y a h
  refine ⟨analyticAt_mobius_first g hg _ ?_, det_jacobian_mobius_first g hg y a h⟩
  rwa [Fin.tail_cons, Fin.cons_zero]

end GlobalTheory.CompanionTheory.Ar.PB.FibPt
end

open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticAt_mobius_det_jacobian_eq : ∀ (d : ℕ) (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ), (∀ p q, Differentiable ℂ fun y' => g y' p q) → ∀ (y : Fin d → ℂ) (a : ℂ), GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a ≠ 0 → AnalyticAt ℂ (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob1 g) (Fin.cons a y) ∧ (ReciprocityTheory.AnForm.A.jacC (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob1 g) (Fin.cons a y)).det = GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.FibPt.analyticAt_mobius_and_det_jacobian
end

section
section
open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FibPt

theorem det_eq_mul_minor_of_col_zero {n : ℕ} (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (h : ∀ i : Fin n, J i.succ 0 = 0) : J.det = J 0 0 * (J.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h]

theorem hasDerivAt_mob_line (G : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) (h : den G a ≠ 0) :
    HasDerivAt (fun t : ℂ => mob G (a + t)) (mobD G a) 0 := by
  have hl : HasDerivAt (fun t : ℂ => a + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_add a
  have hn : HasDerivAt (fun t : ℂ => G 1 0 + G 1 1 * (a + t)) (G 1 1) 0 := by
    simpa using (hl.const_mul (G 1 1)).const_add (G 1 0)
  have hd : HasDerivAt (fun t : ℂ => den G (a + t)) (G 0 1) 0 := by
    simpa [den] using (hl.const_mul (G 0 1)).const_add (G 0 0)
  have h0 : den G (a + 0) ≠ 0 := by simpa using h
  have key := hn.div hd h0
  have e : mobD G a = (G 1 1 * den G (a + 0) - (G 1 0 + G 1 1 * (a + 0)) * G 0 1) / den G (a + 0) ^ 2 := by
    simp only [add_zero]
    unfold mobD
    rw [Matrix.det_fin_two]
    congr 1
    unfold den
    ring
  rw [e]
  exact key

theorem jacC_apply_of_line {D E : ℕ} (F : (Fin D → ℂ) → Fin E → ℂ) (z : Fin D → ℂ)
    (hF : DifferentiableAt ℂ F z) (a : Fin E) (k : Fin D) (c : ℂ)
    (h : HasDerivAt (fun t : ℂ => F (z + t • (Pi.single k 1 : Fin D → ℂ)) a) c 0) :
    ReciprocityTheory.AnForm.A.jacC F z a k = c := by
  have hl : HasDerivAt (fun t : ℂ => z + t • (Pi.single k 1 : Fin D → ℂ)) (Pi.single k 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (Pi.single k 1 : Fin D → ℂ)).const_add z
  have hF' : HasFDerivAt F (fderiv ℂ F z) (z + (0 : ℂ) • (Pi.single k 1 : Fin D → ℂ)) := by
    simpa using hF.hasFDerivAt
  have h2 := hF'.comp_hasDerivAt (0 : ℂ) hl
  have h3 := (hasDerivAt_pi.1 h2) a
  exact h3.unique h

theorem mobius_pair_line_first_axis {d : ℕ} (y : Fin d → ℂ) (a₀ a₁ t : ℂ) :
    (Fin.cons a₀ (Fin.cons a₁ y) : Fin (d + 2) → ℂ) + t • (Pi.single 0 1 : Fin (d + 2) → ℂ) =
      Fin.cons (a₀ + t) (Fin.cons a₁ y) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [Pi.single_apply, Fin.succ_ne_zero]

theorem mobius_pair_line_second_axis {d : ℕ} (y : Fin d → ℂ) (a₀ a₁ t : ℂ) :
    (Fin.cons a₀ (Fin.cons a₁ y) : Fin (d + 2) → ℂ) + t • (Pi.single 1 1 : Fin (d + 2) → ℂ) =
      Fin.cons a₀ (Fin.cons (a₁ + t) y) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Pi.single_apply]
  · refine Fin.cases ?_ (fun l => ?_) j
    · simp [Pi.single_apply]
    · have : (l.succ.succ : Fin (d + 2)) ≠ 1 := by
        intro h
        have := congrArg Fin.val h
        simp at this
      simp [Pi.single_apply, this]

theorem mobius_pair_cons {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (y : Fin d → ℂ) (b₀ b₁ : ℂ) :
    mob2 g (Fin.cons b₀ (Fin.cons b₁ y)) = Fin.cons (mob (g y) b₀) (Fin.cons (mob (g y) b₁) y) := rfl

theorem analyticAt_mobius_pair {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (y : Fin d → ℂ) (a₀ a₁ : ℂ)
    (h₀ : den (g y) a₀ ≠ 0) (h₁ : den (g y) a₁ ≠ 0) :
    AnalyticAt ℂ (mob2 g) (Fin.cons a₀ (Fin.cons a₁ y)) := by
  set z₀ : Fin (d + 2) → ℂ := Fin.cons a₀ (Fin.cons a₁ y) with hz₀
  have hcoord : ∀ i : Fin (d + 2), AnalyticAt ℂ (fun z : Fin (d + 2) → ℂ => z i) z₀ := fun i =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 2) => ℂ) i).analyticAt z₀
  have hT : AnalyticAt ℂ (fun z : Fin (d + 2) → ℂ => Fin.tail (Fin.tail z)) z₀ := by
    rw [analyticAt_pi_iff]
    intro i
    exact hcoord i.succ.succ
  have hTz : Fin.tail (Fin.tail z₀) = y := by
    simp [hz₀]
  have hga : ∀ p q, AnalyticAt ℂ (fun z : Fin (d + 2) → ℂ => g (Fin.tail (Fin.tail z)) p q) z₀ := by
    intro p q
    have h1 : AnalyticAt ℂ (fun y' => g y' p q) (Fin.tail (Fin.tail z₀)) :=
      ReciprocityTheory.AnForm.Osgood.osgood d Set.univ _ isOpen_univ (hg p q).differentiableOn _ (Set.mem_univ _)
    exact AnalyticAt.comp (f := fun z : Fin (d + 2) → ℂ => Fin.tail (Fin.tail z)) h1 hT
  have hm : ∀ i : Fin (d + 2), den (g y) (z₀ i) ≠ 0 →
      AnalyticAt ℂ (fun z : Fin (d + 2) → ℂ => mob (g (Fin.tail (Fin.tail z))) (z i)) z₀ := by
    intro i hi
    unfold mob den
    refine AnalyticAt.div ?_ ?_ ?_
    · exact (hga 1 0).add ((hga 1 1).mul (hcoord i))
    · exact (hga 0 0).add ((hga 0 1).mul (hcoord i))
    · rw [hTz]
      exact hi
  rw [analyticAt_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hm 0 (by simpa [hz₀] using h₀)
  · refine Fin.cases ?_ (fun l => ?_) j
    · exact hm 1 (by simpa [hz₀] using h₁)
    · exact hcoord l.succ.succ

theorem det_jacobian_mobius_pair {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (y : Fin d → ℂ) (a₀ a₁ : ℂ)
    (h₀ : den (g y) a₀ ≠ 0) (h₁ : den (g y) a₁ ≠ 0) :
    (ReciprocityTheory.AnForm.A.jacC (mob2 g) (Fin.cons a₀ (Fin.cons a₁ y))).det =
      mobD (g y) a₀ * mobD (g y) a₁ := by
  have hdiff : DifferentiableAt ℂ (mob2 g) (Fin.cons a₀ (Fin.cons a₁ y)) :=
    (analyticAt_mobius_pair g hg y a₀ a₁ h₀ h₁).differentiableAt
  set J := ReciprocityTheory.AnForm.A.jacC (mob2 g) (Fin.cons a₀ (Fin.cons a₁ y)) with hJ
  have hJ00 : J 0 0 = mobD (g y) a₀ := by
    refine jacC_apply_of_line _ _ hdiff 0 0 _ ?_
    simp only [mobius_pair_line_first_axis, mobius_pair_cons]
    simpa using hasDerivAt_mob_line (g y) a₀ h₀
  have hJ11 : J 1 1 = mobD (g y) a₁ := by
    refine jacC_apply_of_line _ _ hdiff 1 1 _ ?_
    simp only [mobius_pair_line_second_axis, mobius_pair_cons]
    simpa using hasDerivAt_mob_line (g y) a₁ h₁
  have hJ10 : J 1 0 = 0 := by
    refine jacC_apply_of_line _ _ hdiff 1 0 _ ?_
    simp only [mobius_pair_line_first_axis, mobius_pair_cons]
    simpa using hasDerivAt_const (0 : ℂ) (mob (g y) a₁)
  have hJss : ∀ (i : Fin d) (k : Fin (d + 2)), J i.succ.succ k = (Pi.single k 1 : Fin (d + 2) → ℂ) i.succ.succ := by
    intro i k
    refine jacC_apply_of_line _ _ hdiff _ _ _ ?_
    have e : (fun t : ℂ => mob2 g ((Fin.cons a₀ (Fin.cons a₁ y) : Fin (d + 2) → ℂ) +
        t • (Pi.single k 1 : Fin (d + 2) → ℂ)) i.succ.succ) =
        fun t : ℂ => y i + t * (Pi.single k 1 : Fin (d + 2) → ℂ) i.succ.succ := by
      funext t
      simp [mob2, Fin.tail]
    rw [e]
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const ((Pi.single k 1 : Fin (d + 2) → ℂ) i.succ.succ)).const_add (y i)
  have hc0 : ∀ i : Fin (d + 1), J i.succ 0 = 0 := by
    intro i
    refine Fin.cases ?_ (fun l => ?_) i
    · exact hJ10
    · rw [hJss]
      simp [Pi.single_apply, Fin.succ_ne_zero]
  have hc1 : ∀ i : Fin d, (J.submatrix Fin.succ Fin.succ) i.succ 0 = 0 := by
    intro i
    simp only [Matrix.submatrix_apply]
    rw [hJss]
    have : (i.succ.succ : Fin (d + 2)) ≠ 1 := by
      intro h
      have := congrArg Fin.val h
      simp at this
    simp [Pi.single_apply, this]
  have hlast : ((J.submatrix Fin.succ Fin.succ).submatrix Fin.succ Fin.succ) = 1 := by
    ext i j
    simp only [Matrix.submatrix_apply]
    rw [hJss]
    simp [Pi.single_apply, Matrix.one_apply]
  rw [det_eq_mul_minor_of_col_zero J hc0, det_eq_mul_minor_of_col_zero _ hc1, hlast, Matrix.det_one, mul_one,
    hJ00]
  simp only [Matrix.submatrix_apply]
  congr 1

theorem mobius_pair_analyticAt_and_det_jacobian : ∀ (d : ℕ) (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ p q, Differentiable ℂ fun y' => g y' p q) → ∀ (y : Fin d → ℂ) (a₀ a₁ : ℂ),
    GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a₀ ≠ 0 → GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a₁ ≠ 0 →
    AnalyticAt ℂ (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob2 g) (Fin.cons a₀ (Fin.cons a₁ y)) ∧
    (ReciprocityTheory.AnForm.A.jacC (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob2 g) (Fin.cons a₀ (Fin.cons a₁ y))).det =
      GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a₀ * GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a₁ :=
  fun _ g hg y a₀ a₁ h₀ h₁ => ⟨analyticAt_mobius_pair g hg y a₀ a₁ h₀ h₁, det_jacobian_mobius_pair g hg y a₀ a₁ h₀ h₁⟩

end GlobalTheory.CompanionTheory.Ar.PB.FibPt
end
end

open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mobius_pair_analytic_det_jacobian_eq : ∀ (d : ℕ) (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ), (∀ p q, Differentiable ℂ fun y' => g y' p q) → ∀ (y : Fin d → ℂ) (a₀ a₁ : ℂ), GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a₀ ≠ 0 → GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a₁ ≠ 0 → AnalyticAt ℂ (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob2 g) (Fin.cons a₀ (Fin.cons a₁ y)) ∧ (ReciprocityTheory.AnForm.A.jacC (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob2 g) (Fin.cons a₀ (Fin.cons a₁ y))).det = GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a₀ * GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a₁ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobius_pair_analyticAt_and_det_jacobian
end

section
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FibPt

theorem analyticAt_entry {D d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) {T : (Fin D → ℂ) → (Fin d → ℂ)} {z₀ : Fin D → ℂ}
    (hT : AnalyticAt ℂ T z₀) (p q : Fin 2) : AnalyticAt ℂ (fun z => g (T z) p q) z₀ :=
  AnalyticAt.comp' (ReciprocityTheory.AnForm.Osgood.osgood d Set.univ _ isOpen_univ (hg p q).differentiableOn (T z₀) (Set.mem_univ _)) hT

theorem analyticAt_coord {D : ℕ} (i : Fin D) (z₀ : Fin D → ℂ) : AnalyticAt ℂ (fun z : Fin D → ℂ => z i) z₀ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin D => ℂ) i).analyticAt z₀

theorem analyticAt_den {D d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) {T : (Fin D → ℂ) → (Fin d → ℂ)} {z₀ : Fin D → ℂ}
    (hT : AnalyticAt ℂ T z₀) (i : Fin D) : AnalyticAt ℂ (fun z => den (g (T z)) (z i)) z₀ :=
  (analyticAt_entry g hg hT 0 0).add ((analyticAt_entry g hg hT 0 1).mul (analyticAt_coord i z₀))

theorem analyticAt_det {D d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) {T : (Fin D → ℂ) → (Fin d → ℂ)} {z₀ : Fin D → ℂ}
    (hT : AnalyticAt ℂ T z₀) : AnalyticAt ℂ (fun z => (g (T z)).det) z₀ := by
  simp only [Matrix.det_fin_two]
  exact ((analyticAt_entry g hg hT 0 0).mul (analyticAt_entry g hg hT 1 1)).sub
    ((analyticAt_entry g hg hT 0 1).mul (analyticAt_entry g hg hT 1 0))

theorem analyticAt_mob {D d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) {T : (Fin D → ℂ) → (Fin d → ℂ)} {z₀ : Fin D → ℂ}
    (hT : AnalyticAt ℂ T z₀) (i : Fin D) (hd : den (g (T z₀)) (z₀ i) ≠ 0) :
    AnalyticAt ℂ (fun z => mob (g (T z)) (z i)) z₀ :=
  ((analyticAt_entry g hg hT 1 0).add ((analyticAt_entry g hg hT 1 1).mul (analyticAt_coord i z₀))).div
    (analyticAt_den g hg hT i) hd

theorem analyticAt_mobD {D d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) {T : (Fin D → ℂ) → (Fin d → ℂ)} {z₀ : Fin D → ℂ}
    (hT : AnalyticAt ℂ T z₀) (i : Fin D) (hd : den (g (T z₀)) (z₀ i) ≠ 0) :
    AnalyticAt ℂ (fun z => mobD (g (T z)) (z i)) z₀ :=
  (analyticAt_det g hg hT).div ((analyticAt_den g hg hT i).pow 2) (pow_ne_zero 2 hd)

theorem xiPot_frame (G g : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.PosDef) (hg : IsUnit g.det) (a : ℂ) (hd : den g a ≠ 0) :
    xiPot (gᴴ * G * g) a = xiPot G (mob g a) + Real.log ‖mobD g a‖ := by
  have h := (GlobalTheory.T.log_sine_mobius_transform G g hG hg).2.1 a hd
  have hn : ‖g.det‖ ≠ 0 := norm_ne_zero_iff.2 hg.ne_zero
  have hn2 : ‖den g a‖ ≠ 0 := norm_ne_zero_iff.2 hd
  have e : Real.log ‖mobD g a‖ = Real.log ‖g.det‖ - 2 * Real.log ‖den g a‖ := by
    rw [mobD, norm_div, norm_pow, Real.log_div hn (pow_ne_zero 2 hn2), Real.log_pow]
    norm_num
  rw [h, e]
  simp only [mob, den]
  ring

theorem hess_xi {D d : ℕ} (G g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) {T : (Fin D → ℂ) → (Fin d → ℂ)}
    {z₀ : Fin D → ℂ} (hT : AnalyticAt ℂ T z₀) (i : Fin D) (hG : ∀ᶠ y' in 𝓝 (T z₀), (G y').PosDef)
    (hC : ∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) (T z₀)) (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q)
    (hu : IsUnit (g (T z₀)).det) (hd : den (g (T z₀)) (z₀ i) ≠ 0) :
    ContDiffAt ℝ 2 (fun z => xiPot ((g (T z))ᴴ * G (T z) * g (T z)) (z i)) z₀ ∧
    ContDiffAt ℝ 2 (fun z => xiPot (G (T z)) (mob (g (T z)) (z i))) z₀ ∧
    hessC (fun z => xiPot ((g (T z))ᴴ * G (T z) * g (T z)) (z i)) z₀ =
      hessC (fun z => xiPot (G (T z)) (mob (g (T z)) (z i))) z₀ := by
  have hT2 : ContDiffAt ℝ 2 T z₀ := (hT.contDiffAt (n := 2)).restrict_scalars ℝ
  have hco : ContDiffAt ℝ 2 (fun z : Fin D → ℂ => z i) z₀ := ((analyticAt_coord i z₀).contDiffAt (n := 2)).restrict_scalars ℝ
  have hm2 : ContDiffAt ℝ 2 (fun z => mob (g (T z)) (z i)) z₀ :=
    ((analyticAt_mob g hg hT i hd).contDiffAt (n := 2)).restrict_scalars ℝ
  have hpd0 : (G (T z₀)).PosDef := hG.self_of_nhds
  have hCT : ∀ p q, ContDiffAt ℝ 2 (fun z => G (T z) p q) z₀ := fun p q => (hC p q).comp z₀ hT2
  have h2 : ContDiffAt ℝ 2 (fun z => xiPot (G (T z)) (mob (g (T z)) (z i))) z₀ :=
    contDiffAt_xiPot (fun z => G (T z)) _ z₀ hpd0 hCT hm2
  have h1 : ContDiffAt ℝ 2 (fun z => xiPot ((g (T z))ᴴ * G (T z) * g (T z)) (z i)) z₀ := by
    refine contDiffAt_xiPot (fun z => (g (T z))ᴴ * G (T z) * g (T z)) _ z₀ (GlobalTheory.T.log_sine_mobius_transform _ _ hpd0 hu).1 ?_ hco
    intro p q
    exact (contDiffAt_frame_entry G g (T z₀) hC hg p q).comp z₀ hT2
  refine ⟨h1, h2, ?_⟩
  have hmd : mobD (g (T z₀)) (z₀ i) ≠ 0 := div_ne_zero hu.ne_zero (pow_ne_zero 2 hd)
  rw [← ReciprocityTheory.AnForm.A.hessC_add_log_norm _ _ z₀ h2 (analyticAt_mobD g hg hT i hd) hmd]
  apply ReciprocityTheory.AnForm.A.hessC_congr'
  have e1 : ∀ᶠ z in 𝓝 z₀, (G (T z)).PosDef := hT.continuousAt.eventually hG
  have e2 : ∀ᶠ z in 𝓝 z₀, (g (T z)).det ≠ 0 := (analyticAt_det g hg hT).continuousAt.eventually_ne hu.ne_zero
  have e3 : ∀ᶠ z in 𝓝 z₀, den (g (T z)) (z i) ≠ 0 := (analyticAt_den g hg hT i).continuousAt.eventually_ne hd
  filter_upwards [e1, e2, e3] with z h1 h2 h3
  exact xiPot_frame _ _ h1 (isUnit_iff_ne_zero.2 h2) _ h3

theorem maDens_congr_hess {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : ∀ r, hessC (φ r) z = hessC (ψ r) z) : maDens φ z = maDens ψ z := by
  simp only [maDens, h]

theorem analyticAt_tail {d : ℕ} (z₀ : Fin (d + 1) → ℂ) : AnalyticAt ℂ (fun z : Fin (d + 1) → ℂ => Fin.tail z) z₀ :=
  (ContinuousLinearMap.pi (R := ℂ) fun i : Fin d =>
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) i.succ).analyticAt z₀

theorem analyticAt_tail2 {d : ℕ} (z₀ : Fin (d + 2) → ℂ) :
    AnalyticAt ℂ (fun z : Fin (d + 2) → ℂ => Fin.tail (Fin.tail z)) z₀ :=
  AnalyticAt.comp' (analyticAt_tail (Fin.tail z₀)) (analyticAt_tail z₀)

end GlobalTheory.CompanionTheory.Ar.PB.FibPt

namespace GlobalTheory.CompanionTheory.Ar.PB.FibPt

theorem contDiffAt_xi_coord {D d : ℕ} (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) {T : (Fin D → ℂ) → (Fin d → ℂ)}
    {z₀ : Fin D → ℂ} (hT : AnalyticAt ℂ T z₀) (i : Fin D) (hpd : (G (T z₀)).PosDef)
    (hC : ∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) (T z₀)) :
    ContDiffAt ℝ 2 (fun z => xiPot (G (T z)) (z i)) z₀ := by
  have hT2 : ContDiffAt ℝ 2 T z₀ := (hT.contDiffAt (n := 2)).restrict_scalars ℝ
  exact contDiffAt_xiPot (fun z => G (T z)) _ z₀ hpd (fun p q => (hC p q).comp z₀ hT2)
    (((analyticAt_coord i z₀).contDiffAt (n := 2)).restrict_scalars ℝ)

theorem contDiffAt_base {D d : ℕ} (α : (Fin d → ℂ) → ℝ) {T : (Fin D → ℂ) → (Fin d → ℂ)}
    {z₀ : Fin D → ℂ} (hT : AnalyticAt ℂ T z₀) (hα : ContDiffAt ℝ 2 α (T z₀)) :
    ContDiffAt ℝ 2 (fun z => α (T z)) z₀ :=
  hα.comp z₀ ((hT.contDiffAt (n := 2)).restrict_scalars ℝ)

theorem hess_lin {D : ℕ} {f₀ f₁ h₀ h₁ : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (c₀ c₁ : ℝ)
    (hf₀ : ContDiffAt ℝ 2 f₀ z) (hf₁ : ContDiffAt ℝ 2 f₁ z) (hh₀ : ContDiffAt ℝ 2 h₀ z) (hh₁ : ContDiffAt ℝ 2 h₁ z)
    (e₀ : hessC f₀ z = hessC h₀ z) (e₁ : hessC f₁ z = hessC h₁ z) :
    hessC (fun w => c₀ * f₀ w + c₁ * f₁ w) z = hessC (fun w => c₀ * h₀ w + c₁ * h₁ w) z := by
  rw [ReciprocityTheory.AnForm.A.hessC_add _ _ z (contDiffAt_const.mul hf₀) (contDiffAt_const.mul hf₁),
    ReciprocityTheory.AnForm.A.hessC_add _ _ z (contDiffAt_const.mul hh₀) (contDiffAt_const.mul hh₁),
    ReciprocityTheory.AnForm.M.hessC_const_mul', ReciprocityTheory.AnForm.M.hessC_const_mul',
    ReciprocityTheory.AnForm.M.hessC_const_mul', ReciprocityTheory.AnForm.M.hessC_const_mul', e₀, e₁]

theorem dens1 : ∀ (d m : ℕ) (G g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) → (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) → ContDiffAt ℝ 2 α y → (∀ p q, Differentiable ℂ fun y' => g y' p q) → IsUnit (g y).det → ∀ a : ℂ, GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a ≠ 0 → maDens (fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < m then xiPot ((g (Fin.tail z))ᴴ * G (Fin.tail z) * g (Fin.tail z)) (z 0) else α (Fin.tail z)) (Fin.cons a y) = Complex.normSq (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a) * maDens (fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < m then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)) (Fin.cons (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob (g y) a) y) := by
  intro d m G g α y hG hC hα hg hu a ha
  obtain ⟨han, hjac⟩ := GlobalTheory.T.analyticAt_mobius_det_jacobian_eq d g hg y a ha
  have hτ : mob1 g (Fin.cons a y) = Fin.cons (mob (g y) a) y := by simp [mob1]
  let T : (Fin (d + 1) → ℂ) → (Fin d → ℂ) := fun z => Fin.tail z
  have hTa : ∀ z₀, AnalyticAt ℂ T z₀ := fun z₀ => analyticAt_tail z₀
  have hTc : ∀ b : ℂ, T (Fin.cons b y) = y := fun b => by simp [T]
  let φ : Fin (d + 1) → (Fin (d + 1) → ℂ) → ℝ :=
    fun r z => if (r : ℕ) < m then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)
  have hφ : ∀ r, ContDiffAt ℝ 2 (φ r) (mob1 g (Fin.cons a y)) := by
    intro r
    rw [hτ]
    by_cases h : (r : ℕ) < m
    · simp only [φ, h, if_true]
      exact contDiffAt_xi_coord G (hTa _) 0 (by rw [hTc]; exact hG.self_of_nhds) (by rw [hTc]; exact hC)
    · simp only [φ, h, if_false]
      exact contDiffAt_base α (T := T) (hTa _) (by rw [hTc]; exact hα)
  have step := ReciprocityTheory.AnForm.A.maDens_comp φ (mob1 g) _ han hφ
  rw [hjac, hτ] at step
  rw [mul_comm, ← step]
  apply maDens_congr_hess
  intro r
  by_cases h : (r : ℕ) < m
  · have e : φ r ∘ mob1 g = fun z => xiPot (G (T z)) (mob (g (T z)) (z 0)) := by
      funext z
      simp [φ, h, mob1, T]
    rw [e]
    simp only [h, if_true]
    exact (hess_xi G g (hTa _) 0 (by rw [hTc]; exact hG) (by rw [hTc]; exact hC) hg (by rw [hTc]; exact hu)
      (by simpa [hTc] using ha)).2.2
  · have e : φ r ∘ mob1 g = fun z => α (Fin.tail z) := by
      funext z
      simp [φ, h, mob1]
    rw [e]
    simp only [h, if_false]

theorem dens2 : ∀ (d m : ℕ) (u : ℕ → Fin 2 → ℝ) (G g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) → (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) → ContDiffAt ℝ 2 α y → (∀ p q, Differentiable ℂ fun y' => g y' p q) → IsUnit (g y).det → ∀ a₀ a₁ : ℂ, GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a₀ ≠ 0 → GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a₁ ≠ 0 → maDens (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < m then u r 0 * xiPot ((g (Fin.tail (Fin.tail z)))ᴴ * G (Fin.tail (Fin.tail z)) * g (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot ((g (Fin.tail (Fin.tail z)))ᴴ * G (Fin.tail (Fin.tail z)) * g (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z))) (Fin.cons a₀ (Fin.cons a₁ y)) = (Complex.normSq (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a₀) * Complex.normSq (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a₁)) * maDens (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < m then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z))) (Fin.cons (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob (g y) a₀) (Fin.cons (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob (g y) a₁) y)) := by
  intro d m u G g α y hG hC hα hg hu a₀ a₁ h₀ h₁
  obtain ⟨han, hjac⟩ := GlobalTheory.T.mobius_pair_analytic_det_jacobian_eq d g hg y a₀ a₁ h₀ h₁
  have c0 : ∀ b₀ b₁ : ℂ, (Fin.cons b₀ (Fin.cons b₁ y) : Fin (d + 2) → ℂ) 0 = b₀ := fun _ _ => rfl
  have c1 : ∀ b₀ b₁ : ℂ, (Fin.cons b₀ (Fin.cons b₁ y) : Fin (d + 2) → ℂ) 1 = b₁ := fun _ _ => rfl
  let T : (Fin (d + 2) → ℂ) → (Fin d → ℂ) := fun z => Fin.tail (Fin.tail z)
  have hTa : ∀ z₀, AnalyticAt ℂ T z₀ := fun z₀ => analyticAt_tail2 z₀
  have hTc : ∀ b₀ b₁ : ℂ, T (Fin.cons b₀ (Fin.cons b₁ y)) = y := fun b₀ b₁ => by simp [T]
  have hτ : mob2 g (Fin.cons a₀ (Fin.cons a₁ y)) = Fin.cons (mob (g y) a₀) (Fin.cons (mob (g y) a₁) y) := by
    have ht : Fin.tail (Fin.tail (Fin.cons a₀ (Fin.cons a₁ y) : Fin (d + 2) → ℂ)) = y := hTc a₀ a₁
    simp only [mob2, ht, c0, c1]
  let φ : Fin (d + 2) → (Fin (d + 2) → ℂ) → ℝ :=
    fun r z => if (r : ℕ) < m then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) +
      u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z))
  have hφ : ∀ r, ContDiffAt ℝ 2 (φ r) (mob2 g (Fin.cons a₀ (Fin.cons a₁ y))) := by
    intro r
    rw [hτ]
    by_cases h : (r : ℕ) < m
    · simp only [φ, h, if_true]
      exact (contDiffAt_const.mul (contDiffAt_xi_coord G (hTa _) 0 (by rw [hTc]; exact hG.self_of_nhds)
        (by rw [hTc]; exact hC))).add (contDiffAt_const.mul (contDiffAt_xi_coord G (hTa _) 1
          (by rw [hTc]; exact hG.self_of_nhds) (by rw [hTc]; exact hC)))
    · simp only [φ, h, if_false]
      exact contDiffAt_base α (T := T) (hTa _) (by rw [hTc]; exact hα)
  have step := ReciprocityTheory.AnForm.A.maDens_comp φ (mob2 g) _ han hφ
  rw [hjac, hτ, Complex.normSq_mul] at step
  rw [mul_comm, ← step]
  apply maDens_congr_hess
  intro r
  by_cases h : (r : ℕ) < m
  · have e : φ r ∘ mob2 g = fun z => u r 0 * xiPot (G (T z)) (mob (g (T z)) (z 0)) +
        u r 1 * xiPot (G (T z)) (mob (g (T z)) (z 1)) := by
      funext z
      have e0 : mob2 g z 0 = mob (g (T z)) (z 0) := rfl
      have e1 : mob2 g z 1 = mob (g (T z)) (z 1) := rfl
      have e2 : Fin.tail (Fin.tail (mob2 g z)) = T z := by simp [mob2, T]
      simp only [Function.comp, φ, h, if_true, e0, e1, e2, T]
    rw [e]
    simp only [h, if_true]
    have x0 := hess_xi G g (hTa (Fin.cons a₀ (Fin.cons a₁ y))) 0 (by rw [hTc]; exact hG) (by rw [hTc]; exact hC) hg
      (by rw [hTc]; exact hu) (by rw [hTc, c0]; exact h₀)
    have x1 := hess_xi G g (hTa (Fin.cons a₀ (Fin.cons a₁ y))) 1 (by rw [hTc]; exact hG) (by rw [hTc]; exact hC) hg
      (by rw [hTc]; exact hu) (by rw [hTc, c1]; exact h₁)
    exact hess_lin _ _ x0.1 x1.1 x0.2.1 x1.2.1 x0.2.2 x1.2.2
  · have e : φ r ∘ mob2 g = fun z => α (Fin.tail (Fin.tail z)) := by
      funext z
      have e2 : Fin.tail (Fin.tail (mob2 g z)) = Fin.tail (Fin.tail z) := by simp [mob2]
      simp only [Function.comp, φ, h, if_false, e2]
    rw [e]
    simp only [h, if_false]

end GlobalTheory.CompanionTheory.Ar.PB.FibPt

open GlobalTheory.CompanionTheory.Ar.PB.FibPt in

theorem GlobalTheory.CompanionTheory.Ar.PB.FibPt.ae_den_ne (g : Matrix (Fin 2) (Fin 2) ℂ) (hg : IsUnit g.det) : ∀ᵐ a : ℂ, den g a ≠ 0 := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0 := by
    have := hg.ne_zero
    rwa [Matrix.det_fin_two] at this
  by_cases h : g 0 1 = 0
  · refine Eventually.of_forall fun a => ?_
    have h0 : g 0 0 ≠ 0 := by
      rintro h0
      apply hdet
      simp [h, h0]
    simpa [den, h] using h0
  · have hsub : {a : ℂ | ¬ den g a ≠ 0} ⊆ {-(g 0 0) / g 0 1} := by
      intro a ha
      have ha' : den g a = 0 := by simpa using ha
      simp only [Set.mem_singleton_iff]
      unfold den at ha'
      field_simp
      linear_combination ha'
    exact measure_mono_null hsub (by simp)

open GlobalTheory.CompanionTheory.Ar.PB.FibPt in

theorem GlobalTheory.CompanionTheory.Ar.PB.FibPt.fibre_integral_any_frame : GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement → ∀ (d k : ℕ), 1 ≤ k → 2 * k ≤ d + 2 → ∀ (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) → (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) → ContDiffAt ℝ 2 α y → (∑ i ∈ Finset.range k, ∫ p : ℂ × ℂ, logSin (G y) p.1 p.2 * maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z)))) (Fin.cons p.1 (Fin.cons p.2 y))) = 2 * ReciprocityTheory.ChartRestriction.G.AI.kappa k * ∫ a : ℂ, maDens (fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)) (Fin.cons a y) := by
  intro hF d k hk hkd G α y hG hC hα
  obtain ⟨g, hgd, hgu, hpd, hc2, h1, hf0⟩ := GlobalTheory.T.local_unitary_normal_frame_2x2 d G y hG hC
  have key := GlobalTheory.T.log_sine_monge_ampere_normalized hF d k hk hkd (fun y' => (g y')ᴴ * G y' * g y') α y hpd hc2 hα h1 hf0
  have hae := ae_den_ne (g y) hgu
  have hR : ∫ a : ℂ, maDens (fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot ((g (Fin.tail z))ᴴ * G (Fin.tail z) * g (Fin.tail z)) (z 0) else α (Fin.tail z)) (Fin.cons a y) = ∫ a : ℂ, maDens (fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)) (Fin.cons a y) := by
    refine Eq.trans (integral_congr_ae (hae.mono fun a ha => ?_)) (GlobalTheory.T.integral_normSq_mobD_mul_comp_mob' (g y) hgu (fun b : ℂ => maDens (fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)) (Fin.cons b y)))
    exact dens1 d (2 * k - 1) G g α y hG hC hα hgd hgu a ha
  have hL : ∀ u : ℕ → Fin 2 → ℝ, ∫ p : ℂ × ℂ, logSin ((g y)ᴴ * G y * g y) p.1 p.2 * maDens (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot ((g (Fin.tail (Fin.tail z)))ᴴ * G (Fin.tail (Fin.tail z)) * g (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot ((g (Fin.tail (Fin.tail z)))ᴴ * G (Fin.tail (Fin.tail z)) * g (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z))) (Fin.cons p.1 (Fin.cons p.2 y)) = ∫ p : ℂ × ℂ, logSin (G y) p.1 p.2 * maDens (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z))) (Fin.cons p.1 (Fin.cons p.2 y)) := by
    intro u
    have hae2 : ∀ᵐ p : ℂ × ℂ, den (g y) p.1 ≠ 0 ∧ den (g y) p.2 ≠ 0 := by
      have h1' : ∀ᵐ p : ℂ × ℂ, den (g y) p.1 ≠ 0 :=
        (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ))).ae hae
      have h2' : ∀ᵐ p : ℂ × ℂ, den (g y) p.2 ≠ 0 :=
        (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ))).ae hae
      exact h1'.and h2'
    refine Eq.trans (integral_congr_ae (hae2.mono fun p hp => ?_)) (GlobalTheory.T.mobius_change_of_variables_pair (g y) hgu (fun p : ℂ × ℂ => logSin (G y) p.1 p.2 * maDens (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z))) (Fin.cons p.1 (Fin.cons p.2 y))))
    have hpdy : (G y).PosDef := hG.self_of_nhds
    have hs := (GlobalTheory.T.log_sine_mobius_transform (G y) (g y) hpdy hgu).2.2 p.1 p.2 hp.1 hp.2
    simp only []
    rw [hs, dens2 d (2 * k) u G g α y hG hC hα hgd hgu p.1 p.2 hp.1 hp.2]
    simp only [mob, den]
    ring
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (key.trans ?_)
  · exact (hL (fun (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c)).symm
  · exact congrArg _ hR

end
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_sine_monge_ampere_integral : GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement → ∀ (d k : ℕ), 1 ≤ k → 2 * k ≤ d + 2 → ∀ (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ), (∀ᶠ y' in 𝓝 y, (G y').PosDef) → (∀ p q, ContDiffAt ℝ 2 (fun y' => G y' p q) y) → ContDiffAt ℝ 2 α y → (∑ i ∈ Finset.range k, ∫ p : ℂ × ℂ, logSin (G y) p.1 p.2 * maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; (fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z)))) (Fin.cons p.1 (Fin.cons p.2 y))) = 2 * ReciprocityTheory.ChartRestriction.G.AI.kappa k * ∫ a : ℂ, maDens (fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)) (Fin.cons a y) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.FibPt.fibre_integral_any_frame
end

section
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.square_parametrized_density_formula : ∀ (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (a₀ : σ) (ε : σ → ℤ) (Q : AnSq SY a₀ ε) (c : σ → ℝ), c a₀ = 0 → ∀ (n k : ℕ), 1 ≤ k → 2 * k ≤ d + 2 → (∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Q.U n → paramDens (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (Q.ΦY n) z = maDens (fun (r : Fin (d + 1)) (z' : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (Q.G n (Fin.tail z')) (z' 0) else ∑ a, c a * Q.α n a (Fin.tail z')) z) ∧ ∀ i < k, ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Q.U n → paramDens (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) (Q.ΦW n) z = maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; fun (r : Fin (d + 2)) (z' : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 0) + u r 1 * xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 1) else ∑ a, c a * Q.α n a (Fin.tail (Fin.tail z'))) z := by
  intro d σ _ SY a₀ ε Q c hc n k hk _
  exact ⟨fun z hz => PositivityTheory.Xgp.sq_dens.part1 Q c hc n k z hz, fun i hi z hz => PositivityTheory.Xgp.sq_dens.part2 Q c hc n k hk i hi z hz⟩
end

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_parametrized_density_formula : ∀ (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (a₀ : σ) (ε : σ → ℤ) (Q : AnSq SY a₀ ε) (c : σ → ℝ), c a₀ = 0 → ∀ (n k : ℕ), 1 ≤ k → 2 * k ≤ d + 2 → (∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Q.U n → paramDens (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (Q.ΦY n) z = maDens (fun (r : Fin (d + 1)) (z' : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (Q.G n (Fin.tail z')) (z' 0) else ∑ a, c a * Q.α n a (Fin.tail z')) z) ∧ ∀ i < k, ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Q.U n → paramDens (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) (Q.ΦW n) z = maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; fun (r : Fin (d + 2)) (z' : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 0) + u r 1 * xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 1) else ∑ a, c a * Q.α n a (Fin.tail (Fin.tail z'))) z := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.square_parametrized_density_formula
end

section
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace SqFubini

def eY (d : ℕ) : ((Fin d → ℂ) × ℂ) ≃ᵐ (Fin (d + 1) → ℂ) :=
  MeasurableEquiv.prodComm.trans (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0).symm

theorem eY_apply {d : ℕ} (x : (Fin d → ℂ) × ℂ) : eY d x = Fin.cons x.2 x.1 := by
  first | rfl | (simp [eY, MeasurableEquiv.piFinSuccAbove, Fin.consEquiv]; done) | (simp [eY, MeasurableEquiv.piFinSuccAbove]; rfl)

theorem eY_measurePreserving (d : ℕ) : MeasurePreserving (eY d) volume volume :=
  (Measure.measurePreserving_swap).trans
    (volume_preserving_piFinSuccAbove (fun _ => ℂ) 0).symm

def eW (d : ℕ) : ((Fin d → ℂ) × (ℂ × ℂ)) ≃ᵐ (Fin (d + 2) → ℂ) :=
  (MeasurableEquiv.prodComm.trans MeasurableEquiv.prodAssoc).trans
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℂ)
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0).symm).trans
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0).symm)

theorem eW_apply {d : ℕ} (x : (Fin d → ℂ) × (ℂ × ℂ)) :
    eW d x = Fin.cons x.2.1 (Fin.cons x.2.2 x.1) := by
  first | rfl | (simp [eW, MeasurableEquiv.piFinSuccAbove, Fin.consEquiv]; done) | (simp [eW, MeasurableEquiv.piFinSuccAbove]; rfl)

theorem eW_measurePreserving (d : ℕ) : MeasurePreserving (eW d) volume volume :=
  ((Measure.measurePreserving_swap).trans (measurePreserving_prodAssoc volume volume volume)).trans
    (((MeasurePreserving.id volume).prod
      (volume_preserving_piFinSuccAbove (fun _ => ℂ) 0).symm).trans
      (volume_preserving_piFinSuccAbove (fun _ => ℂ) 0).symm)

theorem fubini_piece {Y P Z : Type*} [MeasurableSpace Y] [MeasurableSpace P] [MeasurableSpace Z]
    (μ : Measure Y) (ν : Measure P) (ρ : Measure Z) [SFinite μ] [SFinite ν]
    (e : (Y × P) ≃ᵐ Z) (he : MeasurePreserving e (μ.prod ν) ρ) (B : Set Y) (S : Set Z)
    (hS : e ⁻¹' S = B ×ˢ Set.univ) (F : Z → ℝ) (hF : IntegrableOn F S ρ) :
    IntegrableOn (fun y => ∫ p, F (e (y, p)) ∂ν) B μ ∧
      ∫ z in S, F z ∂ρ = ∫ y in B, ∫ p, F (e (y, p)) ∂ν ∂μ := by
  have h1 : IntegrableOn (F ∘ e) (B ×ˢ Set.univ) (μ.prod ν) := by
    rw [← hS]
    exact (he.integrableOn_comp_preimage e.measurableEmbedding).2 hF
  have h2 : ∫ z in S, F z ∂ρ = ∫ x in B ×ˢ Set.univ, F (e x) ∂(μ.prod ν) := by
    rw [← hS]
    exact (he.setIntegral_preimage_emb e.measurableEmbedding F S).symm
  constructor
  · have h3 : Integrable (F ∘ e) ((μ.restrict B).prod (ν.restrict Set.univ)) := by
      rw [Measure.prod_restrict]
      exact h1
    simpa [IntegrableOn, Function.comp_def] using h3.integral_prod_left
  · rw [h2]
    simpa [Function.comp_def] using setIntegral_prod (F ∘ e) h1

theorem fibre_sum {d k : ℕ} (B : Set (Fin d → ℂ)) (F : ℕ → (Fin (d + 2) → ℂ) → ℝ)
    (H : (Fin (d + 1) → ℂ) → ℝ) (κ : ℝ)
    (hF : ∀ i < k, IntegrableOn (F i) {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ B})
    (hH : IntegrableOn H {z : Fin (d + 1) → ℂ | Fin.tail z ∈ B})
    (hpt : ∀ y ∈ B, ∑ i ∈ Finset.range k, ∫ p : ℂ × ℂ, F i (Fin.cons p.1 (Fin.cons p.2 y)) =
      κ * ∫ a : ℂ, H (Fin.cons a y))
    (hB : MeasurableSet B) :
    ∑ i ∈ Finset.range k, ∫ z in {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ B}, F i z =
      κ * ∫ z in {z : Fin (d + 1) → ℂ | Fin.tail z ∈ B}, H z := by
  have hSW : (eW d) ⁻¹' {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ B} = B ×ˢ Set.univ := by
    ext x
    simp [eW_apply]
  have hSY : (eY d) ⁻¹' {z : Fin (d + 1) → ℂ | Fin.tail z ∈ B} = B ×ˢ Set.univ := by
    ext x
    simp [eY_apply]
  have hW := fun i (hi : i < k) => fubini_piece volume volume volume (eW d) (eW_measurePreserving d) B _ hSW
    (F i) (hF i hi)
  have hY := fubini_piece volume volume volume (eY d) (eY_measurePreserving d) B _ hSY H hH
  simp only [eW_apply, eY_apply] at hW hY
  rw [hY.2, Finset.sum_congr rfl fun i hi => (hW i (Finset.mem_range.1 hi)).2,
    ← integral_finset_sum _ fun i hi => (hW i (Finset.mem_range.1 hi)).1, ← integral_const_mul]
  exact setIntegral_congr_fun hB fun y hy => hpt y hy

theorem ae_ne (d : ℕ) : ∀ᵐ z : Fin (d + 2) → ℂ, z 0 ≠ z 1 := by
  let L : (Fin (d + 2) → ℂ) →ₗ[ℝ] ℂ :=
    (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 2) => ℂ) 0) -
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 2) => ℂ) 1)
  have hs : LinearMap.ker L ≠ ⊤ := by
    intro h
    have h1 : (Pi.single 0 1 : Fin (d + 2) → ℂ) ∈ LinearMap.ker L := by rw [h]; trivial
    simp [L, LinearMap.mem_ker, Pi.single_apply] at h1
  have h0 := Measure.addHaar_submodule (volume : Measure (Fin (d + 2) → ℂ)) (LinearMap.ker L) hs
  refine measure_mono_null ?_ h0
  intro z hz
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hz
  simp [L, LinearMap.mem_ker, hz]

theorem isC2At_sumPot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {σ : Type} [Fintype σ]
    (c : σ → ℝ) (P : σ → LocPot X) (x : X) (h : ∀ a, IsTwiceDifferentiableAt A (P a) x) : IsTwiceDifferentiableAt A (sumPot c P) x := by
  intro j hj
  have : (sumPot c P).φ x ∘ (A.chart j).symm =
      fun y => ∑ a, c a * ((P a).φ x ∘ (A.chart j).symm) y := rfl
  rw [this]
  exact ContDiffAt.sum fun a _ => contDiffAt_const.mul (h a j hj)

end SqFubini

namespace SqFubini

def EW {d : ℕ} (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (α : (Fin d → ℂ) → ℝ) (k i : ℕ) :
    Fin (d + 2) → (Fin (d + 2) → ℂ) → ℝ :=
  let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i
  fun (r : Fin (d + 2)) (z : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (G (Fin.tail (Fin.tail z))) (z 0) + u r 1 * xiPot (G (Fin.tail (Fin.tail z))) (z 1) else α (Fin.tail (Fin.tail z))

def EY {d : ℕ} (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (α : (Fin d → ℂ) → ℝ) (k : ℕ) :
    Fin (d + 1) → (Fin (d + 1) → ℂ) → ℝ :=
  fun (r : Fin (d + 1)) (z : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (G (Fin.tail z)) (z 0) else α (Fin.tail z)

end SqFubini

open SqFubini in

theorem AnSq.sum_polar_gH_eq : Inputs → GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement → ∀ (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (a₀ : σ) (ε : σ → ℤ) (Q : AnSq SY a₀ ε) (c : σ → ℝ), c a₀ = 0 → ∀ k : ℕ, 1 ≤ k → 2 * k ≤ d + 2 → ∑ i ∈ Finset.range k, polar (d + 2) (fun w => mInt Q.SW.A (fun r => Q.SW.potH (w r)) Q.gH) (Q.wcoef c k i) = 2 * kappa k * polar (d + 1) SY.degNum (mix (2 * k - 1) (fun a => (ε a : ℝ)) c) := by
  intro hI hF d σ _ SY a₀ ε Q c hc k hk1 hk2
  have hlim := GlobalTheory.T.analytic_square_regularized_convergence hI d σ SY a₀ ε Q
  obtain ⟨-, hnW, hC2W, -, -⟩ := anSys_open_basics (d + 2) (Option σ) Q.SW
  obtain ⟨-, hnY, hC2Y, -, -⟩ := anSys_open_basics (d + 1) σ SY
  have hhom := AnSys.mIntegrable_potH_and_mInt_eq_degNum hI.convergenceSigned (d + 1) σ SY

  have hexW := fun i => mInt_sumPot_expand (d + 2) Q.SW.X Q.SW.A (Option σ) Q.SW.open' Q.SW.potH
    (Q.wcoef c k i) Q.gH hnW hC2W fun w => (hlim w).1
  have hexY := mInt_sumPot_expand (d + 1) SY.X SY.A σ SY.open' SY.potH
    (mix (2 * k - 1) (fun a => (ε a : ℝ)) c) (fun _ => 1) hnY hC2Y fun w => (hhom w).1
  have hpolW : ∀ i, polar (d + 2) (fun w => mInt Q.SW.A (fun r => Q.SW.potH (w r)) Q.gH) (Q.wcoef c k i) =
      mInt Q.SW.A (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) Q.gH := fun i => (hexW i).2.symm
  have hpolY : polar (d + 1) SY.degNum (mix (2 * k - 1) (fun a => (ε a : ℝ)) c) =
      mInt SY.A (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (fun _ => 1) := by
    rw [hexY.2]
    exact Finset.sum_congr rfl fun w _ => by rw [(hhom w).2]

  have hoW : ∀ n (z : Fin (d + 2) → ℂ), Fin.tail (Fin.tail z) ∈ Q.U n → Q.ΦW n z ∈ Q.SW.open' := by
    intro n z hz
    rw [Q.bdry_eq 0, Set.mem_preimage, Q.first_projection_chart_compat n z hz]
    exact Q.ΦY_open n _ (by simpa using hz)

  have hcW := fun i => integrableOn_hasSum_paramCover (d + 2) Q.SW.X Q.SW.A _ _ Q.ΦW
    (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) Q.gH Q.coverW
    (fun n z hz r => isC2At_sumPot _ _ _ _ fun a => hC2W a _ (hoW n z (Q.B_meas n |>.2 hz)))
    (hexW i).1
  have hcY := integrableOn_hasSum_paramCover (d + 1) SY.X SY.A _ _ Q.ΦY
    (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (fun _ => 1) Q.coverY
    (fun n z hz r => isC2At_sumPot _ _ _ _ fun a => hC2Y a _ (Q.ΦY_open n z (Q.B_meas n |>.2 hz)))
    hexY.1

  have key : ∀ n, ∑ i ∈ Finset.range k, ∫ z in {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ Q.B n},
      Q.gH (Q.ΦW n z) * paramDens (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) (Q.ΦW n) z =
      2 * kappa k * ∫ z in {z : Fin (d + 1) → ℂ | Fin.tail z ∈ Q.B n},
        (fun _ => (1 : ℝ)) (Q.ΦY n z) * paramDens
          (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (Q.ΦY n) z := by
    intro n
    let α : (Fin d → ℂ) → ℝ := fun y => ∑ a, c a * Q.α n a y
    have hd := GlobalTheory.T.square_parametrized_density_formula d σ SY a₀ ε Q c hc n k hk1 hk2
    have hmW : MeasurableSet {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ Q.B n} := (Q.coverW.2.1 n).1
    have hmY : MeasurableSet {z : Fin (d + 1) → ℂ | Fin.tail z ∈ Q.B n} := (Q.coverY.2.1 n).1
    let F : ℕ → (Fin (d + 2) → ℂ) → ℝ := fun i z =>
      logSin (Q.G n (Fin.tail (Fin.tail z))) (z 0) (z 1) * maDens (EW (Q.G n) α k i) z
    have hae : ∀ i < k, ∀ᵐ z ∂(volume.restrict {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ Q.B n}),
        Q.gH (Q.ΦW n z) * paramDens (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) (Q.ΦW n) z = F i z := by
      intro i hi
      filter_upwards [ae_restrict_of_ae (ae_ne d), ae_restrict_mem hmW] with z hne hz
      have hU : Fin.tail (Fin.tail z) ∈ Q.U n := (Q.B_meas n).2 hz
      have h1 : Q.gH (Q.ΦW n z) = logSin (Q.G n (Fin.tail (Fin.tail z))) (z 0) (z 1) :=
        Q.norm_hom n z hU hne
      have h2 : paramDens (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) (Q.ΦW n) z =
          maDens (EW (Q.G n) α k i) z := hd.2 i hi z hU
      rw [h1, h2]
    have hH : ∀ z ∈ {z : Fin (d + 1) → ℂ | Fin.tail z ∈ Q.B n},
        (fun _ => (1 : ℝ)) (Q.ΦY n z) * paramDens
          (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (Q.ΦY n) z =
        maDens (EY (Q.G n) α k) z := by
      intro z hz
      have h2 : paramDens (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (Q.ΦY n) z =
          maDens (EY (Q.G n) α k) z := hd.1 z ((Q.B_meas n).2 hz)
      rw [h2, one_mul]
    have hFint : ∀ i < k, IntegrableOn (F i) {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ Q.B n} :=
      fun i hi => ((hcW i).1 n).congr (hae i hi)
    have hHint : IntegrableOn (maDens (EY (Q.G n) α k)) {z : Fin (d + 1) → ℂ | Fin.tail z ∈ Q.B n} :=
      (integrableOn_congr_fun hH hmY).1 (hcY.1 n)
    have hpt : ∀ y ∈ Q.B n, ∑ i ∈ Finset.range k, ∫ p : ℂ × ℂ, F i (Fin.cons p.1 (Fin.cons p.2 y)) =
        (2 * kappa k) * ∫ a : ℂ, maDens (EY (Q.G n) α k) (Fin.cons a y) := by
      intro y hy
      have hyU : y ∈ Q.U n := (Q.B_meas n).2 hy
      have hnh : Q.U n ∈ 𝓝 y := (Q.U_open n).mem_nhds hyU
      have h2 : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := ENat.LEInfty.out
      exact GlobalTheory.T.log_sine_monge_ampere_integral hF d k hk1 hk2 (Q.G n) α y
        (by filter_upwards [hnh] with y' hy' using Q.G_pos n y' hy')
        (fun p q => ((Q.G_smooth n p q).contDiffAt hnh).of_le h2)
        (ContDiffAt.sum fun a _ => contDiffAt_const.mul (((Q.α_smooth n a).contDiffAt hnh).of_le h2))
    rw [Finset.sum_congr rfl fun i hi => integral_congr_ae (hae i (Finset.mem_range.1 hi)),
      setIntegral_congr_fun hmY hH]
    exact fibre_sum (Q.B n) F _ _ hFint hHint hpt (Q.B_meas n).1
  have hsW : HasSum (fun n => ∑ i ∈ Finset.range k, ∫ z in {z : Fin (d + 2) → ℂ | Fin.tail (Fin.tail z) ∈ Q.B n},
      Q.gH (Q.ΦW n z) * paramDens (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) (Q.ΦW n) z)
      (∑ i ∈ Finset.range k, mInt Q.SW.A (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) Q.gH) :=
    hasSum_sum fun i _ => (hcW i).2
  rw [funext key] at hsW
  rw [Finset.sum_congr rfl fun i _ => hpolW i, hpolY]
  exact hsW.unique (hcY.2.mul_left _)

end GlobalTheory.CompanionTheory.Ar.PB
end
end

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_polar_integral_identity : Inputs → GroundTheory.Heights₂.Heights.Inter.FibreLocal.Statement → ∀ (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (a₀ : σ) (ε : σ → ℤ) (Q : AnSq SY a₀ ε) (c : σ → ℝ), c a₀ = 0 → ∀ k : ℕ, 1 ≤ k → 2 * k ≤ d + 2 → ∑ i ∈ Finset.range k, polar (d + 2) (fun w => mInt Q.SW.A (fun r => Q.SW.potH (w r)) Q.gH) (Q.wcoef c k i) = 2 * kappa k * polar (d + 1) SY.degNum (mix (2 * k - 1) (fun a => (ε a : ℝ)) c) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.AnSq.sum_polar_gH_eq
end
