import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCharacterContinuousUnit

section
noncomputable section

open MeasureTheory Metric Set Filter Topology

namespace GlobalTheory.CompanionTheory.CfFJ

structure Fam {X : Type*} [TopologicalSpace X] (U : Set ℂ) (f : ℂ → X → ℂ) : Prop where
  cont : ContinuousOn (fun q : ℂ × X => f q.1 q.2) (U ×ˢ univ)
  hol : ∀ x, DifferentiableOn ℂ (f · x) U
  bd : ∀ K : Set ℂ, K ⊆ U → IsCompact K → ∃ B : ℝ, ∀ w ∈ K, ∀ x, ‖f w x‖ ≤ B

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {U : Set ℂ}


theorem Fam.comp {f : ℂ → X → ℂ} (h : Fam U f) {φ : Z → X} (hφ : Continuous φ) : Fam U (fun w z => f w (φ z)) where
  cont := h.cont.comp (continuous_fst.prodMk (hφ.comp continuous_snd)).continuousOn (fun q hq => ⟨hq.1, mem_univ _⟩)
  hol z := h.hol (φ z)
  bd K hK hc := by
    obtain ⟨B, hB⟩ := h.bd K hK hc
    exact ⟨B, fun w hw z => hB w hw _⟩

theorem Fam.slice {f : ℂ → X → ℂ} (h : Fam U f) {w : ℂ} (hw : w ∈ U) : Continuous (f w) :=
  h.cont.comp_continuous (f := fun x => (w, x)) (by fun_prop) (fun _ => ⟨hw, mem_univ _⟩)

variable [MeasurableSpace Y] [OpensMeasurableSpace Y] {ν : Measure Y} {κ : Y → ℂ}

theorem Fam.swap [SFinite ν] {g : ℂ → Y → ℂ} (h : Fam U g) (hκ : Integrable κ ν) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hS : sphere c R ⊆ U) {a : ℂ → ℂ} (ha : ContinuousOn a (sphere c R)) :
    ∫ y, (∮ w in C(c, R), a w * g w y) * κ y ∂ν = ∮ w in C(c, R), a w * ∫ y, g w y * κ y ∂ν := by
  have cm : ∀ θ, circleMap c R θ ∈ sphere c R := circleMap_mem_sphere c hR.le
  have hcm : Continuous (circleMap c R) := continuous_circleMap c R
  obtain ⟨A, hA⟩ := (isCompact_sphere c R).exists_bound_of_continuousOn ha
  obtain ⟨B, hB⟩ := h.bd _ hS (isCompact_sphere c R)
  set Φ : ℝ → Y → ℂ := fun θ y => deriv (circleMap c R) θ • (a (circleMap c R θ) * g (circleMap c R θ) y) with hΦ
  have hΦc : Continuous fun q : Y × ℝ => Φ q.2 q.1 := by
    have h1 : Continuous fun q : Y × ℝ => g (circleMap c R q.2) q.1 :=
      h.cont.comp_continuous (f := fun q : Y × ℝ => (circleMap c R q.2, q.1))
        ((hcm.comp continuous_snd).prodMk continuous_fst) (fun q => ⟨hS (cm _), mem_univ _⟩)
    have h2 : Continuous fun θ => a (circleMap c R θ) := ha.comp_continuous hcm cm
    have h3 : Continuous fun θ => deriv (circleMap c R) θ := by
      simp only [deriv_circleMap]
      exact (continuous_circleMap 0 R).mul continuous_const
    simp only [hΦ, smul_eq_mul]
    exact (h3.comp continuous_snd).mul ((h2.comp continuous_snd).mul h1)
  have hΦb : ∀ θ y, ‖Φ θ y‖ ≤ |R| * (A * B) := by
    intro θ y
    simp only [hΦ, smul_eq_mul, norm_mul, deriv_circleMap, norm_circleMap_zero, Complex.norm_I, mul_one]
    have hb := hB _ (cm θ) y
    gcongr
    · exact (norm_nonneg _).trans (hA _ (cm θ))
    · exact hA _ (cm θ)
  have hint : Integrable (Function.uncurry fun (y : Y) (θ : ℝ) => Φ θ y * κ y)
      (ν.prod (volume.restrict (Ioc 0 (2 * Real.pi)))) := by
    have h0 : Integrable (fun q : Y × ℝ => κ q.1 * (1 : ℂ)) (ν.prod (volume.restrict (Ioc 0 (2 * Real.pi)))) :=
      hκ.mul_prod (integrable_const (1 : ℂ))
    have h1 := h0.bdd_mul (f := fun q : Y × ℝ => Φ q.2 q.1) (c := |R| * (A * B)) hΦc.aestronglyMeasurable
      (Eventually.of_forall fun q => hΦb _ _)
    refine h1.congr (Eventually.of_forall fun q => ?_)
    simp [Function.uncurry]
  have hpos : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  calc ∫ y, (∮ w in C(c, R), a w * g w y) * κ y ∂ν
      = ∫ y, ∫ θ in Ioc 0 (2 * Real.pi), Φ θ y * κ y ∂volume ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [circleIntegral, intervalIntegral.integral_of_le hpos, integral_mul_const, hΦ]
    _ = ∫ θ in Ioc 0 (2 * Real.pi), ∫ y, Φ θ y * κ y ∂ν := integral_integral_swap hint
    _ = ∮ w in C(c, R), a w * ∫ y, g w y * κ y ∂ν := by
        simp only [circleIntegral, intervalIntegral.integral_of_le hpos]
        refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
        simp only [hΦ, smul_eq_mul, mul_assoc, integral_const_mul]

theorem Fam.stage [FirstCountableTopology X] [SFinite ν] (hU : IsOpen U) {f : ℂ → X × Y → ℂ} (h : Fam U f)
    (hκ : Integrable κ ν) : Fam U (fun w x => ∫ y, f w (x, y) * κ y ∂ν) := by
  have hsl : ∀ {w : ℂ}, w ∈ U → ∀ x, Continuous fun y => f w (x, y) := fun hw x =>
    (h.slice hw).comp (by fun_prop)
  have hcont : ContinuousOn (fun q : ℂ × X => ∫ y, f q.1 (q.2, y) * κ y ∂ν) (U ×ˢ univ) := by
    intro q hq
    have hqU : q.1 ∈ U := hq.1
    obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hqU)
    obtain ⟨B, hB⟩ := h.bd _ hrU (isCompact_closedBall _ _)
    have hnear : ∀ᶠ u : ℂ × X in 𝓝 q, u.1 ∈ ball q.1 r :=
      continuous_fst.continuousAt.eventually (isOpen_ball.mem_nhds (mem_ball_self hr))
    refine ContinuousAt.continuousWithinAt (continuousAt_of_dominated (bound := fun y => B * ‖κ y‖) ?_ ?_ ?_ ?_)
    · filter_upwards [hnear] with u hu
      exact (hsl (hrU (ball_subset_closedBall hu)) u.2).aestronglyMeasurable.mul hκ.aestronglyMeasurable
    · filter_upwards [hnear] with u hu
      refine Eventually.of_forall fun y => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB _ (ball_subset_closedBall hu) _) (norm_nonneg _)
    · exact hκ.norm.const_mul B
    · refine Eventually.of_forall fun y => ?_
      have h1 : ContinuousAt (fun q : ℂ × (X × Y) => f q.1 q.2) (q.1, (q.2, y)) :=
        h.cont.continuousAt ((hU.prod isOpen_univ).mem_nhds ⟨hqU, mem_univ _⟩)
      have h2 : ContinuousAt (fun u : ℂ × X => (u.1, (u.2, y))) q := by fun_prop
      exact (ContinuousAt.comp (f := fun u : ℂ × X => (u.1, (u.2, y))) h1 h2).mul continuousAt_const
  refine ⟨hcont, ?_, ?_⟩
  · intro x w₀ hw₀
    refine DifferentiableAt.differentiableWithinAt ?_
    obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hw₀)
    have hg : Fam U fun w y => f w (x, y) := h.comp (φ := fun y => (x, y)) (by fun_prop)
    have hS : sphere w₀ r ⊆ U := sphere_subset_closedBall.trans hrU
    have hQc : ContinuousOn (fun w => ∫ y, f w (x, y) * κ y ∂ν) U :=
      hcont.comp (Continuous.continuousOn (f := fun w : ℂ => (w, x)) (by fun_prop)) (fun w hw => ⟨hw, mem_univ _⟩)
    set Q : ℂ → ℂ := fun w => ∫ y, f w (x, y) * κ y ∂ν with hQ
    have hci : CircleIntegrable Q w₀ ((⟨r, hr.le⟩ : NNReal) : ℝ) := (hQc.mono hS).circleIntegrable hr.le
    have hps := hasFPowerSeriesOn_cauchy_integral hci (show (0 : NNReal) < ⟨r, hr.le⟩ from hr)
    refine hps.analyticAt.differentiableAt.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with w hw
    have hwS : ∀ v ∈ sphere w₀ r, v ≠ w := by
      rintro v hv rfl
      exact (ne_of_lt (mem_ball.1 hw)) (mem_sphere.1 hv)
    have hcauchy : ∀ y, ∮ v in C(w₀, r), ((2 * Real.pi * Complex.I)⁻¹ * (v - w)⁻¹) * f v (x, y) = f w (x, y) := by
      intro y
      have h1 := Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable (s := ∅) countable_empty hw
        (f := fun v => f v (x, y)) ((hg.hol y).continuousOn.mono hrU)
        (fun v hv => (hg.hol y).differentiableAt (hU.mem_nhds (hrU (ball_subset_closedBall hv.1))))
      simp only [smul_eq_mul] at h1
      simp only [mul_assoc ((2 * (Real.pi : ℂ) * Complex.I)⁻¹), circleIntegral.integral_const_mul]
      rw [h1, ← mul_assoc, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul]
    have hsw := hg.swap hκ hr hS (a := fun v => (2 * Real.pi * Complex.I)⁻¹ * (v - w)⁻¹)
      (continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).inv₀ fun v hv => sub_ne_zero.2 (hwS v hv)))
    simp only [hcauchy] at hsw
    simp only [smul_eq_mul]
    change Q w = _
    rw [hQ]
    simp only
    rw [hsw]
    simp only [mul_assoc ((2 * (Real.pi : ℂ) * Complex.I)⁻¹), circleIntegral.integral_const_mul]
    rfl
  · intro K hK hc
    obtain ⟨B, hB⟩ := h.bd K hK hc
    refine ⟨∫ y, B * ‖κ y‖ ∂ν, fun w hw x => ?_⟩
    refine norm_integral_le_of_norm_le (hκ.norm.const_mul B) (Eventually.of_forall fun y => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hB w hw _) (norm_nonneg _)

theorem circle_cont {e : ℂ → Z → ℂ} (hc : ContinuousOn (fun q : ℂ × Z => e q.1 q.2) (U ×ˢ univ)) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hS : sphere c R ⊆ U) {a : ℂ → ℂ} (ha : ContinuousOn a (sphere c R)) :
    Continuous fun z => ∮ w in C(c, R), a w * e w z := by
  have cm : ∀ θ, circleMap c R θ ∈ sphere c R := circleMap_mem_sphere c hR
  have hcm : Continuous (circleMap c R) := continuous_circleMap c R
  have h1 : Continuous fun q : Z × ℝ => e (circleMap c R q.2) q.1 :=
    hc.comp_continuous (f := fun q : Z × ℝ => (circleMap c R q.2, q.1))
      ((hcm.comp continuous_snd).prodMk continuous_fst) (fun q => ⟨hS (cm _), mem_univ _⟩)
  have h2 : Continuous fun θ => a (circleMap c R θ) := ha.comp_continuous hcm cm
  have h3 : Continuous fun θ => deriv (circleMap c R) θ := by
    simp only [deriv_circleMap]
    exact (continuous_circleMap 0 R).mul continuous_const
  simp only [circleIntegral]
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
  simp only [Function.uncurry_def, smul_eq_mul]
  exact (h3.comp continuous_snd).mul ((h2.comp continuous_snd).mul h1)

theorem circle_zero {e : ℂ → ℂ} (hU : IsOpen U) (he : DifferentiableOn ℂ e U) {d : Polynomial ℂ} (hd : d ≠ 0) {s₀ : ℂ} {ε : ℝ}
    (hε : 0 < ε) (hB : closedBall s₀ ε ⊆ U) (hroot : ∀ z ∈ closedBall s₀ ε, z ≠ s₀ → d.eval z ≠ 0) {j : ℕ}
    (hj : d.rootMultiplicity s₀ ≤ j) : ∮ z in C(s₀, ε), (z - s₀) ^ j * (e z / d.eval z) = 0 := by
  obtain ⟨q, hq, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd d hd s₀
  set m := d.rootMultiplicity s₀ with hm
  have hev : ∀ z, d.eval z = (z - s₀) ^ m * q.eval z := fun z => by
    conv_lhs => rw [hq]
    simp
  have hq0 : ∀ z ∈ closedBall s₀ ε, q.eval z ≠ 0 := by
    intro z hz h0
    by_cases hzs : z = s₀
    · subst hzs
      exact hnd (Polynomial.dvd_iff_isRoot.2 h0)
    · exact hroot z hz hzs (by rw [hev, h0, mul_zero])
  have hsub : ∀ z ∈ sphere s₀ ε, z ≠ s₀ := by
    rintro z hz rfl
    simp [hε.ne] at hz
  have hcongr : ∮ z in C(s₀, ε), (z - s₀) ^ j * (e z / d.eval z) =
      ∮ z in C(s₀, ε), (z - s₀) ^ (j - m) * (e z / q.eval z) := by
    refine circleIntegral.integral_congr hε.le fun z hz => ?_
    have h1 : z - s₀ ≠ 0 := sub_ne_zero.2 (hsub z hz)
    have h2 := hq0 z (sphere_subset_closedBall hz)
    rw [hev, show j = (j - m) + m by omega, pow_add, Nat.add_sub_cancel]
    field_simp
  rw [hcongr]
  have hdiff : ∀ z ∈ closedBall s₀ ε, DifferentiableAt ℂ (fun z => (z - s₀) ^ (j - m) * (e z / q.eval z)) z := by
    intro z hz
    have h1 : DifferentiableAt ℂ e z := he.differentiableAt (hU.mem_nhds (hB hz))
    have h2 : DifferentiableAt ℂ (fun z => q.eval z) z := q.differentiable.differentiableAt
    exact ((differentiableAt_id.sub_const s₀).pow _).mul (h1.div h2 (hq0 z hz))
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hε.le countable_empty
    (fun z hz => (hdiff z hz).continuousAt.continuousWithinAt)
    (fun z hz => hdiff z (ball_subset_closedBall hz.1))

end GlobalTheory.CompanionTheory.CfFJ
end
end

section
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CfFJ

open Metric Set

variable {D : D7} {n ρ p : ℕ}

theorem conj_chz (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) :
    Continuous (fun z : hermA D ρ => conj (chz ψ b₀ z)) ∧ ∀ z : hermA D ρ, ‖conj (chz ψ b₀ z)‖ = 1 := by
  obtain ⟨hc, -⟩ := GlobalTheory.CompanionTheory.CoefWeight.continuous_norm_coefChar D ρ ψ hψ b₀
  have h1 : ∀ z : hermA D ρ, conj (chz ψ b₀ z) =
      ψ (-halfTr (Matrix.trace (HMul.hMul (b₀.1.map (incA D)) z.1 : Mx D ρ ρ))) := by
    intro z
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 _)]
    rfl
  refine ⟨by simpa only [h1] using hc, fun z => ?_⟩
  rw [RCLike.norm_conj]
  exact hψ.2.1 _

theorem cf_eq (d : Polynomial ℂ) (E : ℂ → G D n → ℂ) (s₀ : ℂ) (ε : ℝ) (k : ℕ) (g : G D n) :
    cf d E s₀ ε k g = ∮ w in C(s₀, ε),
      ((2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) / d.eval w)) * E w g := by
  have h : ∀ w : ℂ, ((2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) / d.eval w)) * E w g =
      (2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) * (E w g / d.eval w)) := fun w => by ring
  simp only [h, circleIntegral.integral_const_mul, cf]

theorem ker_eq (d : Polynomial ℂ) (F : ℂ → ℂ) (s₀ : ℂ) (ε : ℝ) (k : ℕ) :
    ∮ w in C(s₀, ε), ((2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) / d.eval w)) * F w =
      (2 * Real.pi * Complex.I)⁻¹ * ∮ w in C(s₀, ε), (w - s₀) ^ (k - 1) * (F w / d.eval w) := by
  have h : ∀ w : ℂ, ((2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) / d.eval w)) * F w =
      (2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) * (F w / d.eval w)) := fun w => by ring
  simp only [h, circleIntegral.integral_const_mul]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem cfFJ_of_pcBound : PcBound → CfFJ := by
  intro hPc D n H φ s₀ U d E σ hC ε hR
  obtain ⟨hε, hB, hroot⟩ := hR
  have hU := hC.isOpen
  have hS : sphere s₀ ε ⊆ U := sphere_subset_closedBall.trans hB
  have hsne : ∀ z ∈ sphere s₀ ε, z ≠ s₀ := by
    rintro z hz rfl
    simp [hε.ne] at hz
  set a : ℕ → ℂ → ℂ := fun k w => (2 * Real.pi * Complex.I)⁻¹ * ((w - s₀) ^ (k - 1) / d.eval w) with ha_def
  have ha : ∀ k, ContinuousOn (a k) (sphere s₀ ε) := fun k =>
    continuousOn_const.mul (((continuousOn_id.sub continuousOn_const).pow _).div
      d.continuous.continuousOn (fun z hz => hroot z (sphere_subset_closedBall hz) (hsne z hz)))
  have hcf : ∀ k g, cf d E s₀ ε k g = ∮ w in C(s₀, ε), a k w * E w g := fun k g => cf_eq d E s₀ ε k g
  refine ⟨fun k => ⟨?_, ?_⟩, ⟨d.rootMultiplicity s₀ + 1, fun k hk => funext fun g => ?_⟩, ?_⟩
  · have : cf d E s₀ ε k = fun g => ∮ w in C(s₀, ε), a k w * E w g := funext (hcf k)
    rw [this]
    exact circle_cont hC.cont hε.le hS (ha k)
  · intro γ hγ g
    rw [hcf, hcf]
    exact circleIntegral.integral_congr hε.le fun w hw => by
      simp only [hC.inv w (hS hw) γ hγ g]
  · have h0 := circle_zero hU (hC.hol g) hC.ne hε hB hroot (j := k - 1) (by omega)
    simp only [cf, h0, mul_zero, Pi.zero_apply]
  · intro ρ p hn M m ψ hψ b₀ g η hη
    obtain ⟨-, hcov⟩ := hPc D n ρ p hn M m ψ hψ b₀
    obtain ⟨C, hCc, hcover, -⟩ := hcov g
    obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D ρ p
    haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
    haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
    haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
    haveI : FirstCountableTopology (Mx D ρ p) := inferInstance
    haveI : FirstCountableTopology (Mx D ρ p × Mx D ρ p) := inferInstance
    obtain ⟨hμh, -, hμ1⟩ := m.hμ
    obtain ⟨-, -, hl1⟩ := m.hz
    haveI : SFinite m.μ := inferInstance
    haveI : IsFiniteMeasure (m.lz.restrict m.𝓖) := ⟨by rw [Measure.restrict_apply_univ, hl1]; exact ENNReal.one_lt_top⟩
    haveI : IsFiniteMeasure (m.μ.restrict m.𝓕) := ⟨by rw [Measure.restrict_apply_univ, hμ1]; exact ENNReal.one_lt_top⟩
    obtain ⟨hχc, hχ1⟩ := conj_chz ψ hψ b₀
    have hκ1 : Integrable (fun z : hermA D ρ => conj (chz ψ b₀ z)) (m.lz.restrict m.𝓖) :=
      Integrable.of_bound hχc.aestronglyMeasurable 1 (Eventually.of_forall fun z => (hχ1 z).le)
    have hκ2 : Integrable (fun _ : Mx D ρ p => (1 : ℂ)) (m.μ.restrict m.𝓕) := integrable_const _
    have hκ3 : Integrable (fun y => conj (η y)) m.μ :=
      Complex.conjCLE.toContinuousLinearMap.integrable_comp hη
    set pt : (Mx D ρ p × Mx D ρ p) × hermA D ρ → G D n :=
      fun u => M.nzx u.2 0 * (M.nzx 0 u.1.2 * (M.sh u.1.1 * g)) with hpt_def
    have hpt : Continuous pt :=
      (M.nzx_cont.comp (f := fun u : (Mx D ρ p × Mx D ρ p) × hermA D ρ => (u.2, (0 : Mx D ρ p))) (by fun_prop)).mul
        ((M.nzx_cont.comp (f := fun u : (Mx D ρ p × Mx D ρ p) × hermA D ρ => ((0 : hermA D ρ), u.1.2)) (by fun_prop)).mul
          ((M.sh_cont.comp (f := fun u : (Mx D ρ p × Mx D ρ p) × hermA D ρ => u.1.1) (by fun_prop)).mul continuous_const))
    have h0 : Fam U (fun w u => E w (pt u)) := by
      refine ⟨hC.cont.comp (continuous_fst.prodMk (hpt.comp continuous_snd)).continuousOn
        (fun q hq => ⟨hq.1, mem_univ _⟩), fun u => hC.hol _, fun K hK hKc => ?_⟩
      obtain ⟨B, hBd⟩ := (hKc.prod hCc).exists_bound_of_continuousOn
        (hC.cont.mono (prod_mono hK (subset_univ _)))
      refine ⟨B, fun w hw u => ?_⟩
      obtain ⟨γ, hγ, hmem⟩ := hcover u.2 u.1.2 u.1.1
      rw [show E w (pt u) = E w (γ * pt u) from (hC.inv w (hK hw) γ hγ _).symm]
      exact hBd (w, γ * pt u) ⟨hw, hmem⟩
    have h1 : Fam U (fun w (u : Mx D ρ p × Mx D ρ p) => zc M m ψ b₀ (E w) (M.nzx 0 u.2 * (M.sh u.1 * g))) :=
      h0.stage hU hκ1
    have h2 : Fam U (fun w (y : Mx D ρ p) => pc M m ψ b₀ (E w) (M.sh y * g)) := by
      have := h1.stage hU hκ2
      simp only [mul_one] at this
      exact this
    have h3 : Fam U (fun w (_ : Unit) => FJ M m ψ b₀ (E w) g η) :=
      (h2.comp (φ := fun u : Unit × Mx D ρ p => u.2) continuous_snd).stage hU hκ3
    refine ⟨h3.hol (), fun k => ?_⟩
    have e1 : ∀ y x, zc M m ψ b₀ (cf d E s₀ ε k) (M.nzx 0 x * (M.sh y * g)) =
        ∮ w in C(s₀, ε), a k w * zc M m ψ b₀ (E w) (M.nzx 0 x * (M.sh y * g)) := by
      intro y x
      have := (h0.comp (φ := fun z : hermA D ρ => ((y, x), z)) (by fun_prop)).swap hκ1 hε hS (ha k)
      simp only [zc, hcf, pt] at this ⊢
      exact this
    have e2 : ∀ y, pc M m ψ b₀ (cf d E s₀ ε k) (M.sh y * g) =
        ∮ w in C(s₀, ε), a k w * pc M m ψ b₀ (E w) (M.sh y * g) := by
      intro y
      have := (h1.comp (φ := fun x : Mx D ρ p => (y, x)) (by fun_prop)).swap hκ2 hε hS (ha k)
      simp only [mul_one] at this
      simp only [PositivityTheory.Rg.Rsw.pc, e1]
      exact this
    have e3 : FJ M m ψ b₀ (cf d E s₀ ε k) g η = ∮ w in C(s₀, ε), a k w * FJ M m ψ b₀ (E w) g η := by
      have := h2.swap hκ3 hε hS (ha k)
      simp only [FJ, e2]
      exact this
    rw [e3]
    exact ker_eq d _ s₀ ε k

end GlobalTheory.CompanionTheory.CfFJ
end
end

open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_jacobi_coefficient_of_bound : PcBound → CfFJ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CfFJ.cfFJ_of_pcBound
end
