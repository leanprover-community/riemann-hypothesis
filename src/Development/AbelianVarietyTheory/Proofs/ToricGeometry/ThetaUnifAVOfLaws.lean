import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeSectionFacesAndDoubling
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsGlobalFrameOfLocal
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.AppellHumbertNormalFormOfLinearExponent
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ReFormPosOfThetaNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.EntirePeriodicEqZeroOfFourierCoeffEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CardLePowOfLinearIndependent
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CardLePowOfLinearIndependentThetaPrincipal
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.EqZeroOfForallAlgHomComplex
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.HolFamilyOfIsPullback
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsTopologicalGroupComplexPoints
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CompactSpacePointsPolAV
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsTestFunctionsSubsetOfMemNhds
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEtaleCoordsVanishing
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ContinuousOnValue
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsLinearLift
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsConstOfCover
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.WeilIsExpRiemannForm
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.RiemannFormBijectiveOfWeilNondeg
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.SectionsPowThetaFunctions
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIndepSections
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe

section
open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def doublingIterate (h : E → ℂ) : ℕ → E → ℂ
  | 0 => fun z => h ((2 : ℂ)⁻¹ • z)
  | n + 1 => fun z =>
      3 * doublingIterate h n ((2 : ℂ)⁻¹ • z) + doublingIterate h n (-((2 : ℂ)⁻¹ • z))

private theorem norm_half_smul (z : E) : ‖(2 : ℂ)⁻¹ • z‖ = ‖z‖ / 2 := by
  rw [norm_smul, norm_inv]
  simp [div_eq_inv_mul]

private theorem half_mem_ball {r : ℝ} {z : E} (hz : z ∈ Metric.ball (0 : E) r) :
    (2 : ℂ)⁻¹ • z ∈ Metric.ball (0 : E) r := by
  rw [mem_ball_zero_iff] at hz ⊢
  rw [norm_half_smul]
  linarith [norm_nonneg z]

private theorem neg_mem_ball' {r : ℝ} {z : E} (hz : z ∈ Metric.ball (0 : E) r) :
    -z ∈ Metric.ball (0 : E) r := by
  rw [mem_ball_zero_iff] at hz ⊢
  rwa [norm_neg]

theorem differentiableOn_doublingIterate {h : E → ℂ} {r : ℝ}
    (hh : DifferentiableOn ℂ h (Metric.ball 0 r)) (n : ℕ) :
    DifferentiableOn ℂ (doublingIterate h n) (Metric.ball 0 r) := by
  induction n with
  | zero => exact hh.comp (by fun_prop) fun z hz => half_mem_ball hz
  | succ n ih =>
    have h1 : DifferentiableOn ℂ (fun z : E => doublingIterate h n ((2 : ℂ)⁻¹ • z))
        (Metric.ball 0 r) := ih.comp (by fun_prop) fun z hz => half_mem_ball hz
    have h2 : DifferentiableOn ℂ (fun z : E => doublingIterate h n (-((2 : ℂ)⁻¹ • z)))
        (Metric.ball 0 r) := ih.comp (by fun_prop) fun z hz => neg_mem_ball' (half_mem_ball hz)
    exact (h1.const_mul 3).add h2

theorem norm_doublingIterate_le {h : E → ℂ} {r C : ℝ} (hC : 0 ≤ C)
    (hh : ∀ z ∈ Metric.ball (0 : E) r, ‖h z‖ ≤ C * ‖z‖ ^ 3) (n : ℕ) :
    ∀ z ∈ Metric.ball (0 : E) r, ‖doublingIterate h n z‖ ≤ (1 / 2) ^ n * (C * ‖z‖ ^ 3) := by
  induction n with
  | zero =>
    intro z hz
    have h1 := hh _ (half_mem_ball hz)
    rw [norm_half_smul] at h1
    have h2 : 0 ≤ C * ‖z‖ ^ 3 := by positivity
    change ‖h ((2 : ℂ)⁻¹ • z)‖ ≤ _
    nlinarith
  | succ n ih =>
    intro z hz
    have h1 := ih _ (half_mem_ball hz)
    have h2 := ih _ (neg_mem_ball' (half_mem_ball hz))
    rw [norm_neg] at h2
    rw [norm_half_smul] at h1 h2
    change ‖3 * doublingIterate h n ((2 : ℂ)⁻¹ • z)
      + doublingIterate h n (-((2 : ℂ)⁻¹ • z))‖ ≤ _
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have h3 : ‖(3 : ℂ)‖ = 3 := by simp
    rw [h3]
    calc _ ≤ 3 * ((1 / 2) ^ n * (C * (‖z‖ / 2) ^ 3)) + (1 / 2) ^ n * (C * (‖z‖ / 2) ^ 3) := by
          gcongr
      _ = _ := by ring

theorem exists_doubling_solution [FiniteDimensional ℂ E] (h : E → ℂ) (ha : AnalyticAt ℂ h 0)
    (hO : h =O[𝓝 0] (fun z => ‖z‖ ^ 3)) :
    ∃ k : E → ℂ, AnalyticAt ℂ k 0 ∧ k =O[𝓝 0] (fun z => ‖z‖ ^ 3) ∧
      ∀ᶠ z in 𝓝 0, k ((2 : ℂ) • z) - 3 * k z - k (-z) = h z := by
  obtain ⟨C, hC, hO⟩ := hO.exists_nonneg
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (hO.bound.and ha.eventually_analyticAt)
  have hd : DifferentiableOn ℂ h (Metric.ball 0 r) :=
    fun z hz => (hball z hz).2.differentiableAt.differentiableWithinAt
  have hb : ∀ z ∈ Metric.ball (0 : E) r, ‖h z‖ ≤ C * ‖z‖ ^ 3 := fun z hz => by
    simpa using (hball z hz).1
  have hB := norm_doublingIterate_le hC hb
  have hgeom : ∀ c : ℝ, HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n * c) (2 * c) :=
    fun c => hasSum_geometric_two.mul_right c
  have hS : ∀ z ∈ Metric.ball (0 : E) r, Summable fun n => doublingIterate h n z :=
    fun z hz => Summable.of_norm_bounded (hgeom _).summable fun n => hB n z hz
  refine ⟨fun z => ∑' n, doublingIterate h n z, ?_, ?_, ?_⟩
  · refine SCV.analyticAt_of_differentiableOn (s := Metric.ball 0 r)
      (SCV.differentiableOn_tsum_of_locally_normal Metric.isOpen_ball
        (differentiableOn_doublingIterate hd) fun x hx =>
          ⟨Metric.ball 0 r, Metric.isOpen_ball.mem_nhds hx, _, (hgeom (C * r ^ 3)).summable,
            fun n z hz => (hB n z hz).trans ?_⟩) (Metric.ball_mem_nhds 0 hr)
    have := (mem_ball_zero_iff.mp hz).le
    gcongr
  · refine Asymptotics.IsBigO.of_bound (2 * C) ?_
    filter_upwards [Metric.ball_mem_nhds 0 hr] with z hz
    refine (tsum_of_norm_bounded (hgeom _) fun n => hB n z hz).trans_eq ?_
    simp [mul_assoc]
  · filter_upwards [Metric.ball_mem_nhds (0 : E) (half_pos hr)] with z hz
    rw [mem_ball_zero_iff] at hz
    have hz1 : z ∈ Metric.ball (0 : E) r := by
      rw [mem_ball_zero_iff]
      linarith
    have hz2 : (2 : ℂ) • z ∈ Metric.ball (0 : E) r := by
      rw [mem_ball_zero_iff, norm_smul]
      have : ‖(2 : ℂ)‖ = 2 := by simp
      rw [this]
      linarith
    have e : (2 : ℂ)⁻¹ • (2 : ℂ) • z = z := inv_smul_smul₀ two_ne_zero z
    rw [(hS _ hz2).tsum_eq_zero_add]
    simp only [doublingIterate, e]
    rw [((hS z hz1).mul_left 3).tsum_add (hS _ (neg_mem_ball' hz1)), tsum_mul_left]
    ring

end

theorem exists_doubling_solution_pi :
    ∀ (g : ℕ) (h : (Fin g → ℂ) → ℂ), AnalyticAt ℂ h 0 → h =O[𝓝 0] (fun z => ‖z‖ ^ 3) →
      ∃ k : (Fin g → ℂ) → ℂ, AnalyticAt ℂ k 0 ∧ k =O[𝓝 0] (fun z => ‖z‖ ^ 3) ∧
        ∀ᶠ z in 𝓝 0, k ((2 : ℂ) • z) - 3 * k z - k (-z) = h z :=
  fun _ h ha hO => exists_doubling_solution h ha hO

end GlobalTheory
end

section
open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

private lemma eq_zero_of_cube_bound_of_doubling {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (F : E → ℂ) (ε C : ℝ)
    (hP : ∀ w : E, ‖w‖ < ε → ‖F w‖ ≤ C * ‖w‖ ^ 3 ∧ F ((2 : ℂ) • w) = 3 * F w + F (-w))
    (z : E) (hz : ‖z‖ < ε) : F z = 0 := by

  set M : E → ℝ := fun w => ‖F w‖ + ‖F (-w)‖ with hM
  have step : ∀ w : E, ‖w‖ < ε → M ((2 : ℂ) • w) ≤ 4 * M w := by
    intro w hw
    have h1 := (hP w hw).2
    have h2 := (hP (-w) (by rwa [norm_neg])).2
    rw [neg_neg] at h2
    simp only [hM]
    rw [← smul_neg, h1, h2]
    have e1 : ‖3 * F w + F (-w)‖ ≤ 3 * ‖F w‖ + ‖F (-w)‖ :=
      (norm_add_le _ _).trans (by simp)
    have e2 : ‖3 * F (-w) + F w‖ ≤ 3 * ‖F (-w)‖ + ‖F w‖ :=
      (norm_add_le _ _).trans (by simp)
    linarith
  set w : ℕ → E := fun n => ((2 : ℂ)⁻¹) ^ n • z with hw
  have hnorm : ∀ n, ‖w n‖ = ((2 : ℝ) ^ n)⁻¹ * ‖z‖ := by
    intro n
    simp [hw, norm_smul]
  have hsmall : ∀ n, ‖w n‖ < ε := by
    intro n
    rw [hnorm]
    have h1 : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    calc ((2 : ℝ) ^ n)⁻¹ * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
      _ < ε := by simpa using hz
  have hsucc : ∀ n, w n = (2 : ℂ) • w (n + 1) := by
    intro n
    simp only [hw, smul_smul]
    congr 1
    rw [pow_succ]
    field_simp
  have hiter : ∀ n : ℕ, M z ≤ 4 ^ n * M (w n) := by
    intro n
    induction n with
    | zero => simp [hw]
    | succ n ih =>
      calc M z ≤ 4 ^ n * M (w n) := ih
        _ = 4 ^ n * M ((2 : ℂ) • w (n + 1)) := by rw [← hsucc]
        _ ≤ 4 ^ n * (4 * M (w (n + 1))) := by
          gcongr
          exact step _ (hsmall _)
        _ = 4 ^ (n + 1) * M (w (n + 1)) := by ring
  have hbound : ∀ n : ℕ, M z ≤ (2 * C * ‖z‖ ^ 3) * ((1 : ℝ) / 2) ^ n := by
    intro n
    have hb : M (w n) ≤ 2 * C * ‖w n‖ ^ 3 := by
      have a1 := (hP (w n) (hsmall n)).1
      have a2 := (hP (-w n) (by rw [norm_neg]; exact hsmall n)).1
      rw [norm_neg] at a2
      simp only [hM]
      linarith
    have h4 : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    calc M z ≤ 4 ^ n * M (w n) := hiter n
      _ ≤ 4 ^ n * (2 * C * ‖w n‖ ^ 3) := by gcongr
      _ = (2 * C * ‖z‖ ^ 3) * ((1 : ℝ) / 2) ^ n := by
        have h2 : ((1 : ℝ) / 2) ^ n * 2 ^ n = 1 := by
          rw [← mul_pow]
          norm_num
        rw [hnorm, h4]
        field_simp
        linear_combination (-(C * ‖z‖ ^ 3)) * h2
  have hlim : Filter.Tendsto (fun n : ℕ => (2 * C * ‖z‖ ^ 3) * ((1 : ℝ) / 2) ^ n)
      Filter.atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (2 * C * ‖z‖ ^ 3)
    simpa using this
  have hM0 : M z ≤ 0 := ge_of_tendsto' hlim hbound
  have : ‖F z‖ ≤ 0 := by
    have := norm_nonneg (F (-z))
    simp only [hM] at hM0
    linarith
  exact norm_le_zero_iff.1 this

theorem eventually_eq_zero_of_isBigO_cube_of_doubling :
    (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : E → ℂ),
      F =O[𝓝 0] (fun z => ‖z‖ ^ 3) →
      (∀ᶠ z in 𝓝 0, F ((2 : ℂ) • z) = 3 * F z + F (-z)) → ∀ᶠ z in 𝓝 0, F z = 0) := by
  intro E _ _ F hO hrel
  obtain ⟨C, hC⟩ := hO.bound
  have hev : ∀ᶠ z in 𝓝 (0 : E), ‖F z‖ ≤ C * ‖z‖ ^ 3 ∧ F ((2 : ℂ) • z) = 3 * F z + F (-z) := by
    filter_upwards [hC, hrel] with z h1 h2
    exact ⟨by simpa using h1, h2⟩
  obtain ⟨ε, hε, hP⟩ := Metric.eventually_nhds_iff.1 hev
  filter_upwards [Metric.ball_mem_nhds (0 : E) hε] with z hz
  exact eq_zero_of_cube_bound_of_doubling F ε C (fun w hw => hP (by simpa using hw)) z
    (by simpa using hz)

end GlobalTheory
end

section
open Complex Matrix Filter Topology Asymptotics
open scoped BigOperators Real

namespace GlobalTheory.LocalCube

open Complex Matrix Filter Topology Asymptotics in
open scoped BigOperators Real in
private lemma norm_le_div_mul_norm_of_schwarz {φ : ℂ → ℂ} {ρ c : ℝ}
    (hd : DifferentiableOn ℂ φ (Metric.ball 0 ρ)) (h0 : φ 0 = 0)
    (hc : ∀ t ∈ Metric.ball (0 : ℂ) ρ, ‖φ t‖ ≤ c) {t : ℂ} (ht : t ∈ Metric.ball (0 : ℂ) ρ) :
    ‖φ t‖ ≤ c / ρ * ‖t‖ := by
  have hmap : Set.MapsTo φ (Metric.ball 0 ρ) (Metric.closedBall (φ 0) c) := by
    intro s hs
    rw [h0, mem_closedBall_zero_iff]
    exact hc s hs
  simpa [h0, dist_zero_right] using Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hmap ht

open Complex Matrix Filter Topology Asymptotics in
open scoped BigOperators Real in
private lemma isBigO_norm_cube_of_analytic_vanishing_coords {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {u : (Fin 3 → V) → ℂ} (ha : AnalyticAt ℂ u 0)
    (hv : ∀ a : Fin 3, ∀ᶠ x in 𝓝 (0 : Fin 3 → V), x a = 0 → u x = 0) :
    u =O[𝓝 0] fun z => ‖z‖ ^ 3 := by
  have hu0 : u 0 = 0 := (hv 0).self_of_nhds rfl
  have hev : ∀ᶠ x in 𝓝 (0 : Fin 3 → V),
      DifferentiableAt ℂ u x ∧ ‖u x‖ < 1 ∧ ∀ a, x a = 0 → u x = 0 := by
    have h1 : ∀ᶠ x in 𝓝 (0 : Fin 3 → V), DifferentiableAt ℂ u x :=
      ha.eventually_analyticAt.mono fun x hx => hx.differentiableAt
    have h2 : ∀ᶠ x in 𝓝 (0 : Fin 3 → V), ‖u x‖ < 1 :=
      ha.continuousAt.norm.eventually (gt_mem_nhds (by simp [hu0]))
    exact h1.and (h2.and (Filter.eventually_all.2 hv))
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine IsBigO.of_bound (1 / R ^ 3) ?_
  filter_upwards [Metric.ball_mem_nhds 0 hR] with y hy
  simp only [norm_pow, norm_norm]
  rcases eq_or_ne y 0 with rfl | hy0
  · simp [hu0]
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hyR : ‖y‖ < R := mem_ball_zero_iff.1 hy
  set ρ := R / ‖y‖ with hρdef
  have hρ : 0 < ρ := div_pos hR hyn
  have hρ1 : 1 < ρ := (one_lt_div hyn).2 hyR
  let e : Fin 3 → (Fin 3 → V) := fun a => Pi.single a (y a)
  let p : ℂ → ℂ → ℂ → (Fin 3 → V) := fun t₀ t₁ t₂ => t₀ • e 0 + t₁ • e 1 + t₂ • e 2
  have hpa : ∀ t₀ t₁ t₂ a, p t₀ t₁ t₂ a = ![t₀, t₁, t₂] a • y a := by
    intro t₀ t₁ t₂ a
    fin_cases a <;> simp [p, e, Pi.single_apply]
  have hpb : ∀ t₀ t₁ t₂, ‖t₀‖ < ρ → ‖t₁‖ < ρ → ‖t₂‖ < ρ → p t₀ t₁ t₂ ∈ Metric.ball 0 R := by
    intro t₀ t₁ t₂ h₀ h₁ h₂
    rw [mem_ball_zero_iff, pi_norm_lt_iff hR]
    intro a
    rw [hpa, norm_smul]
    have hya : ‖y a‖ ≤ ‖y‖ := norm_le_pi_norm y a
    have hta : ‖![t₀, t₁, t₂] a‖ < ρ := by fin_cases a <;> simp [h₀, h₁, h₂]
    calc ‖![t₀, t₁, t₂] a‖ * ‖y a‖ ≤ ‖![t₀, t₁, t₂] a‖ * ‖y‖ :=
          mul_le_mul_of_nonneg_left hya (norm_nonneg _)
      _ < ρ * ‖y‖ := mul_lt_mul_of_pos_right hta hyn
      _ = R := by rw [hρdef]; field_simp
  let G : ℂ → ℂ → ℂ → ℂ := fun t₀ t₁ t₂ => u (p t₀ t₁ t₂)
  have hGb : ∀ t₀ t₁ t₂, ‖t₀‖ < ρ → ‖t₁‖ < ρ → ‖t₂‖ < ρ → ‖G t₀ t₁ t₂‖ ≤ 1 :=
    fun _ _ _ h₀ h₁ h₂ => (hball _ (hpb _ _ _ h₀ h₁ h₂)).2.1.le
  have hGz : ∀ t₀ t₁ t₂ (a : Fin 3), ‖t₀‖ < ρ → ‖t₁‖ < ρ → ‖t₂‖ < ρ →
      ![t₀, t₁, t₂] a = 0 → G t₀ t₁ t₂ = 0 := by
    intro t₀ t₁ t₂ a h₀ h₁ h₂ ha0
    exact (hball _ (hpb _ _ _ h₀ h₁ h₂)).2.2 a (by rw [hpa, ha0, zero_smul])
  have hGd : ∀ t₀ t₁ t₂, ‖t₀‖ < ρ → ‖t₁‖ < ρ → ‖t₂‖ < ρ → DifferentiableAt ℂ u (p t₀ t₁ t₂) :=
    fun _ _ _ h₀ h₁ h₂ => (hball _ (hpb _ _ _ h₀ h₁ h₂)).1
  have hd₀ : ∀ t₁ t₂, ‖t₁‖ < ρ → ‖t₂‖ < ρ →
      DifferentiableOn ℂ (fun s => G s t₁ t₂) (Metric.ball 0 ρ) := by
    intro t₁ t₂ h₁ h₂ s hs
    rw [mem_ball_zero_iff] at hs
    have hfd : DifferentiableAt ℂ (fun s : ℂ => p s t₁ t₂) s := by
      show DifferentiableAt ℂ (fun s : ℂ => s • e 0 + t₁ • e 1 + t₂ • e 2) s
      fun_prop
    exact (DifferentiableAt.comp s (hGd s t₁ t₂ hs h₁ h₂) hfd).differentiableWithinAt
  have hd₁ : ∀ t₀ t₂, ‖t₀‖ < ρ → ‖t₂‖ < ρ →
      DifferentiableOn ℂ (fun s => G t₀ s t₂) (Metric.ball 0 ρ) := by
    intro t₀ t₂ h₀ h₂ s hs
    rw [mem_ball_zero_iff] at hs
    have hfd : DifferentiableAt ℂ (fun s : ℂ => p t₀ s t₂) s := by
      show DifferentiableAt ℂ (fun s : ℂ => t₀ • e 0 + s • e 1 + t₂ • e 2) s
      fun_prop
    exact (DifferentiableAt.comp s (hGd t₀ s t₂ h₀ hs h₂) hfd).differentiableWithinAt
  have hd₂ : ∀ t₀ t₁, ‖t₀‖ < ρ → ‖t₁‖ < ρ →
      DifferentiableOn ℂ (fun s => G t₀ t₁ s) (Metric.ball 0 ρ) := by
    intro t₀ t₁ h₀ h₁ s hs
    rw [mem_ball_zero_iff] at hs
    have hfd : DifferentiableAt ℂ (fun s : ℂ => p t₀ t₁ s) s := by
      show DifferentiableAt ℂ (fun s : ℂ => t₀ • e 0 + t₁ • e 1 + s • e 2) s
      fun_prop
    exact (DifferentiableAt.comp s (hGd t₀ t₁ s h₀ h₁ hs) hfd).differentiableWithinAt
  have h0ρ : ‖(0 : ℂ)‖ < ρ := by simpa using hρ
  have S₁ : ∀ t₀ t₁ t₂, ‖t₀‖ < ρ → ‖t₁‖ < ρ → ‖t₂‖ < ρ → ‖G t₀ t₁ t₂‖ ≤ 1 / ρ * ‖t₀‖ := by
    intro t₀ t₁ t₂ h₀ h₁ h₂
    exact norm_le_div_mul_norm_of_schwarz (φ := fun s => G s t₁ t₂) (hd₀ t₁ t₂ h₁ h₂)
      (hGz 0 t₁ t₂ 0 h0ρ h₁ h₂ (by simp))
      (fun s hs => hGb s t₁ t₂ (mem_ball_zero_iff.1 hs) h₁ h₂) (mem_ball_zero_iff.2 h₀)
  have S₂ : ∀ t₀ t₁ t₂, ‖t₀‖ < ρ → ‖t₁‖ < ρ → ‖t₂‖ < ρ →
      ‖G t₀ t₁ t₂‖ ≤ 1 / ρ / ρ * ‖t₁‖ * ‖t₀‖ := by
    intro t₀ t₁ t₂ h₀ h₁ h₂
    rcases eq_or_ne t₀ 0 with rfl | ht₀
    · rw [hGz 0 t₁ t₂ 0 h₀ h₁ h₂ (by simp)]
      simp
    have hn : 0 < ‖t₀‖ := norm_pos_iff.2 ht₀
    have hb : ∀ s ∈ Metric.ball (0 : ℂ) ρ, ‖G t₀ s t₂ / t₀‖ ≤ 1 / ρ := by
      intro s hs
      rw [norm_div, div_le_iff₀ hn]
      exact S₁ t₀ s t₂ h₀ (mem_ball_zero_iff.1 hs) h₂
    have key := norm_le_div_mul_norm_of_schwarz (φ := fun s => G t₀ s t₂ / t₀) ((hd₁ t₀ t₂ h₀ h₂).div_const t₀)
      (by simp only [hGz t₀ 0 t₂ 1 h₀ h0ρ h₂ (by simp), zero_div]) hb (mem_ball_zero_iff.2 h₁)
    beta_reduce at key
    rwa [norm_div, div_le_iff₀ hn] at key
  have S₃ : ∀ t₀ t₁ t₂, ‖t₀‖ < ρ → ‖t₁‖ < ρ → ‖t₂‖ < ρ →
      ‖G t₀ t₁ t₂‖ ≤ 1 / ρ / ρ / ρ * ‖t₂‖ * (‖t₁‖ * ‖t₀‖) := by
    intro t₀ t₁ t₂ h₀ h₁ h₂
    rcases eq_or_ne (t₁ * t₀) 0 with h | ht
    · rcases mul_eq_zero.1 h with rfl | rfl
      · rw [hGz t₀ 0 t₂ 1 h₀ h₁ h₂ (by simp)]
        simp
      · rw [hGz 0 t₁ t₂ 0 h₀ h₁ h₂ (by simp)]
        simp
    have hn : 0 < ‖t₁ * t₀‖ := norm_pos_iff.2 ht
    have hb : ∀ s ∈ Metric.ball (0 : ℂ) ρ, ‖G t₀ t₁ s / (t₁ * t₀)‖ ≤ 1 / ρ / ρ := by
      intro s hs
      rw [norm_div, div_le_iff₀ hn, norm_mul, ← mul_assoc]
      exact S₂ t₀ t₁ s h₀ h₁ (mem_ball_zero_iff.1 hs)
    have key := norm_le_div_mul_norm_of_schwarz (φ := fun s => G t₀ t₁ s / (t₁ * t₀))
      ((hd₂ t₀ t₁ h₀ h₁).div_const _)
      (by simp only [hGz t₀ t₁ 0 2 h₀ h₁ h0ρ (by simp), zero_div]) hb (mem_ball_zero_iff.2 h₂)
    beta_reduce at key
    rwa [norm_div, div_le_iff₀ hn, norm_mul] at key
  have h1 : ‖(1 : ℂ)‖ < ρ := by simpa using hρ1
  have hy1 : p 1 1 1 = y := by
    funext a
    rw [hpa]
    fin_cases a <;> simp
  have hG1 : G 1 1 1 = u y := congrArg u hy1
  have hfin := S₃ 1 1 1 h1 h1 h1
  rw [hG1] at hfin
  simp only [norm_one, mul_one] at hfin
  calc ‖u y‖ ≤ 1 / ρ / ρ / ρ := hfin
    _ = 1 / R ^ 3 * ‖y‖ ^ 3 := by rw [hρdef]; field_simp

open Complex Matrix Filter Topology Asymptotics in
open scoped BigOperators Real in
private lemma isBigO_norm_cube_comp_clm {E F' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F'] [NormedSpace ℂ F'] {u : F' → ℂ}
    (hu : u =O[𝓝 0] fun z => ‖z‖ ^ 3) (T : E →L[ℂ] F') :
    (fun x => u (T x)) =O[𝓝 0] fun x => ‖x‖ ^ 3 := by
  have h1 : (fun x => u (T x)) =O[𝓝 0] fun x => ‖T x‖ ^ 3 :=
    hu.comp_tendsto (by simpa using T.continuous.tendsto 0)
  refine h1.trans (IsBigO.of_bound (‖T‖ ^ 3) (Eventually.of_forall fun x => ?_))
  simp only [norm_pow, norm_norm]
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm x) 3

open Complex Matrix Filter Topology Asymptotics in
open scoped BigOperators Real in
private lemma eventually_nhds_zero_comp_of_continuous {E F' : Type*} [TopologicalSpace E] [Zero E]
    [TopologicalSpace F'] [Zero F'] {T : E → F'} (hT : Continuous T) (h0 : T 0 = 0)
    {p : F' → Prop} (h : ∀ᶠ y in 𝓝 0, p y) : ∀ᶠ x in 𝓝 0, p (T x) :=
  (hT.tendsto' 0 0 h0).eventually h

open Complex Matrix Filter Topology Asymptotics in
open scoped BigOperators Real in

theorem _root_.GlobalTheory.LocalCube.exists_third_difference :
    (∀ (g : ℕ) (h : (Fin g → ℂ) → ℂ), AnalyticAt ℂ h 0 → h =O[𝓝 0] (fun z => ‖z‖ ^ 3) → ∃ k : (Fin g → ℂ) → ℂ, AnalyticAt ℂ k 0 ∧ k =O[𝓝 0] (fun z => ‖z‖ ^ 3) ∧ ∀ᶠ z in 𝓝 0, k ((2 : ℂ) • z) - 3 * k z - k (-z) = h z) → (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : E → ℂ), F =O[𝓝 0] (fun z => ‖z‖ ^ 3) → (∀ᶠ z in 𝓝 0, F ((2 : ℂ) • z) = 3 * F z + F (-z)) → ∀ᶠ z in 𝓝 0, F z = 0) → (∀ (g : ℕ) (F : (Fin 3 → Fin g → ℂ) → ℂ), AnalyticAt ℂ F 0 → F 0 ≠ 0 → ((∀ a : Fin 3, ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), x a = 0 → F x = F 0) ∧ (∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F ((2 : ℂ) • x) * (∏ I : Finset (Fin 3), F ![∑ a ∈ I, x a, ∑ a ∈ I, x a, -∑ a ∈ I, x a] ^ ((-1 : ℤ) ^ (3 - I.card))) * F 0 ^ 3 = F x ^ 3 * F (-x))) → ∃ k : (Fin g → ℂ) → ℂ, AnalyticAt ℂ k 0 ∧ k 0 = 0 ∧ ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F x = F 0 * ∏ I : Finset (Fin 3), cexp (k (∑ a ∈ I, x a)) ^ ((-1 : ℤ) ^ (3 - I.card))) := by
  intro hA hB g F hF hF0 hcond
  obtain ⟨hax, heq⟩ := hcond
  have hsign : ∑ I : Finset (Fin 3), ((((-1 : ℤ) ^ (3 - I.card) : ℤ)) : ℂ) = 0 := by
    have h : ∑ I : Finset (Fin 3), (-1 : ℤ) ^ (3 - I.card) = 0 := by decide
    rw [← Int.cast_sum, h, Int.cast_zero]
  set L := Complex.log (F 0) with hL
  have hL' : cexp L = F 0 := Complex.exp_log hF0
  set f : (Fin 3 → Fin g → ℂ) → ℂ := fun x => Complex.log (F x / F 0) with hfdef
  have hfa : AnalyticAt ℂ f 0 :=
    (hF.div analyticAt_const hF0).clog (by simpa [hF0] using Complex.one_mem_slitPlane)
  have hFne : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F x ≠ 0 := hF.continuousAt.eventually_ne hF0
  have hFexp : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F x = cexp (L + f x) := by
    filter_upwards [hFne] with x hx
    rw [Complex.exp_add, hL']
    simp only [hfdef]
    rw [Complex.exp_log (div_ne_zero hx hF0)]
    field_simp
  have hfax : ∀ a, ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), x a = 0 → f x = 0 := by
    intro a
    filter_upwards [hax a] with x hx h0
    simp only [hfdef, hx h0, div_self hF0, Complex.log_one]
  have hfO : f =O[𝓝 0] fun z => ‖z‖ ^ 3 := isBigO_norm_cube_of_analytic_vanishing_coords hfa hfax
  let M : (Fin g → ℂ) →L[ℂ] (Fin 3 → Fin g → ℂ) := ContinuousLinearMap.pi fun a : Fin 3 =>
    ![ContinuousLinearMap.id ℂ (Fin g → ℂ), ContinuousLinearMap.id ℂ (Fin g → ℂ),
      -ContinuousLinearMap.id ℂ (Fin g → ℂ)] a
  have hM : ∀ s, M s = ![s, s, -s] := by
    intro s
    funext a
    fin_cases a <;> simp [M]
  let S : Finset (Fin 3) → (Fin 3 → Fin g → ℂ) →L[ℂ] (Fin g → ℂ) := fun I =>
    ∑ a ∈ I, ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => Fin g → ℂ) a
  have hS : ∀ I x, S I x = ∑ a ∈ I, x a := by
    intro I x
    simp [S]
  let φ : (Fin g → ℂ) → ℂ := fun s => f (M s)
  have hφa : AnalyticAt ℂ φ 0 := hfa.comp_of_eq (M.analyticAt 0) (map_zero M)
  have hφO : φ =O[𝓝 0] fun z => ‖z‖ ^ 3 := isBigO_norm_cube_comp_clm hfO M
  obtain ⟨k, hka, hkO, hkeq⟩ := hA g (fun s => -φ s) hφa.neg hφO.neg_left
  have hk0 : k 0 = 0 := by
    have : k =O[𝓝 (0 : Fin g → ℂ)] fun y => ‖y - 0‖ ^ 3 := by simpa using hkO
    exact this.eq_zero_of_norm_pow (by norm_num)
  let D : ((Fin g → ℂ) → ℂ) → (Fin 3 → Fin g → ℂ) → ℂ := fun w x =>
    ∑ I : Finset (Fin 3), ((((-1 : ℤ) ^ (3 - I.card) : ℤ)) : ℂ) * w (∑ a ∈ I, x a)
  have hDO : ∀ w : (Fin g → ℂ) → ℂ, w =O[𝓝 0] (fun z => ‖z‖ ^ 3) →
      D w =O[𝓝 0] fun x => ‖x‖ ^ 3 := by
    intro w hw
    have : D w = ∑ I : Finset (Fin 3),
        fun x => ((((-1 : ℤ) ^ (3 - I.card) : ℤ)) : ℂ) * w (S I x) := by
      funext x
      simp [D, hS]
    rw [this]
    exact IsBigO.sum fun I _ => (isBigO_norm_cube_comp_clm hw (S I)).const_mul_left _
  let Gf : (Fin 3 → Fin g → ℂ) → ℂ := fun x => f x - D k x
  have hGO : Gf =O[𝓝 0] fun x => ‖x‖ ^ 3 := hfO.sub (hDO k hkO)
  have ev2 : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F ((2 : ℂ) • x) = cexp (L + f ((2 : ℂ) • x)) :=
    eventually_nhds_zero_comp_of_continuous (T := fun x : Fin 3 → Fin g → ℂ => (2 : ℂ) • x)
      (p := fun y => F y = cexp (L + f y)) (by fun_prop) (smul_zero _) hFexp
  have evn : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F (-x) = cexp (L + f (-x)) :=
    eventually_nhds_zero_comp_of_continuous (T := fun x : Fin 3 → Fin g → ℂ => -x)
      (p := fun y => F y = cexp (L + f y)) (by fun_prop) neg_zero hFexp
  have evI : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), ∀ I : Finset (Fin 3),
      F (M (∑ a ∈ I, x a)) = cexp (L + f (M (∑ a ∈ I, x a))) :=
    Filter.eventually_all.2 fun I => eventually_nhds_zero_comp_of_continuous
      (T := fun x : Fin 3 → Fin g → ℂ => M (∑ a ∈ I, x a))
      (p := fun y => F y = cexp (L + f y))
      (M.continuous.comp (continuous_finset_sum _ fun a _ => continuous_apply a)) (by simp) hFexp
  have evk : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), ∀ I : Finset (Fin 3),
      k ((2 : ℂ) • ∑ a ∈ I, x a) - 3 * k (∑ a ∈ I, x a) - k (-∑ a ∈ I, x a) =
        -φ (∑ a ∈ I, x a) :=
    Filter.eventually_all.2 fun I => eventually_nhds_zero_comp_of_continuous
      (T := fun x : Fin 3 → Fin g → ℂ => ∑ a ∈ I, x a)
      (p := fun z => k ((2 : ℂ) • z) - 3 * k z - k (-z) = -φ z)
      (continuous_finset_sum _ fun a _ => continuous_apply a) (by simp) hkeq
  have hEt : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ),
      ‖f ((2 : ℂ) • x) + D φ x - 3 * f x - f (-x)‖ < 2 * π := by
    have h2x : (fun x : Fin 3 → Fin g → ℂ => f ((2 : ℂ) • x)) =O[𝓝 0] fun x => ‖x‖ ^ 3 := by
      have := isBigO_norm_cube_comp_clm hfO ((2 : ℂ) • ContinuousLinearMap.id ℂ (Fin 3 → Fin g → ℂ))
      simpa only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply] using this
    have hnx : (fun x : Fin 3 → Fin g → ℂ => f (-x)) =O[𝓝 0] fun x => ‖x‖ ^ 3 := by
      have := isBigO_norm_cube_comp_clm hfO (-ContinuousLinearMap.id ℂ (Fin 3 → Fin g → ℂ))
      simpa only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply] using this
    have h3 : (fun x : Fin 3 → Fin g → ℂ => 3 * f x) =O[𝓝 0] fun x => ‖x‖ ^ 3 :=
      hfO.const_mul_left 3
    have hO : (fun x => f ((2 : ℂ) • x) + D φ x - 3 * f x - f (-x)) =O[𝓝 0]
        fun x : Fin 3 → Fin g → ℂ => ‖x‖ ^ 3 :=
      ((h2x.add (hDO φ hφO)).sub h3).sub hnx
    have ht : Tendsto (fun x : Fin 3 → Fin g → ℂ => ‖x‖ ^ 3) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun x : Fin 3 → Fin g → ℂ => ‖x‖ ^ 3 := by fun_prop
      simpa using hc.tendsto 0
    filter_upwards [(hO.trans_tendsto ht).eventually
      (Metric.ball_mem_nhds 0 (by positivity : (0 : ℝ) < 2 * π))] with x hx
    exact mem_ball_zero_iff.1 hx
  have hE : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), f ((2 : ℂ) • x) + D φ x - 3 * f x - f (-x) = 0 := by
    filter_upwards [heq, hFexp, ev2, evn, evI, hEt] with x hx hx1 hx2 hx3 hx4 hx5
    have hprod : ∏ I : Finset (Fin 3),
        F ![∑ a ∈ I, x a, ∑ a ∈ I, x a, -∑ a ∈ I, x a] ^ ((-1 : ℤ) ^ (3 - I.card)) =
          cexp (∑ I : Finset (Fin 3),
            ((((-1 : ℤ) ^ (3 - I.card) : ℤ)) : ℂ) * (L + φ (∑ a ∈ I, x a))) := by
      rw [Complex.exp_sum]
      refine Finset.prod_congr rfl fun I _ => ?_
      rw [Complex.exp_int_mul, ← hM, hx4 I]
    rw [hprod, hx2, hx3, hx1, ← hL'] at hx
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add,
      ← Complex.exp_add] at hx
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 hx
    have hsum : ∑ I : Finset (Fin 3),
        ((((-1 : ℤ) ^ (3 - I.card) : ℤ)) : ℂ) * (L + φ (∑ a ∈ I, x a)) = D φ x := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsign, zero_mul, zero_add, D]
    rw [hsum] at hn
    have hEx : f ((2 : ℂ) • x) + D φ x - 3 * f x - f (-x) = n * (2 * π * Complex.I) := by
      linear_combination hn
    have hn0 : n = 0 := by
      rw [hEx] at hx5
      have h1 : ‖(n : ℂ) * (2 * π * Complex.I)‖ = |(n : ℝ)| * (2 * π) := by
        simp [abs_of_pos Real.pi_pos]
      rw [h1] at hx5
      have h2 : |(n : ℝ)| < 1 := (mul_lt_iff_lt_one_left (by positivity)).1 hx5
      have h3 : |n| < 1 := by exact_mod_cast h2
      exact Int.abs_lt_one_iff.1 h3
    rw [hEx, hn0]
    simp
  have hGeq : ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), Gf ((2 : ℂ) • x) = 3 * Gf x + Gf (-x) := by
    filter_upwards [hE, evk] with x hx hk
    have e1 : ∀ I : Finset (Fin 3), ∑ a ∈ I, ((2 : ℂ) • x) a = (2 : ℂ) • ∑ a ∈ I, x a :=
      fun I => by simp [Finset.smul_sum]
    have e2 : ∀ I : Finset (Fin 3), ∑ a ∈ I, (-x) a = -∑ a ∈ I, x a :=
      fun I => by simp [Finset.sum_neg_distrib]
    have hD : D k ((2 : ℂ) • x) - 3 * D k x - D k (-x) = -D φ x := by
      simp only [D, e1, e2]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
        ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun I _ => ?_
      linear_combination ((((-1 : ℤ) ^ (3 - I.card) : ℤ)) : ℂ) * hk I
    show f ((2 : ℂ) • x) - D k ((2 : ℂ) • x) = 3 * (f x - D k x) + (f (-x) - D k (-x))
    linear_combination hx - hD
  have hG0 := hB (Fin 3 → Fin g → ℂ) Gf hGO hGeq
  refine ⟨k, hka, hk0, ?_⟩
  filter_upwards [hG0, hFexp] with x hx hx1
  have hprod2 : ∏ I : Finset (Fin 3), cexp (k (∑ a ∈ I, x a)) ^ ((-1 : ℤ) ^ (3 - I.card)) =
      cexp (D k x) := by
    simp only [D]
    rw [Complex.exp_sum]
    exact Finset.prod_congr rfl fun I _ => (Complex.exp_int_mul _ _).symm
  rw [hx1, ← hL', hprod2, ← Complex.exp_add]
  have hfx : f x - D k x = 0 := hx
  congr 1
  linear_combination hfx

end GlobalTheory.LocalCube
end

section
open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

theorem exists_localFrame_compatible_cube :
    (∀ (g : ℕ) {ι : Type} (W : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (W i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T : (Finset (Fin 3) → ι) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) * T j' x) → ∀ (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i) → (∀ i j z, ∀ l ∈ Λ, c i j (z + l) = c i j z) → (∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x + l) = T j x) → ∀ (i₀ : ι), 0 ∈ W i₀ → ∀ F : (Fin 3 → Fin g → ℂ) → ℂ, F = T (fun _ => i₀) → (∀ a : Fin 3, ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), x a = 0 → F x = F 0) ∧ (∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F ((2 : ℂ) • x) * (∏ I : Finset (Fin 3), F ![∑ a ∈ I, x a, ∑ a ∈ I, x a, -∑ a ∈ I, x a] ^ ((-1 : ℤ) ^ (3 - I.card))) * F 0 ^ 3 = F x ^ 3 * F (-x))) → (∀ (g : ℕ) (F : (Fin 3 → Fin g → ℂ) → ℂ), AnalyticAt ℂ F 0 → F 0 ≠ 0 → ((∀ a : Fin 3, ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), x a = 0 → F x = F 0) ∧ (∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F ((2 : ℂ) • x) * (∏ I : Finset (Fin 3), F ![∑ a ∈ I, x a, ∑ a ∈ I, x a, -∑ a ∈ I, x a] ^ ((-1 : ℤ) ^ (3 - I.card))) * F 0 ^ 3 = F x ^ 3 * F (-x))) → ∃ k : (Fin g → ℂ) → ℂ, AnalyticAt ℂ k 0 ∧ k 0 = 0 ∧ ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), F x = F 0 * ∏ I : Finset (Fin 3), cexp (k (∑ a ∈ I, x a)) ^ ((-1 : ℤ) ^ (3 - I.card))) → (∀ (g : ℕ) {ι : Type} (W : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (W i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T : (Finset (Fin 3) → ι) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) * T j' x) → ∀ (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i) → (∀ i j z, ∀ l ∈ Λ, c i j (z + l) = c i j z) → (∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x + l) = T j x) → ∃ (r : ℝ) (fr : ι → (Fin g → ℂ) → ℂ) (κ : ℂ), 0 < r ∧ ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩ Metric.ball 0 r)) ∧ (∀ i z, z ∈ W i → z ∈ Metric.ball 0 r → fr i z ≠ 0) ∧ (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Metric.ball 0 r → fr i z = c i j z * fr j z)) ∧ ∀ᶠ x in 𝓝 (0 : Fin 3 → Fin g → ℂ), ∀ j, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) := by
  intro H1 H2 g ι W c hW hcov hcd hc0 hcoc T hTd hT0 hTc Λ hΛd hΛs hWp hcp hTp
  obtain ⟨i₀, hi₀⟩ := hcov 0
  obtain ⟨F, hF⟩ : ∃ F, F = T (fun _ => i₀) := ⟨_, rfl⟩
  let U : Set (Fin 3 → Fin g → ℂ) := {x | ∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W i₀}
  have hUo : IsOpen U := by
    have e : U = ⋂ I : Finset (Fin 3), (fun x : Fin 3 → Fin g → ℂ => ∑ a ∈ I, x a) ⁻¹' W i₀ := by
      ext x
      simp [U]
    rw [e]
    exact isOpen_iInter_of_finite fun I =>
      (hW i₀).preimage (continuous_finsetSum I fun a _ => continuous_apply a)
  have hU0 : (0 : Fin 3 → Fin g → ℂ) ∈ U := fun I => by simpa using hi₀
  have hUn : U ∈ 𝓝 (0 : Fin 3 → Fin g → ℂ) := hUo.mem_nhds hU0
  have hFa : AnalyticAt ℂ F 0 := hF ▸ GlobalTheory.SCV.analyticAt_of_differentiableOn (hTd _) hUn
  have hF0 : F 0 ≠ 0 := hF ▸ hT0 _ 0 hU0
  have hcube := H1 g W c hW hcov hcd hc0 hcoc T hTd hT0 hTc Λ hΛd hΛs hWp hcp hTp i₀ hi₀ F hF
  obtain ⟨k, hka, -, hkF⟩ := H2 g F hFa hF0 hcube
  obtain ⟨ε, hε, hkε⟩ : ∃ ε > 0, ∀ z ∈ Metric.ball (0 : Fin g → ℂ) ε, DifferentiableAt ℂ k z :=
    Metric.eventually_nhds_iff_ball.1 (hka.eventually_analyticAt.mono fun z hz => hz.differentiableAt)
  obtain ⟨δ, hδ, hδW⟩ := Metric.isOpen_iff.1 (hW i₀) 0 hi₀
  have hrW : ∀ z ∈ Metric.ball (0 : Fin g → ℂ) (min ε δ), z ∈ W i₀ := fun z hz =>
    hδW (Metric.ball_subset_ball (min_le_right _ _) hz)
  refine ⟨min ε δ, fun i z => c i i₀ z * cexp (k z), F 0, lt_min hε hδ, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i
    show DifferentiableOn ℂ (fun z => c i i₀ z * cexp (k z)) _
    refine DifferentiableOn.mul ((hcd i i₀).mono ?_) ?_
    · rintro z ⟨hz1, hz2⟩
      exact ⟨hz1, hrW z hz2⟩
    · intro z hz
      exact (hkε z (Metric.ball_subset_ball (min_le_left _ _) hz.2)).cexp.differentiableWithinAt
  · intro i z hz hzr
    exact mul_ne_zero (hc0 i i₀ z hz (hrW z hzr)) (Complex.exp_ne_zero _)
  · intro i j z hzi hzj hzr
    show c i i₀ z * cexp (k z) = c i j z * (c j i₀ z * cexp (k z))
    rw [← mul_assoc, hcoc i j i₀ z hzi hzj (hrW z hzr)]
  · filter_upwards [hkF, hUn] with x hx hxU
    intro j hj
    rw [hTc j (fun _ => i₀) x hj hxU, ← hF, hx]
    simp only [mul_zpow, Finset.prod_mul_distrib]
    ring

end GlobalTheory
end

section
open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

theorem entire_hom_eq_cexp_fderiv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (h : V → ℂ) (hd : Differentiable ℂ h) (h0 : h 0 = 1) (hadd : ∀ y z, h (y + z) = h y * h z)
    (z : V) : h z = cexp (fderiv ℂ h 0 z) := by
  set B : V →L[ℂ] ℂ := fderiv ℂ h 0 with hB
  have hder : ∀ w, HasFDerivAt h (h w • B) w := by
    intro w
    have e : h = fun u => h w * h (u - w) := by
      funext u
      rw [← hadd]; congr 1; abel
    have h1 : HasFDerivAt h B (w - w) := by
      rw [sub_self]; exact (hd 0).hasFDerivAt
    have h2 : HasFDerivAt (fun u => h (u - w)) B w := by
      have := HasFDerivAt.comp (f := fun u => u - w) w h1 ((hasFDerivAt_id w).sub_const w)
      simpa [Function.comp_def] using this
    have h3 := h2.const_mul (h w)
    rw [← e] at h3
    exact h3
  have hφ : ∀ w, HasFDerivAt (fun u => h u * cexp (-(B u))) (0 : V →L[ℂ] ℂ) w := by
    intro w
    have h1 : HasFDerivAt (fun u => cexp (-(B u))) (cexp (-(B w)) • (-B)) w :=
      (B.hasFDerivAt.neg).cexp
    have h2 := (hder w).mul h1
    have e : h w • cexp (-B w) • -B + cexp (-B w) • h w • B = 0 := by
      rw [smul_comm (h w) (cexp (-B w)), smul_neg, smul_neg, neg_add_cancel]
    rw [e] at h2
    exact h2
  have hc := is_const_of_fderiv_eq_zero (𝕜 := ℂ) (f := fun u => h u * cexp (-(B u)))
    (fun w => (hφ w).differentiableAt) (fun w => (hφ w).fderiv) z 0
  simp only [h0, map_zero, neg_zero, Complex.exp_zero, mul_one] at hc
  rw [Complex.exp_neg] at hc
  have := Complex.exp_ne_zero (B z)
  field_simp at hc
  exact hc

theorem clm_eq_of_cexp_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (B C : V →L[ℂ] ℂ) (h : ∀ z, cexp (B z) = cexp (C z)) : B = C := by
  have h1 : HasFDerivAt (fun u => cexp (B u)) (cexp (B 0) • B) 0 := B.hasFDerivAt.cexp
  have h2 : HasFDerivAt (fun u => cexp (C u)) (cexp (C 0) • C) 0 := C.hasFDerivAt.cexp
  have e : (fun u => cexp (B u)) = fun u => cexp (C u) := funext h
  rw [e] at h1
  simpa using h1.unique h2

theorem prod_finset_fin_three {M : Type*} [CommMonoid M] (f : Finset (Fin 3) → M) :
    ∏ I, f I = f ∅ * (f {0} * (f {1} * (f {2} * (f {0, 1} * (f {0, 2} * (f {1, 2} *
      f {0, 1, 2})))))) := by
  have e : (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  rw [e]
  repeat rw [Finset.prod_insert (by decide)]
  rw [Finset.prod_singleton]

theorem automorphyFactor_exp_linear_of_cube :
    (∀ (g : ℕ) {ι : Type} (W : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (W i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T : (Finset (Fin 3) → ι) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) * T j' x) → ∀ (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i) → (∀ i j z, ∀ l ∈ Λ, c i j (z + l) = c i j z) → (∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x + l) = T j x) → ∀ (fr : ι → (Fin g → ℂ) → ℂ) (κ : ℂ), ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩ Set.univ)) ∧ (∀ i z, z ∈ W i → z ∈ Set.univ → fr i z ≠ 0) ∧ (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Set.univ → fr i z = c i j z * fr j z)) → (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) → ∃ (a : Λ → ℂ) (B : Λ →+ ((Fin g → ℂ) →ₗ[ℂ] ℂ)), (∀ l, a l ≠ 0) ∧ (∀ l m : Λ, a (l + m) = a l * a m * cexp (B l m)) ∧ ∀ (l : Λ) i z, z ∈ W i → fr i z = a l * cexp (B l z) * fr i (z + l)) := by
  intro g ι W c hWo hcov _ _ _ T _ hT0 _ Λ _ _ hWp hcp hTp fr κ ⟨hfd, hf0, hfc⟩ hcube
  choose σ hσ using hcov
  have hf0' : ∀ i z, z ∈ W i → fr i z ≠ 0 := fun i z hz => hf0 i z hz (Set.mem_univ _)
  have hfa : ∀ i z, z ∈ W i → DifferentiableAt ℂ (fr i) z := fun i z hz => by
    have := hfd i
    rw [Set.inter_univ] at this
    exact this.differentiableAt ((hWo i).mem_nhds hz)
  let α : Λ → (Fin g → ℂ) → ℂ := fun l z => fr (σ z) z / fr (σ z) (z + l)
  have hα : ∀ (l : Λ) i z, z ∈ W i → α l z = fr i z / fr i (z + l) := by
    intro l i z hz
    have hzl : z + l ∈ W i := (hWp i z l l.2).2 hz
    have hzl' : z + l ∈ W (σ z) := (hWp _ z l l.2).2 (hσ z)
    have e1 := hfc (σ z) i z (hσ z) hz (Set.mem_univ _)
    have e2 := hfc (σ z) i (z + l) hzl' hzl (Set.mem_univ _)
    rw [hcp _ _ z l l.2] at e2
    have hc0 : c (σ z) i z ≠ 0 := by
      intro h
      rw [h, zero_mul] at e1
      exact hf0' _ _ (hσ z) e1
    show fr (σ z) z / fr (σ z) (z + l) = _
    rw [e1, e2, mul_div_mul_left _ _ hc0]
  have hα0 : ∀ (l : Λ) z, α l z ≠ 0 := fun l z =>
    div_ne_zero (hf0' _ _ (hσ z)) (hf0' _ _ ((hWp _ z l l.2).2 (hσ z)))
  have hαd : ∀ l : Λ, Differentiable ℂ (α l) := by
    intro l z
    have hzl' : z + l ∈ W (σ z) := (hWp _ z l l.2).2 (hσ z)
    have h1 : DifferentiableAt ℂ (fun w => fr (σ z) (w + l)) z :=
      (hfa _ _ hzl').comp z (differentiableAt_id.add_const _)
    have h2 : DifferentiableAt ℂ (fun w => fr (σ z) w / fr (σ z) (w + l)) z := by
      simp only [div_eq_mul_inv]
      exact (hfa _ _ (hσ z)).mul (h1.inv (hf0' _ _ hzl'))
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [(hWo (σ z)).mem_nhds (hσ z)] with w hw
    exact hα l _ w hw
  have hαc : ∀ (l m : Λ) z, α (l + m) z = α l z * α m (z + l) := by
    intro l m z
    have hzl' : z + l ∈ W (σ z) := (hWp _ z l l.2).2 (hσ z)
    rw [hα (l + m) _ z (hσ z), hα l _ z (hσ z), hα m _ (z + l) hzl', Submodule.coe_add,
      ← add_assoc]
    have := hf0' _ _ hzl'
    field_simp
  have hcubeα : ∀ (l : Λ) y z, α l (y + z) * α l 0 = α l y * α l z := by
    intro l y z
    let x : Fin 3 → Fin g → ℂ := ![0, y, z]
    let L : Fin 3 → Fin g → ℂ := ![l, 0, 0]
    have hL : ∀ a, L a ∈ Λ := by
      intro a
      fin_cases a
      · exact l.2
      · exact Λ.zero_mem
      · exact Λ.zero_mem
    let j : Finset (Fin 3) → ι := fun I => σ (∑ a ∈ I, x a)
    have hj : ∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I) := fun I => hσ _
    have hs : ∀ I : Finset (Fin 3), ∑ a ∈ I, (x + L) a = ∑ a ∈ I, x a + ∑ a ∈ I, L a := by
      intro I
      simp only [Pi.add_apply, Finset.sum_add_distrib]
    have hj' : ∀ I : Finset (Fin 3), ∑ a ∈ I, (x + L) a ∈ W (j I) := by
      intro I
      rw [hs]
      exact (hWp _ _ _ (Λ.sum_mem fun a _ => hL a)).2 (hj I)
    have e1 := hcube j x hj
    have e2 := hcube j (x + L) hj'
    have hκ : κ ≠ 0 := by
      intro h
      rw [h, zero_mul] at e1
      exact hT0 j x hj e1
    rw [hTp j x L hL, e1] at e2
    have e3 := mul_left_cancel₀ hκ e2
    have e4 : ∏ I : Finset (Fin 3), (fr (j I) (∑ a ∈ I, x a) /
        fr (j I) (∑ a ∈ I, x a + ∑ a ∈ I, L a)) ^ ((-1 : ℤ) ^ (3 - I.card)) = 1 := by
      simp only [div_zpow, Finset.prod_div_distrib]
      simp only [hs] at e3
      rw [← e3]
      exact div_self (Finset.prod_ne_zero_iff.2 fun I _ => zpow_ne_zero _ (hf0' _ _ (hj I)))
    have hz : ∀ (m : Λ) w, (m : Fin g → ℂ) = 0 → α m w = 1 := by
      intro m w hm
      show fr (σ w) w / fr (σ w) (w + m) = 1
      rw [hm, add_zero]
      exact div_self (hf0' _ _ (hσ w))
    have hl : ∀ (m : Λ) w w', (m : Fin g → ℂ) = l → w = w' → α m w = α l w' := by
      intro m w w' hm hw
      rw [Subtype.ext hm, hw]
    let F : Finset (Fin 3) → ℂ := fun I =>
      α ⟨∑ a ∈ I, L a, Λ.sum_mem fun a _ => hL a⟩ (∑ a ∈ I, x a)
    have e6 : ∏ I : Finset (Fin 3), F I ^ ((-1 : ℤ) ^ (3 - I.card)) = 1 := e4
    have f0 : F ∅ = 1 := hz _ _ (by simp)
    have f1 : F {0} = α l 0 := hl _ _ _ (by simp [L]) (by simp [x])
    have f2 : F {1} = 1 := hz _ _ (by simp [L])
    have f3 : F {2} = 1 := hz _ _ (by simp [L])
    have f4 : F {0, 1} = α l y := hl _ _ _ (by simp [L]) (by simp [x])
    have f5 : F {0, 2} = α l z := hl _ _ _ (by simp [L]) (by simp [x])
    have f6 : F {1, 2} = 1 := hz _ _ (by simp [L])
    have f7 : F {0, 1, 2} = α l (y + z) := hl _ _ _ (by simp [L]) (by simp [x])
    clear e4
    have e4 := e6
    rw [prod_finset_fin_three, f0, f1, f2, f3, f4, f5, f6, f7] at e4
    have c1 : ({0} : Finset (Fin 3)).card = 1 := rfl
    have c2 : ({0, 1} : Finset (Fin 3)).card = 2 := rfl
    have c3 : ({0, 2} : Finset (Fin 3)).card = 2 := rfl
    have c4 : ({0, 1, 2} : Finset (Fin 3)).card = 3 := rfl
    rw [c1, c2, c3, c4] at e4
    norm_num at e4
    have := hα0 l y
    have := hα0 l z
    field_simp at e4
    linear_combination e4
  let B₀ : Λ → ((Fin g → ℂ) →L[ℂ] ℂ) := fun l => fderiv ℂ (fun z => α l z / α l 0) 0
  have hexp : ∀ (l : Λ) z, α l z = α l 0 * cexp (B₀ l z) := by
    intro l z
    have h0 := hα0 l 0
    have := entire_hom_eq_cexp_fderiv (fun z => α l z / α l 0)
      (by simp only [div_eq_mul_inv]; exact (hαd l).mul_const _)
      (div_self h0) (fun y z => by
        have := hcubeα l y z
        field_simp
        linear_combination this) z
    show _ = _ * cexp (fderiv ℂ (fun z => α l z / α l 0) 0 z)
    rw [← this]
    field_simp
  have ha : ∀ l m : Λ, α (l + m) 0 = α l 0 * α m 0 * cexp (B₀ l m) := by
    intro l m
    rw [add_comm, hαc, zero_add, hexp l m]
    ring
  have hBadd : ∀ l m : Λ, B₀ (l + m) = B₀ l + B₀ m := by
    intro l m
    apply clm_eq_of_cexp_eq
    intro z
    have e := hαc m l z
    rw [add_comm m l, hexp (l + m), hexp m, hexp l, ha, map_add, Complex.exp_add] at e
    rw [ContinuousLinearMap.add_apply, Complex.exp_add]
    have h1 : α l 0 * α m 0 * cexp (B₀ l m) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (hα0 _ _) (hα0 _ _)) (Complex.exp_ne_zero _)
    apply mul_left_cancel₀ h1
    linear_combination e
  refine ⟨fun l => α l 0, AddMonoidHom.mk' (fun l => (B₀ l).toLinearMap) ?_, fun l => hα0 l 0,
    ha, ?_⟩
  · intro l m
    rw [hBadd]; rfl
  · intro l i z hz
    have e := hexp l z
    rw [hα l i z hz, div_eq_iff (hf0' _ _ ((hWp _ z l l.2).2 hz))] at e
    exact e

end GlobalTheory
end

section
open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

theorem bilinForm_bijective_of_nondegenerate_mod (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (E : LinearMap.BilinForm ℤ X)
    (h : ∀ (k : ℕ) (a : X), 0 < k → (∀ b, (k : ℤ) ∣ E a b) → ∃ a', a = (k : ℤ) • a') :
    Function.Bijective E := by
  classical
  set b := Module.Free.chooseBasis ℤ X
  have hinj : Function.Injective E := by
    refine (injective_iff_map_eq_zero E).2 fun a ha => ?_
    refine b.ext_elem fun i => ?_
    obtain ⟨n, hn⟩ : ∃ n, (b.repr a i).natAbs = n := ⟨_, rfl⟩
    obtain ⟨a', ha'⟩ := h (n + 1) a (Nat.succ_pos n) (fun y => by rw [ha]; simp)
    have hdvd : ((n + 1 : ℕ) : ℤ) ∣ b.repr a i := ⟨b.repr a' i, by rw [ha']; simp⟩
    rw [map_zero, Finsupp.zero_apply]
    refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd ?_
    rw [Int.natAbs_natCast, hn]
    exact Nat.lt_succ_self n
  have hrank : Module.rank ℤ (Module.Dual ℤ X ⧸ LinearMap.range E) = 0 := by
    have h1 := rank_quotient_add_rank_of_isDomain (LinearMap.range E)
    rw [← (LinearEquiv.ofInjective E hinj).rank_eq, ← b.toDualEquiv.rank_eq] at h1
    obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.1 (Module.rank_lt_aleph0 ℤ X)
    have hq : Module.rank ℤ (Module.Dual ℤ X ⧸ LinearMap.range E) < Cardinal.aleph0 :=
      lt_of_le_of_lt (le_self_add) (h1 ▸ Module.rank_lt_aleph0 ℤ X)
    obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.1 hq
    rw [hm, hn] at h1
    rw [hm]
    have : m + n = n := by exact_mod_cast h1
    exact_mod_cast (by omega : m = 0)
  refine ⟨hinj, fun f => ?_⟩
  obtain ⟨c, hc0, hcf⟩ := rank_eq_zero_iff.1 hrank (Submodule.Quotient.mk f)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hcf
  obtain ⟨x, hx⟩ := hcf
  have hk : 0 < c.natAbs * c.natAbs := Nat.mul_pos (Int.natAbs_pos.2 hc0) (Int.natAbs_pos.2 hc0)
  obtain ⟨a', ha'⟩ := h (c.natAbs * c.natAbs) (c • x) hk (fun y => by
    rw [Int.natAbs_mul_self, map_smul, hx, smul_smul]
    simp)
  refine ⟨a', ?_⟩
  have hEq : E (c • x) = ((c.natAbs * c.natAbs : ℕ) : ℤ) • f := by
    rw [Int.natAbs_mul_self, map_smul, hx, smul_smul]
  rw [ha', map_smul] at hEq
  ext y
  have hy := LinearMap.congr_fun hEq y
  simp only [LinearMap.smul_apply, smul_eq_mul] at hy
  exact mul_left_cancel₀ (by exact_mod_cast hk.ne') hy

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

namespace OriginFrame

def ValRules : Prop :=
  ∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)

theorem rigVal_ne_zero (hv : ValRules) {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (s : Γ(X, U)ˣ) : valAt' x U s.val ≠ 0 := by
  intro h0
  obtain ⟨e, he⟩ := (hv X x).2.1 U h
  have key := congrArg e s.val_inv
  rw [map_mul, map_one, ← he, h0, zero_mul] at key
  exact zero_ne_one key

theorem rigChart_iff {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (L : LB X) (j : (L.pull x).ι) :
    ⊤ ≤ (L.pull x).U j ↔ ⊤ ≤ x ⁻¹ᵁ L.U (j PUnit.unit) := by
  delta LB.pull LB.LinComb LB.wchart
  constructor
  · intro h p _
    exact Set.mem_iInter.mp (h trivial) PUnit.unit
  · intro h p hp
    exact Set.mem_iInter.mpr (fun k => by cases k; exact h hp)

theorem rigVal_compat (hv : ValRules) {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (L : LB X)
    (rig : LB.Gen (L.pull x)) (hr : rig.IsGen) (j j' : (L.pull x).ι)
    (hj : ⊤ ≤ (L.pull x).U j) (hj' : ⊤ ≤ (L.pull x).U j') :
    valAt' (𝟙 (Sp ℂ)) ((L.pull x).U j) (rig.s j).val =
      valAt' x (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) (L.g (j PUnit.unit) (j' PUnit.unit)).val *
        valAt' (𝟙 (Sp ℂ)) ((L.pull x).U j') (rig.s j').val := by
  unfold LB.Gen.IsGen at hr
  obtain ⟨hle, hg⟩ : ∃ hle : (L.pull x).U j ⊓ (L.pull x).U j' ≤ x ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)),
      (L.pull x).g j j' = res hle (pullU x _ (L.g (j PUnit.unit) (j' PUnit.unit))) := by
    delta LB.pull LB.LinComb
    dsimp only
    rw [Fintype.prod_unique, zpow_one]
    exact ⟨_, rfl⟩
  have hJ : ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ ((L.pull x).U j ⊓ (L.pull x).U j') := by
    exact le_inf hj hj'
  obtain ⟨e, he⟩ := (hv (Sp ℂ) (𝟙 _)).2.1 _ hJ
  have hrj := congrArg (fun u => e (Units.val u)) (hr j j')
  rw [hg] at hrj
  rw [Units.val_mul, map_mul] at hrj
  simp only [← he] at hrj
  have eres : ∀ {U W : (Sp ℂ).Opens} (hh : W ≤ U) (u : (Γ(Sp ℂ, U))ˣ),
      ((res hh u : (Γ(Sp ℂ, W))ˣ) : Γ(Sp ℂ, W)) = resG (Sp ℂ) hh (u : Γ(Sp ℂ, U)) := fun _ _ => rfl
  have epu : ∀ (W : X.Opens) (u : (Γ(X, W))ˣ),
      ((pullU x W u : (Γ(Sp ℂ, x ⁻¹ᵁ W))ˣ) : Γ(Sp ℂ, x ⁻¹ᵁ W)) = (x.app W).hom (u : Γ(X, W)) := fun _ _ => rfl
  have r3 := fun U h f => (hv (Sp ℂ) (𝟙 (Sp ℂ))).2.2.1 U ((L.pull x).U j ⊓ (L.pull x).U j') h f hJ
  simp only [eres, epu, r3] at hrj
  rw [(hv (Sp ℂ) (𝟙 _)).2.2.2.1 X x, Category.id_comp] at hrj
  exact hrj

end OriginFrame

open OriginFrame in

theorem exists_appellHumbert_frame_isRig :
    Out.CubeSt → (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default
        : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X,
        U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X,
        U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ
        : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫
        φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X,
        U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U
        : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (A : Over (Sp
        ℂ)) [GrpObj A] [IsCommMonObj A] (L₀ L : LB A.left) (g : ℕ) (u
        : HolUnif A L₀ g), L.IsLB → ∀ t : LB.Gen (Theta A L), t.IsGen → ∀ (W : L.ι → Set (Fin g →
        ℂ)) (c : L.ι → L.ι → (Fin g → ℂ) → ℂ), W = (fun (i : L.ι) => {z : Fin g → ℂ | ⊤ ≤ (u.ex
        z).left ⁻¹ᵁ L.U i}) → c = (fun (i j : L.ι) (z : Fin g → ℂ) => valAt' (u.ex z).left (L.U i ⊓
        L.U j) (L.g i j).val) → ((∀ i, IsOpen (W i)) ∧ (∀ z, ∃ i, z ∈ W i) ∧
        (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j)) ∧ (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0)
        ∧ (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) ∧
        (∀ i z, ∀ l ∈ u.Λ, z + l ∈ W i ↔ z ∈ W i) ∧ (∀ i j z, ∀ l ∈ u.Λ, c i j (z +
        l) = c i j z)) ∧ ∃ T : (Finset (Fin 3) → L.ι) → (Fin 3 → Fin g →
        ℂ) → ℂ, (∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j
        I))}) ∧ (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j
        I)) → T j x ≠ 0) ∧ (∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j
        I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) → T j x = (∏ I : Finset (Fin 3), c (j
        I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) * T j' x) ∧ (∀ j x (l
        : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ u.Λ) → T j (x + l) = T j x)) → (∀ (g : ℕ) {J : Type} (W
        : J → Set (Fin g → ℂ)) (c : J → J → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (W
        i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W
        j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T
        : (Finset (Fin 3) → J) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x
        | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin
        3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin
        3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j'
        I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 -
        I.card))) * T j' x) → ∀ (Λ : Submodule ℤ (Fin g →
        ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g →
        ℂ)) = ⊤ → (∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i) → (∀ i j z, ∀ l ∈ Λ, c i j (z +
        l) = c i j z) → (∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x + l) = T j x) → ∃ (r
        : ℝ) (fr : J → (Fin g → ℂ) → ℂ) (κ : ℂ), 0 < r ∧ ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩
        Metric.ball 0 r)) ∧ (∀ i z, z ∈ W i → z ∈ Metric.ball 0 r → fr i z ≠ 0) ∧
        (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Metric.ball 0 r → fr i z = c i j z * fr j z)) ∧ ∀ᶠ x in 𝓝 (0
        : Fin 3 → Fin g → ℂ), ∀ j, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j
        I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 -
        I.card))) → (∀ (g : ℕ) {J : Type} (W : J → Set (Fin g → ℂ)) (c : J → J → (Fin g →
        ℂ) → ℂ), (∀ i, IsOpen (W i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i
        ∩ W
        j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T
        : (Finset (Fin 3) → J) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x
        | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin
        3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin
        3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j'
        I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 -
        I.card))) * T j' x) → (∃ (r : ℝ) (fr : J → (Fin g → ℂ) → ℂ) (κ
        : ℂ), 0 < r ∧ ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩ Metric.ball 0 r)) ∧
        (∀ i z, z ∈ W i → z ∈ Metric.ball 0 r → fr i z ≠ 0) ∧
        (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Metric.ball 0 r → fr i z = c i j z * fr j z)) ∧ ∀ᶠ x in 𝓝 (0
        : Fin 3 → Fin g → ℂ), ∀ j, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j
        I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 -
        I.card))) → ∃ (fr : J → (Fin g → ℂ) → ℂ) (κ : ℂ), ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩
        Set.univ)) ∧ (∀ i z, z ∈ W i → z ∈ Set.univ → fr i z ≠ 0) ∧
        (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Set.univ → fr i z = c i j z * fr j z)) ∧ ∀ j x, (∀ I : Finset (Fin
        3), ∑ a ∈ I, x a ∈ W (j I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j
        I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) → (∀ (g : ℕ) {J : Type} (W : J → Set (Fin g →
        ℂ)) (c : J → J → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (W
        i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W
        j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T
        : (Finset (Fin 3) → J) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x
        | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin
        3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin
        3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j'
        I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 -
        I.card))) * T j' x) → ∀ (Λ : Submodule ℤ (Fin g →
        ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g →
        ℂ)) = ⊤ → (∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i) → (∀ i j z, ∀ l ∈ Λ, c i j (z +
        l) = c i j z) → (∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x +
        l) = T j x) → ∀ (fr : J → (Fin g → ℂ) → ℂ) (κ : ℂ), ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩
        Set.univ)) ∧ (∀ i z, z ∈ W i → z ∈ Set.univ → fr i z ≠ 0) ∧
        (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Set.univ → fr i z = c i j z * fr j z)) → (∀ j x, (∀ I : Finset (Fin
        3), ∑ a ∈ I, x a ∈ W (j I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j
        I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) → ∃ (a : Λ → ℂ) (B : Λ →+ ((Fin g → ℂ) →ₗ[ℂ]
        ℂ)), (∀ l, a l ≠ 0) ∧ (∀ l m : Λ, a (l + m) = a l * a m * cexp (B l m)) ∧ ∀ (l
        : Λ) i z, z ∈ W i → fr i z = a l * cexp (B l z) * fr i (z + l)) → (∀ (g : ℕ) (Λ
        : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g →
        ℂ)) = ⊤ → ∀ (a : Λ → ℂ) (B : Λ →+ ((Fin g → ℂ) →ₗ[ℂ] ℂ)), (∀ l, a l ≠ 0) → (∀ l m : Λ, a (l
        + m) = a l * a m * cexp (B l m)) → ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef
        : LinearMap.BilinForm ℤ Λ) (Q : (Fin g →
        ℂ) → ℂ), Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ
        Hm.mulVec (star (m : Fin g → ℂ))).im) ∧ Differentiable ℂ Q ∧ Q 0 = 0 ∧ ∀ (l
        : Λ) z, a l * cexp (B l z) * cexp (Q z - Q (z + l)) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec
        (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l
        : Fin g → ℂ)))))) → (∀ (P : Out.PolAV (Sp ℂ)) (rig : LB.Gen (P.L.pull (eSec
        P.A))), rig.IsGen → ∀ u₀ : HolUnif P.A (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩
        : LB P.A.left) P.g, ∃ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ
        : u.Λ → ℂ) (Ef
        : LinearMap.BilinForm ℤ u.Λ), u.ex = u₀.ex ∧ u.IsRig rig ∧ Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef
        l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l
        : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ
        Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l
        : Fin P.g → ℂ))))) * u.fr i (z + l)) := by
  intro hCube hV hFrame hLoc hGlob hFact hNorm P rig hrig u₀
  have hLB : P.L.IsLB := P.7
  obtain ⟨cs⟩ := (hCube (Sp ℂ) P ⟨P.L, rig, hLB, hrig⟩ rfl).1
  obtain ⟨W, hW⟩ : ∃ W : P.L.ι → Set (Fin P.g → ℂ),
      W = fun i => {z | ⊤ ≤ (u₀.ex z).left ⁻¹ᵁ P.L.U i} := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : P.L.ι → P.L.ι → (Fin P.g → ℂ) → ℂ,
      c = fun i j z => valAt' (u₀.ex z).left (P.L.U i ⊓ P.L.U j) (P.L.g i j).val := ⟨_, rfl⟩
  have memW : ∀ i z, z ∈ W i ↔ ⊤ ≤ (u₀.ex z).left ⁻¹ᵁ P.L.U i := by
    intro i z
    rw [hW]
    exact Iff.rfl
  obtain ⟨⟨hWo, hWc, hcd, hcn, hcc, hWp, hcp⟩, T, hT1, hT2, hT3, hT4⟩ :=
    hFrame P.A _ P.L P.g u₀ hLB cs.t cs.2 W c hW hc
  have hloc := hLoc P.g W c hWo hWc hcd hcn hcc T hT1 hT2 hT3 u₀.Λ u₀.discrete u₀.full hWp hcp hT4
  obtain ⟨fr, κ, ⟨hfrd, hfrn, hfrc⟩, hTfr⟩ := hGlob P.g W c hWo hWc hcd hcn hcc T hT1 hT2 hT3 hloc
  obtain ⟨a, B, ha, hab, hfa⟩ :=
    hFact P.g W c hWo hWc hcd hcn hcc T hT1 hT2 hT3 u₀.Λ u₀.discrete u₀.full hWp hcp hT4 fr κ
      ⟨hfrd, hfrn, hfrc⟩ hTfr
  obtain ⟨Hm, χ, Ef, Q, hH, hχ, hEf, hQd, _, hQ⟩ := hNorm P.g u₀.Λ u₀.discrete u₀.full a B ha hab

  have hex0 : u₀.ex 0 = 1 := (u₀.ker 0).2 (Submodule.zero_mem _)
  have he0 : (u₀.ex 0).left = eSec P.A := by
    simp only [hex0, CategoryTheory.Hom.one_def, toUnit_unit, Category.id_comp]
    rfl
  obtain ⟨i₀, h₀⟩ := hWc 0
  have hjj : ⊤ ≤ (P.L.pull (eSec P.A)).U (fun _ => i₀ : PUnit.{1} → P.L.ι) :=
    (OriginFrame.rigChart_iff (eSec P.A) P.L (fun _ => i₀ : PUnit.{1} → P.L.ι)).2 (by rw [← he0]; exact (memW _ _).1 h₀)
  have hjj' : ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ (P.L.pull (eSec P.A)).U (fun _ => i₀ : PUnit.{1} → P.L.ι) := by
    exact hjj
  have hvne := OriginFrame.rigVal_ne_zero hV (𝟙 (Sp ℂ)) _ hjj' (rig.s (fun _ => i₀ : PUnit.{1} → P.L.ι))
  clear hFrame hLoc hGlob hFact hNorm hCube hT1 hT2 hT3 hT4 hloc hTfr hcd hcn hcc hWp hcp hWo hWc hab
  have hF : fr i₀ 0 * Complex.exp (Q 0) ≠ 0 := mul_ne_zero (hfrn i₀ 0 h₀ trivial) (Complex.exp_ne_zero _)
  have hlam : valAt' (𝟙 (Sp ℂ)) ((P.L.pull (eSec P.A)).U (fun _ => i₀ : PUnit.{1} → P.L.ι)) (rig.s (fun _ => i₀ : PUnit.{1} → P.L.ι)).val /
      (fr i₀ 0 * Complex.exp (Q 0)) ≠ 0 := div_ne_zero hvne hF
  refine ⟨{
      ex := u₀.ex
      ex_add := u₀.ex_add
      ex_onto := u₀.ex_onto
      Λ := u₀.Λ
      ker := u₀.ker
      discrete := u₀.discrete
      full := u₀.full
      hol := u₀.hol
      fr := fun i z => valAt' (𝟙 (Sp ℂ)) ((P.L.pull (eSec P.A)).U (fun _ => i₀ : PUnit.{1} → P.L.ι)) (rig.s (fun _ => i₀ : PUnit.{1} → P.L.ι)).val /
        (fr i₀ 0 * Complex.exp (Q 0)) * (fr i z * Complex.exp (Q z))
      fr_hol := ?_
      fr_ne := ?_
      fr_compat := ?_ }, Hm, χ, Ef, rfl, ?_, hH, hχ, hEf, ?_⟩
  · intro i
    refine (((hfrd i).mono fun z hz => ⟨(memW i z).2 hz, trivial⟩).mul
      hQd.cexp.differentiableOn).const_mul _
  · intro i z hz
    exact mul_ne_zero hlam (mul_ne_zero (hfrn i z ((memW i z).2 hz) trivial) (Complex.exp_ne_zero _))
  · intro i j z hz
    have hp := ((hV _ (u₀.ex z).left).1 _).1 hz
    have hzi : z ∈ W i := (memW i z).2 (((hV _ _).1 _).2 hp.1)
    have hzj : z ∈ W j := (memW j z).2 (((hV _ _).1 _).2 hp.2)
    have h1 := hfrc i j z hzi hzj trivial
    rw [hc] at h1
    dsimp only at h1 ⊢
    rw [h1]
    ring
  · intro j hj
    have hj0 : 0 ∈ W (j PUnit.unit) :=
      (memW _ _).2 (by rw [he0]; exact (OriginFrame.rigChart_iff (eSec P.A) P.L j).1 hj)
    have hcomp := OriginFrame.rigVal_compat hV (eSec P.A) P.L rig hrig j (fun _ => i₀ : PUnit.{1} → P.L.ι) hj hjj
    have hfc := hfrc (j PUnit.unit) i₀ 0 hj0 h₀ trivial
    rw [hc] at hfc
    dsimp only at hfc ⊢
    rw [hcomp, hfc, he0, div_mul_eq_mul_div, div_eq_iff hF]
    ring
  · intro l i z hz
    have hzW : z ∈ W i := (memW i z).2 hz
    dsimp only at hz ⊢
    have hE := Complex.exp_ne_zero (Q (z + l))
    rw [← hQ l z, hfa l i z hzW, Complex.exp_sub]
    field_simp

end GlobalTheory
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

def thetaZeroSec {X : Scheme.{0}} (L : LB X) : L.Sec where
  f _ := 0
  compat := by intros; simp

theorem valAt'_zero_fn {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) : valAt' x U 0 = 0 := by
  unfold valAt'
  split_ifs with h
  · simp [valAt]
  · rfl

theorem isAH_of_polarisation :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ) (θ : (Fin g → ℂ) → ℂ), Hm.IsHermitian → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) → Function.Injective Ef → Differentiable ℂ θ → θ ≠ 0 → (∀ (l : Λ) z, θ (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z) → ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ (P : Out.PolAV (Sp ℂ)) (n : ℕ), 1 ≤ n → ∃ s : Fin (n ^ P.g) → (lbPow P.L n).Sec, ∀ a : Fin (n ^ P.g) → ℂ, (∀ j, ∑ i, constFn P.A.hom _ (a i) * (s i).f j = 0) → a = 0) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧ ∀ θ s s', u.IsFnPow n s θ → u.IsFnPow n s' θ → s = s') → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → Function.Bijective Ef → u.IsAH Hm χ) := by
  intro _ hpos hsec hthe P u Hm χ Ef hAH hbij
  obtain ⟨hH, hχ, hE, hfr⟩ := hAH
  refine ⟨hH, ?_, hχ, hfr⟩

  obtain ⟨s, hs⟩ := hsec P 1 le_rfl
  have hone : ∀ i j : Fin (1 ^ P.g), i = j := fun i j =>
    Fin.ext (by
      have hi : (i : ℕ) < 1 := lt_of_lt_of_eq i.isLt (one_pow _)
      have hj : (j : ℕ) < 1 := lt_of_lt_of_eq j.isLt (one_pow _)
      omega)
  let i0 : Fin (1 ^ P.g) := ⟨0, by rw [one_pow]; exact Nat.one_pos⟩
  have hcorr := hthe P u Hm χ Ef ⟨hH, hχ, hE, hfr⟩ 1
  obtain ⟨θ, ⟨hθ, hfn⟩, -⟩ := hcorr.1 (s i0)

  have hθne : θ ≠ 0 := by
    rintro rfl
    have hz : u.IsFnPow 1 (thetaZeroSec (lbPow P.L 1)) 0 := by
      intro j z _
      rw [Pi.zero_apply, zero_mul]
      exact valAt'_zero_fn _ _
    have hs0 : s i0 = thetaZeroSec (lbPow P.L 1) := hcorr.2 0 _ _ hfn hz
    have hall : ∀ i, s i = thetaZeroSec (lbPow P.L 1) := fun i => by rw [hone i i0, hs0]
    have h1 := hs (fun _ => 1) (fun j => Finset.sum_eq_zero (fun i _ => by rw [hall i]; exact mul_zero _))
    exact absurd (congrFun h1 i0) (by simp)

  exact hpos P.g u.Λ u.discrete u.full Hm χ Ef θ hH hχ hE hbij.1 hθ.1 hθne
    (fun l z => by have h := hθ.2 l z; rw [pow_one] at h; exact h)

end GlobalTheory
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

theorem thetaUnifAV_of_parts :
    (∀ P : Out.PolAV (Sp ℂ), ∃ u : HolUnif P.A (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩
        : LB P.A.left) P.g, (∃ (U : P.A.left.Opens) (t : Fin P.g → Γ(P.A.left,
        U)), IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U ∧ (∀ D : Γ(P.A.left, U) →+ ℂ, (∀ a, D (constFn
        P.A.hom U a) = 0) → (∀ f f', D (f * f') = valAt' (u.ex 0).left U f * D f' + valAt' (u.ex
        0).left U f' * D f) → (∀ i, D (t i) = 0) → D = 0) ∧ HasFDerivAt (fun w i => valAt' (u.ex
        w).left U (t i)) (ContinuousLinearMap.id ℂ (Fin P.g → ℂ)) 0) ∧ (∀ (n : ℕ) (a : (Fin n →
        ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), (∀ (U : (P.A).left.Opens) (f : Γ((P.A).left, U)), IsOpen {w
        | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a
        w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ (Set.univ
        : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → a 0 = 1 → ∃ G : (Fin n → ℂ) → (Fin P.g →
        ℂ), G 0 = 0 ∧ AnalyticAt ℂ G 0 ∧ ∀ᶠ w in 𝓝 0, u.ex (G w) = a w)) → (∀ (A : Over (Sp
        ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), (∃ (U : A.left.Opens) (t
        : Fin g → Γ(A.left, U)), IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U ∧ (∀ D : Γ(A.left,
        U) →+ ℂ, (∀ a, D (constFn A.hom U a) = 0) → (∀ f f', D (f * f') = valAt' (u.ex
        0).left U f * D f' + valAt' (u.ex 0).left U f' * D f) → (∀ i, D (t
        i) = 0) → D = 0) ∧ HasFDerivAt (fun w i => valAt' (u.ex w).left U (t
        i)) (ContinuousLinearMap.id ℂ (Fin g →
        ℂ)) 0) → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v)) → (∀ (A
        : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), (∀ (n : ℕ) (a : (Fin
        n → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)), (∀ (U : (A).left.Opens) (f : Γ((A).left, U)), IsOpen {w
        | w ∈ (Set.univ : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a
        w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ (Set.univ
        : Set (Fin n → ℂ)) ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → a 0 = 1 → ∃ G : (Fin n → ℂ) → (Fin g →
        ℂ), G 0 = 0 ∧ AnalyticAt ℂ G 0 ∧ ∀ᶠ w in 𝓝 0, u.ex (G
        w) = a w) → ∀ f : A ⟶ A, IsMonHom f → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, u.ex (F
        z) = u.ex z ≫ f) → (∀ (P : Out.PolAV (Sp ℂ)) (rig : LB.Gen (P.L.pull (eSec
        P.A))), rig.IsGen → ∀ u₀ : HolUnif P.A (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩
        : LB P.A.left) P.g, ∃ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ
        : u.Λ → ℂ) (Ef
        : LinearMap.BilinForm ℤ u.Λ), u.ex = u₀.ex ∧ u.IsRig rig ∧ Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef
        l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l
        : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ
        Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l
        : Fin P.g → ℂ))))) * u.fr i (z + l)) → (∀ (P : Out.PolAV (Sp ℂ)) (u
        : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef
        : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m
        : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l
        : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ
        Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l
        : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k → (c
        : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) /
        k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b
        : Fin P.g → ℂ))) (unitOn c)) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm
        : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef
        : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m
        : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l
        : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ
        Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l
        : Fin P.g → ℂ))))) * u.fr i (z + l)) → Function.Bijective Ef) → (∀ (P : Out.PolAV (Sp ℂ)) (u
        : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef
        : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m
        : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l
        : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ
        Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l
        : Fin P.g → ℂ))))) * u.fr i (z +
        l)) → ∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧ ∀ θ s s', u.IsFnPow n s θ → u.IsFnPow n s' θ → s = s') → (∀ (P
        : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ
        : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), u.IsAH Hm χ → (Hm.IsHermitian ∧
        (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m
        : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l *
        cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ)
        ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → Function.Bijective Ef → ∀ (n
        : ℕ) θ, u.IsThetaFn Hm χ n θ → ∃ s, u.IsFnPow n s θ) → (∀ (P : Out.PolAV (Sp ℂ)) (u
        : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef
        : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m
        : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l
        : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ
        Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l
        : Fin P.g → ℂ))))) * u.fr i (z +
        l)) → Function.Bijective Ef → u.IsAH Hm χ) → ThetaUnifAV := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 P rig hrig
  obtain ⟨u₀, hco, hlift⟩ := h1 P
  obtain ⟨u, Hm, χ, Ef, hex, hr, hd⟩ := h4 P rig hrig u₀
  rw [← hex] at hco hlift
  have hb := h6 P u Hm χ Ef hd
  have hAH := h9 P u Hm χ Ef hd hb
  have ht := h2 P.A P.L P.g u hco
  refine ⟨u, Hm, χ, Ef, hAH, hr, ht.1, ht.2, h3 P.A P.L P.g u hlift, fun n => ⟨(h7 P u Hm χ Ef hd n).1, fun θ hθ => ?_⟩,
    hd.2.2.1, hb, h5 P u Hm χ Ef hd⟩
  obtain ⟨s, hs⟩ := h8 P u Hm χ Ef hAH hd hb n θ hθ
  exact ⟨s, hs, fun s' hs' => (h7 P u Hm χ Ef hd n).2 θ s' s hs' hs⟩

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem thetaUnifAV_of_laws :
    Out.CubeSt → Out.MulNSt → Out.WeilSt → Out.WeilNondegSt → Out.GlobalSectionsRankAlgClosed → ThetaUnifAV := by
  intro hcube hmul hpair hnd hsec
  have hval := @valAt'_rules
  have hvalaff := @existsUnique_point_of_ringHom
  have hvalext := @eq_of_valAt'_eq hval hvalaff
  have hsmred := @isReduced_of_smooth_complex
  have hchring := @exists_holomorphic_section_of_etale
  have hchart := @HolChart.exists_holomorphic_chart hval hvalaff hchring
  have hcpt := @PointsCompact.compactSpace_points_polAV hval hvalaff
  have hholprod := @holFamily_lift hval
  have htopgrp := @isTopologicalGroup_complexPoints hval
  have hexp := @AbelianExp.exists_holUnif hmul hval hholprod htopgrp hcpt hchart
  have htan := @TangentOrigin.tangent_bijection_of_values hval
  have hendo := @EndoLinear.exists_linear_lift hval
  have hcubet := @cube_trivialisation_on_uniformising_space hval hholprod
  have hdbl := @exists_doubling_solution_pi
  have hdblu := @eventually_eq_zero_of_isBigO_cube_of_doubling
  have hlock := @LocalCube.exists_third_difference hdbl hdblu
  have hface := @cube_section_faces_and_doubling
  have hlocframe := @exists_localFrame_compatible_cube @hface hlock
  have hglobframe := @CubeFrame.exists_global_frame
  have hautfactor := @automorphyFactor_exp_linear_of_cube
  have hahform := @appellHumbert_normal_form_of_linear_exponent
  have hframe := @exists_appellHumbert_frame_isRig hcube hval hcubet
    @hlocframe @hglobframe @hautfactor hahform
  have hthg := @ThetaGroupFrame.thetaGrp_in_frame hval hholprod
  have hweil := @WeilExp.weilIs_exp_riemannForm hpair hval hvalext hsmred hthg
  have hunimod := @bilinForm_bijective_of_nondegenerate_mod
  have hperf := @riemannForm_bijective_of_weilNondeg hnd hunimod hweil
  have hsecfn := @sections_pow_theta_functions hval hvalext hsmred
  have hfshift := @fourierCoeff_unitCube_translate_of_entire_periodic
  have hfvan := @entire_periodic_eq_zero_of_fourierCoeff_eq_zero hfshift
  have hdimcl := @ClassicalTheta.card_le_pow_of_linearIndependent hfshift hfvan
  have hnormform := @SiegelNormalForm.exists_normal_form
  have hdim := @card_le_pow_of_linearIndependent_theta_principal hnormform hdimcl
  have hindep := @PowSec.exists_indep_sections hsec
  have hpos := @ThetaPositivity.re_form_pos_of_theta_ne_zero
  have hisah := @isAH_of_polarisation hval hpos hindep hsecfn
  have hseconto := @ThetaOnto.theta_from_section hval hdim hindep hsecfn
  exact thetaUnifAV_of_parts hexp htan hendo hframe hweil hperf hsecfn hseconto hisah

end GlobalTheory
end
