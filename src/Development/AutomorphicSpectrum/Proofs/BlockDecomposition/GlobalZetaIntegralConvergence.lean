import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleCpowDetInverseTwist
import BuildAid.ForwardExisting

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RSZeta

theorem differentiable_integral_cpow_of_one_le {X : Type*} [MeasurableSpace X] (ν : Measure X) (D : X → ℝ)
    (w : X → ℂ) (hD : Measurable D) (hw : Measurable w) (h1 : ∀ᵐ x ∂ν, 1 ≤ D x)
    (hfin : ∀ σ : ℝ, 1 < σ → ∫⁻ x, ‖w x‖ₑ * ENNReal.ofReal (D x ^ σ) ∂ν < ∞) :
    Differentiable ℂ (fun s : ℂ => ∫ x, w x * ((D x : ℝ) : ℂ) ^ s ∂ν) := by
  intro s₀
  set σ : ℝ := max 2 (|s₀.re| + 3) with hσ
  have hσ2 : 2 ≤ σ := le_max_left _ _
  have hσ3 : |s₀.re| + 3 ≤ σ := le_max_right _ _
  have hmD : Measurable fun x => ((D x : ℝ) : ℂ) := Complex.measurable_ofReal.comp hD
  have hmb : Measurable fun x => ‖w x‖ * D x ^ σ := hw.norm.mul (hD.pow_const σ)
  have hbound : Integrable (fun x => ‖w x‖ * D x ^ σ) ν := by
    refine ⟨hmb.aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt (le_of_eq ?_) (hfin σ (by linarith))
    refine lintegral_congr_ae ?_
    filter_upwards [h1] with x hx
    have hp : 0 ≤ D x ^ σ := Real.rpow_nonneg (by linarith) σ
    rw [enorm_mul, Real.enorm_of_nonneg hp, enorm_norm]
  have hre : ∀ s ∈ Metric.ball s₀ 1, s.re + 1 ≤ σ := by
    intro s hs
    have h : ‖s - s₀‖ < 1 := by simpa [dist_eq_norm] using hs
    have h2 : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
    have h3 := le_abs_self (s - s₀).re
    have h4 := le_abs_self s₀.re
    simp only [Complex.sub_re] at h2 h3
    linarith
  have hnorm : ∀ x, 1 ≤ D x → ∀ s : ℂ, ‖((D x : ℝ) : ℂ) ^ s‖ = D x ^ s.re := fun x hx s =>
    Complex.norm_cpow_eq_rpow_re_of_pos (by linarith) s
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := s₀)
    (F := fun s x => w x * ((D x : ℝ) : ℂ) ^ s)
    (F' := fun s x => w x * (((D x : ℝ) : ℂ) ^ s * Complex.log ((D x : ℝ) : ℂ)))
    (bound := fun x => ‖w x‖ * D x ^ σ) (Metric.ball_mem_nhds s₀ one_pos)
    (Eventually.of_forall fun s => (hw.mul (hmD.pow_const s)).aestronglyMeasurable)
    ?_ ((hw.mul ((hmD.pow_const s₀).mul (Complex.measurable_log.comp hmD))).aestronglyMeasurable)
    ?_ hbound ?_
  · exact key.2.differentiableAt
  · refine hbound.mono' (hw.mul (hmD.pow_const s₀)).aestronglyMeasurable ?_
    filter_upwards [h1] with x hx
    rw [norm_mul, hnorm x hx]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine Real.rpow_le_rpow_of_exponent_le hx ?_
    have := le_abs_self s₀.re
    linarith
  · filter_upwards [h1] with x hx s hs
    rw [norm_mul, norm_mul, hnorm x hx, ← Complex.ofReal_log (by linarith), Complex.norm_real,
      Real.norm_of_nonneg (Real.log_nonneg hx)]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hpos : 0 < D x := by linarith
    have hlog : Real.log (D x) ≤ D x := (Real.log_le_sub_one_of_pos hpos).trans (by linarith)
    calc D x ^ s.re * Real.log (D x) ≤ D x ^ s.re * D x :=
          mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hpos.le _)
      _ = D x ^ (s.re + 1) := by rw [Real.rpow_add_one hpos.ne']
      _ ≤ D x ^ σ := Real.rpow_le_rpow_of_exponent_le hx (hre s hs)
  · filter_upwards [h1] with x hx s _
    have h0 : ((D x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by linarith)
    have := ((hasDerivAt_id s).const_cpow (c := ((D x : ℝ) : ℂ)) (Or.inl h0)).const_mul (w x)
    simpa using this

theorem differentiable_Zp (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ)
    (Φ : (Fin 2 → 𝔸[ℚ]) → ℂ) (c : HeckeCharacter ℚ) (h3 : Ad3.R.G3) (h0 : Set0 μ 𝓕 mK 𝓓) (hH : Aut H)
    (hΦ : Φ ∈ Adele2.schwartzBruhat2 ℚ) : Differentiable ℂ (GlobalTheory.CompanionTheory.RSZeta.Zp μ 𝓕 H c Φ) := by
  have hth : Measurable (th Φ) := (h3 μ 𝓕 mK 𝓓 h0 H hH Φ hΦ 2 one_lt_two).1
  have hmA : MeasurableSet (𝓕 ∩ {g | 1 ≤ Dt g}) :=
    h0.meas.inter (measurableSet_le measurable_const measurable_Dt)
  have hw : Measurable fun g => H g * cdet c g * th Φ g :=
    (hH.cont.measurable.mul (measurable_cdet c)).mul hth
  have main := differentiable_integral_cpow_of_one_le (μ.restrict (𝓕 ∩ {g | 1 ≤ Dt g})) Dt
    (fun g => H g * cdet c g * th Φ g) measurable_Dt hw
    ((ae_restrict_mem hmA).mono fun g hg => hg.2) ?_
  · have e : GlobalTheory.CompanionTheory.RSZeta.Zp μ 𝓕 H c Φ =
        fun s : ℂ => ∫ g, (H g * cdet c g * th Φ g) * ((Dt g : ℝ) : ℂ) ^ s ∂(μ.restrict (𝓕 ∩ {g | 1 ≤ Dt g})) := by
      funext s
      simp only [Zp]
      refine integral_congr_ae (Eventually.of_forall fun g => ?_)
      simp only
      ring
    rw [e]
    exact main
  · intro σ hσ
    refine lt_of_le_of_lt ?_ (h3 μ 𝓕 mK 𝓓 h0 H hH Φ hΦ σ hσ).2.2
    refine le_trans ?_ (lintegral_mono_set (Set.inter_subset_left (t := {g | 1 ≤ Dt g})))
    refine lintegral_mono fun g => ?_
    have hc : ‖cdet c g‖ₑ = 1 := by
      rw [← ofReal_norm, norm_cdet]; simp
    rw [enorm_mul, enorm_mul, hc, mul_one]
    calc ‖H g‖ₑ * ‖th Φ g‖ₑ * ENNReal.ofReal (Dt g ^ σ)
        = (‖H g‖ₑ * ENNReal.ofReal (Dt g ^ σ)) * ‖th Φ g‖ₑ := by ring
      _ ≤ _ := by gcongr; exact enorm_tsum_le_tsum_enorm

end GlobalTheory.CompanionTheory.RSZeta
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiable_partial_zeta_integral : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (Φ : (Fin 2 → 𝔸[ℚ]) → ℂ) (c : HeckeCharacter ℚ),
  Ad3.R.G3 → Set0 μ 𝓕 mK 𝓓 → Aut H → Φ ∈ Adele2.schwartzBruhat2 ℚ → Differentiable ℂ (GlobalTheory.CompanionTheory.RSZeta.Zp μ 𝓕 H c Φ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.RSZeta.differentiable_Zp
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RSZeta

theorem Bd_differentiable : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (c : HeckeCharacter ℚ),
    Set0 μ 𝓕 mK 𝓓 → Aut H → Differentiable ℂ (GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c) := by
  intro μ 𝓕 mK 𝓓 H c h0 hH s₀
  obtain ⟨C, hC⟩ := hH.bdd
  have hband : MeasurableSet band :=
    (measurable_Dt measurableSet_Ici).inter (measurable_Dt measurableSet_Iio)
  have hS : MeasurableSet (𝓕 ∩ band) := h0.meas.inter hband
  haveI : IsFiniteMeasure (μ.restrict (𝓕 ∩ band)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact h0.vol⟩
  set R : ℝ := |s₀.re| + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)

  have hpow : ∀ g ∈ 𝓕 ∩ band, ∀ s ∈ Metric.ball s₀ 1, ‖((Dt g : ℝ) : ℂ) ^ s‖ ≤ (2 : ℝ) ^ R := by
    intro g hg s hs
    obtain ⟨h1, h2⟩ := hg.2
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (Dt_pos g)]
    have hre : s.re ≤ R := by
      have h3 : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
      have h4 : ‖s - s₀‖ < 1 := by simpa [dist_eq_norm] using hs
      have h5 := abs_le.1 h3
      have h6 := le_abs_self s₀.re
      simp only [Complex.sub_re] at h5
      rw [hR]; linarith [h5.2]
    calc Dt g ^ s.re ≤ Dt g ^ R := Real.rpow_le_rpow_of_exponent_le h1 hre
      _ ≤ (2 : ℝ) ^ R := Real.rpow_le_rpow (Dt_pos g).le h2.le hR0
  have hlog : ∀ g ∈ 𝓕 ∩ band, ‖Complex.log ((Dt g : ℝ) : ℂ)‖ ≤ 1 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hg.2
    rw [← Complex.ofReal_log (Dt_pos g).le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg h1)]
    linarith [Real.log_le_sub_one_of_pos (Dt_pos g)]
  have hF' : ∀ s : ℂ, Measurable fun g =>
      H g * cdet c g * (((Dt g : ℝ) : ℂ) ^ s * Complex.log ((Dt g : ℝ) : ℂ)) := by
    intro s
    have hl : Measurable fun g => Complex.log ((Dt g : ℝ) : ℂ) :=
      Complex.measurable_log.comp (Complex.measurable_ofReal.comp measurable_Dt)
    exact (hH.cont.measurable.mul (measurable_cdet c)).mul
      (((Complex.measurable_ofReal.comp measurable_Dt).pow_const s).mul hl)
  have hbd : ∀ g ∈ 𝓕 ∩ band, ∀ s ∈ Metric.ball s₀ 1, ‖H g * cdet c g * ((((Dt g : ℝ) : ℂ) ^ s) * Complex.log ((Dt g : ℝ) : ℂ))‖ ≤ C * (2 : ℝ) ^ R := by
    intro g hg s hs
    rw [norm_mul, norm_mul, norm_mul, norm_cdet, mul_one]
    have h1 := hpow g hg s hs
    have h2 := hlog g hg
    have h3 := hC g
    calc ‖H g‖ * (‖((Dt g : ℝ) : ℂ) ^ s‖ * ‖Complex.log ((Dt g : ℝ) : ℂ)‖)
        ≤ C * ((2 : ℝ) ^ R * 1) := by gcongr
      _ = C * (2 : ℝ) ^ R := by ring
  have hint : Integrable (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s₀) (μ.restrict (𝓕 ∩ band)) := by
    refine (integrable_const (C * (2 : ℝ) ^ R)).mono' (measurable_w hH c s₀).aestronglyMeasurable ?_
    refine (ae_restrict_iff' hS).2 (Eventually.of_forall fun g hg => ?_)
    rw [norm_mul, norm_mul, norm_cdet, mul_one]
    have h1 := hpow g hg s₀ (Metric.mem_ball_self one_pos)
    have h3 := hC g
    gcongr
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict (𝓕 ∩ band))
    (F := fun s g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s)
    (F' := fun s g => H g * cdet c g * (((Dt g : ℝ) : ℂ) ^ s * Complex.log ((Dt g : ℝ) : ℂ)))
    (x₀ := s₀) (s := Metric.ball s₀ 1) (bound := fun _ => C * (2 : ℝ) ^ R)
    (Metric.ball_mem_nhds s₀ one_pos)
    (Eventually.of_forall fun s => (measurable_w hH c s).aestronglyMeasurable)
    hint (hF' s₀).aestronglyMeasurable
    ((ae_restrict_iff' hS).2 (Eventually.of_forall fun g hg s hs => hbd g hg s hs))
    (integrable_const _)
    (Eventually.of_forall fun g s _ => by
      have := ((hasDerivAt_id s).const_cpow (c := ((Dt g : ℝ) : ℂ)) (Or.inl (Dt_ne g))).const_mul (H g * cdet c g)
      simpa using this)
  exact key.2.differentiableAt

end GlobalTheory.CompanionTheory.RSZeta
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiable_boundary_zeta_term : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (c : HeckeCharacter ℚ),
  Set0 μ 𝓕 mK 𝓓 → Aut H → Differentiable ℂ (GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.RSZeta.Bd_differentiable
end

section
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RSZeta

def dyShell (n : ℕ) : Set ℝ := {x | x * 2 ^ n ∈ Set.Ico (1 : ℝ) 2}

theorem measurableSet_dyShell (n : ℕ) : MeasurableSet (dyShell n) :=
  (measurable_id.mul_const ((2 : ℝ) ^ n)) measurableSet_Ico

theorem exists_mem_dyShell {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : ∃ n : ℕ, x ∈ dyShell (n + 1) := by
  have hex : ∃ m : ℕ, 1 ≤ x * 2 ^ m := by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt x⁻¹ (one_lt_two : (1 : ℝ) < 2)
    refine ⟨m, ?_⟩
    have := mul_lt_mul_of_pos_left hm h0
    rw [mul_inv_cancel₀ h0.ne'] at this
    exact this.le
  have hspec := Nat.find_spec hex
  have hne : Nat.find hex ≠ 0 := by
    intro h
    rw [h] at hspec
    simp at hspec
    linarith
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
  have hmin : ¬ 1 ≤ x * 2 ^ k := Nat.find_min hex (by omega)
  rw [hk] at hspec
  refine ⟨k, hspec, ?_⟩
  have : x * 2 ^ (k + 1) = 2 * (x * 2 ^ k) := by ring
  show x * 2 ^ (k + 1) < 2
  rw [this]
  linarith [not_le.1 hmin]

def lowW (H : G2 → ℂ) (σ : ℝ) (g : G2) : ℝ≥0∞ := ‖H g‖ₑ * ENNReal.ofReal (Dt g ^ σ)

theorem measurable_lowW {H : G2 → ℂ} (hH : Aut H) (σ : ℝ) : Measurable (lowW H σ) :=
  hH.cont.measurable.enorm.mul (ENNReal.measurable_ofReal.comp (measurable_Dt.pow_const σ))

theorem linv_lowW {H : G2 → ℂ} (hH : Aut H) (σ : ℝ) : LInv (lowW H σ) := fun γ g => by
  simp only [lowW, hH.left γ g, Dt_dia]

theorem lowW_dg {H : G2 → ℂ} (hH : Aut H) (σ : ℝ) {z : Jd} (hz : md z ^ 2 = 1 / 2) (g : G2) :
    lowW H σ (dg2 z z * g) = ENNReal.ofReal ((1 / 2 : ℝ) ^ σ) * lowW H σ g := by
  simp only [lowW, hH.cen z g, Dt_dg, hz]
  rw [Real.mul_rpow (by norm_num) (Dt_pos g).le, ENNReal.ofReal_mul (by positivity)]
  ring

def lowS (H : G2 → ℂ) (σ : ℝ) (n : ℕ) : G2 → ℝ≥0∞ := Set.indicator {g | Dt g ∈ dyShell n} (lowW H σ)

theorem measurable_lowS {H : G2 → ℂ} (hH : Aut H) (σ : ℝ) (n : ℕ) : Measurable (lowS H σ n) :=
  (measurable_lowW hH σ).indicator (measurable_Dt (measurableSet_dyShell n))

theorem lowS_dg {H : G2 → ℂ} (hH : Aut H) (σ : ℝ) {z : Jd} (hz : md z ^ 2 = 1 / 2) (n : ℕ) (g : G2) :
    lowS H σ (n + 1) (dg2 z z * g) = ENNReal.ofReal ((1 / 2 : ℝ) ^ σ) * lowS H σ n g := by
  have hm : Dt (dg2 z z * g) ∈ dyShell (n + 1) ↔ Dt g ∈ dyShell n := by
    have e : 1 / 2 * Dt g * 2 ^ (n + 1) = Dt g * 2 ^ n := by ring
    simp only [dyShell, Set.mem_setOf_eq, Dt_dg, hz, e]
  by_cases h : Dt g ∈ dyShell n
  · rw [lowS, lowS, Set.indicator_of_mem (show dg2 z z * g ∈ {g | Dt g ∈ dyShell (n + 1)} from hm.2 h),
      Set.indicator_of_mem (show g ∈ {g | Dt g ∈ dyShell n} from h), lowW_dg hH σ hz]
  · rw [lowS, lowS, Set.indicator_of_notMem (show dg2 z z * g ∉ {g | Dt g ∈ dyShell (n + 1)} from fun h' => h (hm.1 h')),
      Set.indicator_of_notMem (show g ∉ {g | Dt g ∈ dyShell n} from h), mul_zero]

theorem lintegral_lowS_zero {μ : Measure G2} {𝓕 : Set G2} {mK : Measure KA} {𝓓 : Set Jd} {H : G2 → ℂ}
    (h0 : Set0 μ 𝓕 mK 𝓓) (hH : Aut H) {σ : ℝ} (hσ : 0 < σ) :
    ∫⁻ g in 𝓕, lowS H σ 0 g ∂μ < ∞ := by
  obtain ⟨C, hC⟩ := hH.bdd
  have hb : MeasurableSet band := by
    have : band = {g | Dt g ∈ Set.Ico (1 : ℝ) 2} := rfl
    rw [this]
    exact measurable_Dt measurableSet_Ico
  have hle : ∀ g, lowS H σ 0 g ≤ Set.indicator band (fun _ => ENNReal.ofReal (C * 2 ^ σ)) g := by
    intro g
    have hiff : g ∈ {g | Dt g ∈ dyShell 0} ↔ g ∈ band := by
      show Dt g * 2 ^ 0 ∈ Set.Ico (1 : ℝ) 2 ↔ (1 ≤ Dt g ∧ Dt g < 2)
      simp
    by_cases h : g ∈ band
    · have hs := hiff.2 h
      rw [lowS, Set.indicator_of_mem hs, Set.indicator_of_mem h, lowW]
      have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC g)
      rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul (hC g)
        (Real.rpow_le_rpow (Dt_pos g).le h.2.le hσ.le) (by have := Dt_pos g; positivity) hC0)
    · have hs : g ∉ {g | Dt g ∈ dyShell 0} := fun h' => h (hiff.1 h')
      rw [lowS, Set.indicator_of_notMem hs, Set.indicator_of_notMem h]
  calc ∫⁻ g in 𝓕, lowS H σ 0 g ∂μ
      ≤ ∫⁻ g in 𝓕, Set.indicator band (fun _ => ENNReal.ofReal (C * 2 ^ σ)) g ∂μ :=
        lintegral_mono hle
    _ = ENNReal.ofReal (C * 2 ^ σ) * μ (𝓕 ∩ band) := by
        rw [lintegral_indicator hb, setLIntegral_const, Measure.restrict_apply hb, Set.inter_comm band 𝓕]
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h0.vol

theorem lintegral_lowS_succ {μ : Measure G2} {𝓕 : Set G2} {mK : Measure KA} {𝓓 : Set Jd} {H : G2 → ℂ}
    (hG : Ad3.R.G1a) (h0 : Set0 μ 𝓕 mK 𝓓) (hH : Aut H) (σ : ℝ) {z : Jd} (hz : md z ^ 2 = 1 / 2) (n : ℕ) :
    ∫⁻ g in 𝓕, lowS H σ (n + 1) g ∂μ = ENNReal.ofReal ((1 / 2 : ℝ) ^ σ) * ∫⁻ g in 𝓕, lowS H σ n g ∂μ := by
  have hT := ((hG μ 𝓕 mK 𝓓 h0).2.2 (fun g => dg2 z z * g) (Or.inr (Or.inr ⟨z, rfl⟩))).1 (lowS H σ (n + 1))
    (measurable_lowS hH σ (n + 1)) (linv_ind (linv_lowW hH σ) (dyShell (n + 1)))
  rw [← hT, ← lintegral_const_mul _ (measurable_lowS hH σ n)]
  exact lintegral_congr fun g => lowS_dg hH σ hz n g

theorem lintegral_lowW_lt_top {μ : Measure G2} {𝓕 : Set G2} {mK : Measure KA} {𝓓 : Set Jd} {H : G2 → ℂ}
    (hG : Ad3.R.G1a) (h0 : Set0 μ 𝓕 mK 𝓓) (hH : Aut H) {σ : ℝ} (hσ : 0 < σ) :
    ∫⁻ g in 𝓕 ∩ {g | Dt g < 1}, lowW H σ g ∂μ < ∞ := by
  obtain ⟨z, hz, -⟩ := (hG μ 𝓕 mK 𝓓 h0).2.1 (1 / 2) (by norm_num)
  set q : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℝ) ^ σ) with hq
  have hq1 : q < 1 := by
    rw [hq, ENNReal.ofReal_lt_one]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) hσ
  have hpow : ∀ n, ∫⁻ g in 𝓕, lowS H σ n g ∂μ = q ^ n * ∫⁻ g in 𝓕, lowS H σ 0 g ∂μ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [lintegral_lowS_succ hG h0 hH σ hz n, ih, pow_succ']; ring
  have hS : MeasurableSet {g : G2 | Dt g < 1} := measurable_Dt measurableSet_Iio
  have hle : ∀ g, Set.indicator {g : G2 | Dt g < 1} (lowW H σ) g ≤ ∑' n, lowS H σ n g := by
    intro g
    by_cases h : g ∈ {g : G2 | Dt g < 1}
    · obtain ⟨n, hn⟩ := exists_mem_dyShell (Dt_pos g) h
      rw [Set.indicator_of_mem h]
      refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (n + 1))
      rw [lowS, Set.indicator_of_mem (show g ∈ {g | Dt g ∈ dyShell (n + 1)} from hn)]
    · rw [Set.indicator_of_notMem h]
      exact zero_le
  calc ∫⁻ g in 𝓕 ∩ {g | Dt g < 1}, lowW H σ g ∂μ
      = ∫⁻ g in 𝓕, Set.indicator {g : G2 | Dt g < 1} (lowW H σ) g ∂μ := by
        rw [lintegral_indicator hS, Measure.restrict_restrict hS, Set.inter_comm 𝓕]
    _ ≤ ∫⁻ g in 𝓕, ∑' n, lowS H σ n g ∂μ := lintegral_mono hle
    _ = ∑' n, ∫⁻ g in 𝓕, lowS H σ n g ∂μ :=
        lintegral_tsum fun n => (measurable_lowS hH σ n).aemeasurable
    _ = (∑' n, q ^ n) * ∫⁻ g in 𝓕, lowS H σ 0 g ∂μ := by
        rw [tsum_congr hpow, ENNReal.tsum_mul_right]
    _ < ∞ := by
        refine ENNReal.mul_lt_top ?_ (lintegral_lowS_zero h0 hH hσ)
        rw [ENNReal.tsum_geometric]
        exact ENNReal.inv_lt_top.2 (tsub_pos_of_lt hq1)

theorem integrableOn_low (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ)
    (c : HeckeCharacter ℚ) (hG : Ad3.R.G1a) (h0 : Set0 μ 𝓕 mK 𝓓) (hH : Aut H) (_hc : IsOfFinOrder c)
    (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s) (𝓕 ∩ {g | Dt g < 1}) μ := by
  refine ⟨(measurable_w hH c s).aestronglyMeasurable, ?_⟩
  have hn : ∀ g, ‖H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s‖ₑ = lowW H s.re g := by
    intro g
    rw [enorm_mul, enorm_mul, lowW, ← ofReal_norm_eq_enorm (cdet c g), norm_cdet,
      ← ofReal_norm_eq_enorm (((Dt g : ℝ) : ℂ) ^ s), Complex.norm_cpow_eq_rpow_re_of_pos (Dt_pos g)]
    simp
  rw [HasFiniteIntegral]
  simp_rw [hn]
  exact lintegral_lowW_lt_top hG h0 hH hs

end GlobalTheory.CompanionTheory.RSZeta
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_lower_zeta_integrand : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (c : HeckeCharacter ℚ),
  Ad3.R.G1a → Set0 μ 𝓕 mK 𝓓 → Aut H → IsOfFinOrder c → ∀ s : ℂ, 0 < s.re →
    IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s) (𝓕 ∩ {g | Dt g < 1}) μ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.RSZeta.integrableOn_low
end

section
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RSZeta

theorem integrableOn_band_w {μ : Measure G2} {𝓕 : Set G2} {mK : Measure KA} {𝓓 : Set Jd}
    {H : G2 → ℂ} (c : HeckeCharacter ℚ) (hS : Set0 μ 𝓕 mK 𝓓) (hH : Aut H) (s : ℂ)
    (hmb : MeasurableSet band) :
    IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s) (𝓕 ∩ band) μ := by
  obtain ⟨C, hC⟩ := hH.bdd
  have hmF : MeasurableSet (𝓕 ∩ band) := hS.meas.inter hmb
  refine Measure.integrableOn_of_bounded (M := C * (2 : ℝ) ^ |s.re|) hS.vol.ne
    (measurable_w hH c s).aestronglyMeasurable ?_
  refine (ae_restrict_iff' hmF).2 (Eventually.of_forall fun g hg => ?_)
  obtain ⟨h1, h2⟩ := hg.2
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
  have hp : (Dt g) ^ s.re ≤ (2 : ℝ) ^ |s.re| :=
    (Real.rpow_le_rpow_of_exponent_le h1 (le_abs_self _)).trans
      (Real.rpow_le_rpow (Dt_pos g).le h2.le (abs_nonneg _))
  rw [norm_mul, norm_mul, norm_cdet, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos (Dt_pos g)]
  exact mul_le_mul (hC g) hp (Real.rpow_nonneg (Dt_pos g).le _) hC0

theorem cpow_half (s : ℂ) : (((1 / 2 : ℝ)) : ℂ) ^ s = 2 ^ (-s) := by
  have h2 : (2 : ℂ).arg ≠ Real.pi := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.arg_ofReal_of_nonneg (by norm_num)]
    exact Real.pi_pos.ne
  rw [show (((1 / 2 : ℝ)) : ℂ) = (2 : ℂ)⁻¹ by push_cast; norm_num, Complex.inv_cpow _ _ h2,
    Complex.cpow_neg]

theorem Jl_shift : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (c : HeckeCharacter ℚ),
  Ad3.R.G1a → Set0 μ 𝓕 mK 𝓓 → Aut H → IsOfFinOrder c → ∀ s : ℂ,
    IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s) (𝓕 ∩ {g | Dt g < 1}) μ →
    GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c s * (1 - 2 ^ (-s)) = GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c s * 2 ^ (-s) := by
  intro μ 𝓕 mK 𝓓 H c hG hS hH hc s hI
  set w : G2 → ℂ := fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s with hw
  obtain ⟨-, hr, hT⟩ := hG μ 𝓕 mK 𝓓 hS
  obtain ⟨z, hz2, hzc⟩ := hr (1 / 2) (by norm_num)
  have hzc' := hzc c hc
  have hm1 : MeasurableSet {g : G2 | Dt g < 1} := measurableSet_lt measurable_Dt measurable_const
  have hm2 : MeasurableSet {g : G2 | Dt g < 2} := measurableSet_lt measurable_Dt measurable_const
  have hmb : MeasurableSet band :=
    (measurableSet_le measurable_const measurable_Dt).inter hm2
  have hwm : Measurable w := measurable_w hH c s
  have hset : {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} = {g : G2 | Dt g < 1} := rfl
  have hFm : Measurable (Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w) :=
    hwm.indicator hm1
  have hFl : LInv (Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w) :=
    linv_ind (linv_w hH c s) _
  have hinv : ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w (dg2 z z * g) ∂μ =
      ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w g ∂μ :=
    (hT (fun g : G2 => dg2 z z * g) (Or.inr (Or.inr ⟨z, rfl⟩))).2 _ hFm hFl
  have hpt : ∀ g : G2, Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w (dg2 z z * g) =
      2 ^ (-s) * Set.indicator {g : G2 | Dt g < 2} w g := by
    intro g
    have hD : Dt (dg2 z z * g) = 1 / 2 * Dt g := by rw [Dt_dg, hz2]
    have hwg : w (dg2 z z * g) = 2 ^ (-s) * w g := by
      simp only [hw]
      rw [hH.cen z g, cdet_dg c z hzc' g, cpow_dg, hz2, cpow_half]
      ring
    by_cases h : Dt g < 2
    · have h' : dg2 z z * g ∈ {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} := by
        simp only [Set.mem_setOf_eq, Set.mem_Iio, hD]; linarith
      rw [Set.indicator_of_mem h', Set.indicator_of_mem (show g ∈ {g : G2 | Dt g < 2} from h), hwg]
    · have h' : dg2 z z * g ∉ {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} := by
        simp only [Set.mem_setOf_eq, Set.mem_Iio, hD]; linarith
      rw [Set.indicator_of_notMem h', Set.indicator_of_notMem (show g ∉ {g : G2 | Dt g < 2} from h),
        mul_zero]
  have e1 : ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w (dg2 z z * g) ∂μ =
      2 ^ (-s) * ∫ g in 𝓕 ∩ {g : G2 | Dt g < 2}, w g ∂μ := by
    simp_rw [hpt]
    rw [integral_const_mul, setIntegral_indicator hm2]
  have e2 : ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Iio (1 : ℝ)} w g ∂μ =
      GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c s := by
    rw [hset, setIntegral_indicator hm1]
    rfl
  have hun : 𝓕 ∩ {g : G2 | Dt g < 2} = (𝓕 ∩ {g : G2 | Dt g < 1}) ∪ (𝓕 ∩ band) := by
    ext g
    simp only [band, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h : Dt g < 1
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨h1, not_lt.1 h, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, -, h2⟩)
      · exact ⟨h1, by linarith⟩
      · exact ⟨h1, h2⟩
  have hdis : Disjoint (𝓕 ∩ {g : G2 | Dt g < 1}) (𝓕 ∩ band) := by
    refine Set.disjoint_left.2 fun g hg hb => ?_
    have h1 : Dt g < 1 := hg.2
    have h2 : 1 ≤ Dt g := hb.2.1
    linarith
  have e3 : ∫ g in 𝓕 ∩ {g : G2 | Dt g < 2}, w g ∂μ =
      GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c s + GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c s := by
    rw [hun, setIntegral_union hdis (hS.meas.inter hmb) hI (integrableOn_band_w c hS hH s hmb)]
    rfl
  have key : 2 ^ (-s) * (GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c s + GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c s) =
      GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c s := by
    rw [← e3, ← e1, hinv, e2]
  linear_combination -key

end GlobalTheory.CompanionTheory.RSZeta
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lower_zeta_integral_boundary_relation : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (c : HeckeCharacter ℚ),
  Ad3.R.G1a → Set0 μ 𝓕 mK 𝓓 → Aut H → IsOfFinOrder c → ∀ s : ℂ,
    IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s) (𝓕 ∩ {g | Dt g < 1}) μ →
    GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c s * (1 - 2 ^ (-s)) = GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c s * 2 ^ (-s) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.RSZeta.Jl_shift
end

section
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RSZeta

theorem restrict_Dt_two_null {μ : Measure G2} {𝓕 : Set G2} {mK : Measure KA} {𝓓 : Set Jd}
    (hG : Ad3.R.G1a) (h0 : Set0 μ 𝓕 mK 𝓓) : (μ.restrict 𝓕) {g | Dt g ∈ ({2} : Set ℝ)} = 0 := by
  obtain ⟨h1, hz, hT⟩ := hG μ 𝓕 mK 𝓓 h0
  obtain ⟨z, hz2, -⟩ := hz 2 (by norm_num)
  have hinv := (hT (fun g => dg2 z z * g) (Or.inr (Or.inr ⟨z, rfl⟩))).1
  have hS : MeasurableSet {g : G2 | Dt g ∈ ({2} : Set ℝ)} := measurable_Dt (measurableSet_singleton _)
  have hS1 : MeasurableSet {g : G2 | Dt g = 1} := measurable_Dt (measurableSet_singleton (1 : ℝ))
  have key := hinv (Set.indicator {g : G2 | Dt g ∈ ({2} : Set ℝ)} (fun _ => (1 : ℝ≥0∞)))
    (measurable_const.indicator hS) (linv_ind (fun _ _ => rfl) _)
  have e1 : (fun g : G2 => Set.indicator {g : G2 | Dt g ∈ ({2} : Set ℝ)} (fun _ => (1 : ℝ≥0∞)) (dg2 z z * g))
      = Set.indicator {g : G2 | Dt g = 1} (fun _ => (1 : ℝ≥0∞)) := by
    funext g
    have : (dg2 z z * g ∈ {g : G2 | Dt g ∈ ({2} : Set ℝ)}) ↔ g ∈ {g : G2 | Dt g = 1} := by
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Dt_dg, hz2]
      constructor <;> intro h <;> linarith
    by_cases hg : g ∈ {g : G2 | Dt g = 1}
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (this.2 hg)]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (this.1 h))]
  rw [e1, lintegral_indicator_const hS1, lintegral_indicator_const hS, one_mul, one_mul] at key
  rw [← key]
  exact le_antisymm ((Measure.restrict_apply_le _ _).trans h1.le) bot_le

theorem Bd_reflect : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (c : HeckeCharacter ℚ),
    Ad3.R.G1a → Set0 μ 𝓕 mK 𝓓 → Aut H → IsOfFinOrder c → ∀ s : ℂ,
      GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c⁻¹ (-s) = 2 ^ (-s) * GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c s := by
  intro μ 𝓕 mK 𝓓 H c hG h0 hH hc s
  have hnull2 := restrict_Dt_two_null hG h0
  obtain ⟨h1, hz, hT⟩ := hG μ 𝓕 mK 𝓓 h0
  obtain ⟨z, hz2, hzc⟩ := hz (1 / 2) (by norm_num)
  have hzc := hzc c hc
  set w : G2 → ℂ := fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s with hw
  set w' : G2 → ℂ := fun g => H g * cdet c⁻¹ g * ((Dt g : ℝ) : ℂ) ^ (-s) with hw'
  have mS : ∀ A : Set ℝ, MeasurableSet A → MeasurableSet {g : G2 | Dt g ∈ A} := fun A hA => measurable_Dt hA
  have hband : band = {g : G2 | Dt g ∈ Set.Ico (1 : ℝ) 2} := rfl
  have mB : MeasurableSet band := hband ▸ mS _ measurableSet_Ico

  have b1 : Bd μ 𝓕 H c⁻¹ (-s) = ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Ico (1 : ℝ) 2} w' g ∂μ := by
    rw [setIntegral_indicator (mS _ measurableSet_Ico)]; rfl
  have b2 : Bd μ 𝓕 H c s = ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Ico (1 : ℝ) 2} w g ∂μ := by
    rw [setIntegral_indicator (mS _ measurableSet_Ico)]; rfl

  have r1 := (hT Ad3.R.inv2 (Or.inl rfl)).2 (Set.indicator {g : G2 | Dt g ∈ Set.Ico (1 : ℝ) 2} w')
    ((measurable_w hH c⁻¹ (-s)).indicator (mS _ measurableSet_Ico)) (linv_ind (linv_w hH c⁻¹ (-s)) _)
  have e1 : (fun g : G2 => Set.indicator {g : G2 | Dt g ∈ Set.Ico (1 : ℝ) 2} w' (Ad3.R.inv2 g))
      = Set.indicator {g : G2 | Dt g ∈ Set.Ioc (1 / 2 : ℝ) 1} w := by
    funext g
    have hp := Dt_pos g
    have hm : (Ad3.R.inv2 g ∈ {g : G2 | Dt g ∈ Set.Ico (1 : ℝ) 2}) ↔ g ∈ {g : G2 | Dt g ∈ Set.Ioc (1 / 2 : ℝ) 1} := by
      simp only [Set.mem_setOf_eq, Set.mem_Ico, Set.mem_Ioc, module_det_inverse_twist]
      rw [one_le_inv₀ hp, inv_lt_comm₀ hp (by norm_num)]
      constructor
      · rintro ⟨a, b⟩; exact ⟨by norm_num at b ⊢; linarith, a⟩
      · rintro ⟨a, b⟩; exact ⟨b, by norm_num at a ⊢; linarith⟩
    have hv : w' (Ad3.R.inv2 g) = w g := by
      simp only [hw, hw', Aut.inv2 hH, character_det_inverse_twist, module_cpow_det_inverse_twist, inv_inv, neg_neg]
    by_cases hg : g ∈ {g : G2 | Dt g ∈ Set.Ioc (1 / 2 : ℝ) 1}
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hm.2 hg), hv]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hm.1 h))]

  have r2 := (hT (fun g => dg2 z z * g) (Or.inr (Or.inr ⟨z, rfl⟩))).2
    (Set.indicator {g : G2 | Dt g ∈ Set.Ioc (1 / 2 : ℝ) 1} w)
    ((measurable_w hH c s).indicator (mS _ measurableSet_Ioc)) (linv_ind (linv_w hH c s) _)
  have hhalf : (((1 / 2 : ℝ) : ℝ) : ℂ) ^ s = 2 ^ (-s) := by
    have : (((1 / 2 : ℝ) : ℝ) : ℂ) = (2 : ℂ)⁻¹ := by push_cast; norm_num
    rw [this, Complex.inv_cpow _ _ (by simpa using Real.pi_pos.ne), Complex.cpow_neg]
  have e2 : (fun g : G2 => Set.indicator {g : G2 | Dt g ∈ Set.Ioc (1 / 2 : ℝ) 1} w (dg2 z z * g))
      = fun g => 2 ^ (-s) * Set.indicator {g : G2 | Dt g ∈ Set.Ioc (1 : ℝ) 2} w g := by
    funext g
    have hm : (dg2 z z * g ∈ {g : G2 | Dt g ∈ Set.Ioc (1 / 2 : ℝ) 1}) ↔ g ∈ {g : G2 | Dt g ∈ Set.Ioc (1 : ℝ) 2} := by
      simp only [Set.mem_setOf_eq, Set.mem_Ioc, Dt_dg, hz2]
      constructor
      · rintro ⟨a, b⟩; exact ⟨by linarith, by linarith⟩
      · rintro ⟨a, b⟩; exact ⟨by linarith, by linarith⟩
    have hv : w (dg2 z z * g) = 2 ^ (-s) * w g := by
      simp only [hw]
      rw [hH.cen, cdet_dg c z hzc, cpow_dg, hz2, hhalf]
      ring
    by_cases hg : g ∈ {g : G2 | Dt g ∈ Set.Ioc (1 : ℝ) 2}
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hm.2 hg), hv]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hm.1 h)), mul_zero]

  have ae1 : ∀ᵐ g ∂(μ.restrict 𝓕), Dt g ≠ 1 :=
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 h1)
  have ae2 : ∀ᵐ g ∂(μ.restrict 𝓕), Dt g ≠ 2 := by
    have := measure_eq_zero_iff_ae_notMem.1 hnull2
    simpa using this
  have r3 : ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Ioc (1 : ℝ) 2} w g ∂μ
      = ∫ g in 𝓕, Set.indicator {g : G2 | Dt g ∈ Set.Ico (1 : ℝ) 2} w g ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [ae1, ae2] with g g1 g2
    have hm : g ∈ {g : G2 | Dt g ∈ Set.Ioc (1 : ℝ) 2} ↔ g ∈ {g : G2 | Dt g ∈ Set.Ico (1 : ℝ) 2} := by
      simp only [Set.mem_setOf_eq, Set.mem_Ioc, Set.mem_Ico]
      constructor
      · rintro ⟨a, b⟩; exact ⟨a.le, lt_of_le_of_ne b g2⟩
      · rintro ⟨a, b⟩; exact ⟨lt_of_le_of_ne a (Ne.symm g1), b.le⟩
    by_cases hg : g ∈ {g : G2 | Dt g ∈ Set.Ioc (1 : ℝ) 2}
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hm.1 hg)]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hm.2 h))]
  rw [b1, b2, ← r1, e1, ← r2, e2, integral_const_mul, r3]

end GlobalTheory.CompanionTheory.RSZeta

end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_zeta_term_functional_equation : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (c : HeckeCharacter ℚ),
  Ad3.R.G1a → Set0 μ 𝓕 mK 𝓓 → Aut H → IsOfFinOrder c → ∀ s : ℂ,
    GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c⁻¹ (-s) = 2 ^ (-s) * GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c s := by
  atlas_forward_decl GlobalTheory.CompanionTheory.RSZeta.Bd_reflect
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RSZeta

theorem integrableOn_Zg_integrand {μ : Measure G2} {𝓕 : Set G2} {H : G2 → ℂ}
    {Φ : (Fin 2 → 𝔸[ℚ]) → ℂ} (c : HeckeCharacter ℚ) (hH : Aut H) (s : ℂ)
    (mth : Measurable (th Φ))
    (fin : ∫⁻ g in 𝓕, (‖H g‖ₑ * ENNReal.ofReal (Dt g ^ s.re)) * ∑' ξ : NZ, ‖Φ (row ξ.1 g)‖ₑ ∂μ < ∞) :
    IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s * th Φ g) 𝓕 μ := by
  refine ⟨((measurable_w hH c s).mul mth).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  refine lt_of_le_of_lt (lintegral_mono fun g => ?_) fin
  have h1 : ‖cdet c g‖ₑ = 1 := by
    rw [← ofReal_norm_eq_enorm, norm_cdet]; simp
  have h2 : ‖((Dt g : ℝ) : ℂ) ^ s‖ₑ = ENNReal.ofReal (Dt g ^ s.re) := by
    rw [← ofReal_norm_eq_enorm, Complex.norm_cpow_eq_rpow_re_of_pos (Dt_pos g)]
  have h3 : ‖th Φ g‖ₑ ≤ ∑' ξ : NZ, ‖Φ (row ξ.1 g)‖ₑ := enorm_tsum_le_tsum_enorm
  simp only [enorm_mul, h1, h2, mul_one]
  gcongr

theorem integrand_theta_eq {H : G2 → ℂ} {Φ Φ' : (Fin 2 → 𝔸[ℚ]) → ℂ} (c : HeckeCharacter ℚ) (s : ℂ) (g : G2)
    (hth : th Φ g + Φ 0 = (((Dt g)⁻¹ : ℝ) : ℂ) * (th Φ' (inv2 g) + Φ' 0)) :
    H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s * th Φ g =
      H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ (s - 1) * th Φ' (inv2 g)
        + Φ' 0 * (H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ (s - 1))
        - Φ 0 * (H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s) := by
  have hD := Dt_ne g
  have hp : ((Dt g : ℝ) : ℂ) ^ (s - 1) = ((Dt g : ℝ) : ℂ) ^ s * (((Dt g)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.cpow_sub _ _ hD, Complex.cpow_one, Complex.ofReal_inv, div_eq_mul_inv]
  have ht : th Φ g = (((Dt g)⁻¹ : ℝ) : ℂ) * (th Φ' (inv2 g) + Φ' 0) - Φ 0 := by
    rw [← hth]; ring
  rw [hp, ht]; ring

theorem setIntegral_lower_det_inverse_twist {μ : Measure G2} {𝓕 : Set G2} {H : G2 → ℂ}
    {Φ' : (Fin 2 → 𝔸[ℚ]) → ℂ} (c : HeckeCharacter ℚ) (hH : Aut H) (s : ℂ)
    (hm : MeasurableSet 𝓕) (hnull : μ {g | Dt g = 1} = 0)
    (hT : ∀ F : G2 → ℂ, Measurable F → LInv F → ∫ g in 𝓕, F (inv2 g) ∂μ = ∫ g in 𝓕, F g ∂μ)
    (mth : Measurable (th Φ')) (lth : LInv (th Φ')) :
    ∫ g in 𝓕 ∩ {g | Dt g < 1}, H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ (s - 1) * th Φ' (inv2 g) ∂μ =
      Zp μ 𝓕 H c⁻¹ Φ' (1 - s) := by
  have hB : MeasurableSet {g | Dt g < 1} := measurableSet_lt measurable_Dt measurable_const
  have hC : MeasurableSet {g | Dt g ∈ Set.Ioi (1 : ℝ)} := measurable_Dt measurableSet_Ioi
  set G : G2 → ℂ := fun g => H g * cdet c⁻¹ g * ((Dt g : ℝ) : ℂ) ^ (1 - s) * th Φ' g with hG
  have mG : Measurable G := (measurable_w hH c⁻¹ (1 - s)).mul mth
  have lG : LInv G := fun γ g => by
    have := linv_w hH c⁻¹ (1 - s) γ g
    simp only [hG, lth γ g]
    simp only at this
    rw [this]
  have key := hT _ (mG.indicator hC) (linv_ind lG (Set.Ioi (1 : ℝ)))
  have hpt : ∀ g, Set.indicator {g | Dt g ∈ Set.Ioi (1 : ℝ)} G (inv2 g) =
      Set.indicator {g | Dt g < 1} (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ (s - 1) * th Φ' (inv2 g)) g := by
    intro g
    have hiff : inv2 g ∈ {g | Dt g ∈ Set.Ioi (1 : ℝ)} ↔ g ∈ {g | Dt g < 1} := by
      simp only [Set.mem_setOf_eq, Set.mem_Ioi, module_det_inverse_twist]
      exact one_lt_inv₀ (Dt_pos g)
    by_cases h : g ∈ {g | Dt g < 1}
    · rw [Set.indicator_of_mem (hiff.2 h), Set.indicator_of_mem h]
      simp only [hG, character_det_inverse_twist, inv_inv, module_cpow_det_inverse_twist, Aut.inv2 hH, neg_sub]
    · rw [Set.indicator_of_notMem (fun h' => h (hiff.1 h')), Set.indicator_of_notMem h]
  simp only [hpt] at key
  rw [setIntegral_indicator hB, setIntegral_indicator hC] at key
  rw [key]
  refine setIntegral_congr_set ?_
  have hae : ∀ᵐ g ∂μ, Dt g ≠ 1 := by
    have : μ ({g | Dt g ≠ 1}ᶜ) = 0 := by
      convert hnull using 2
      ext g; simp
    exact this
  refine Filter.eventuallyEq_set.2 ?_
  filter_upwards [hae] with g hg
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ioi]
  exact and_congr_right fun _ => ⟨fun h => h.le, fun h => lt_of_le_of_ne h (Ne.symm hg)⟩

theorem Zg_decomposition : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (Φ Φ' : (Fin 2 → 𝔸[ℚ]) → ℂ) (c : HeckeCharacter ℚ),
  Ad3.R.G1a → Ad3.R.G3 → Set0 μ 𝓕 mK 𝓓 → Aut H → Φ ∈ Adele2.schwartzBruhat2 ℚ → Φ' ∈ Adele2.schwartzBruhat2 ℚ →
  (∀ g, th Φ g + Φ 0 = (((Dt g)⁻¹ : ℝ) : ℂ) * (th Φ' (inv2 g) + Φ' 0)) →
  (∀ t : ℂ, 0 < t.re → IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ t) (𝓕 ∩ {g | Dt g < 1}) μ) →
  ∀ s : ℂ, 1 < s.re → Zg μ 𝓕 H c Φ s = GlobalTheory.CompanionTheory.RSZeta.Zp μ 𝓕 H c Φ s + GlobalTheory.CompanionTheory.RSZeta.Zp μ 𝓕 H c⁻¹ Φ' (1 - s)
    + Φ' 0 * GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c (s - 1) - Φ 0 * GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c s := by
  intro μ 𝓕 mK 𝓓 H Φ Φ' c h1 h3 h0 hH hΦ hΦ' hth hw s hs
  obtain ⟨mth, -, fin⟩ := h3 μ 𝓕 mK 𝓓 h0 H hH Φ hΦ s.re hs
  obtain ⟨mth', lth', -⟩ := h3 μ 𝓕 mK 𝓓 h0 H hH Φ' hΦ' 2 (by norm_num)
  obtain ⟨hnull, -, hT⟩ := h1 μ 𝓕 mK 𝓓 h0
  have hWi := integrableOn_Zg_integrand c hH s mth fin
  have hA : MeasurableSet {g | 1 ≤ Dt g} := measurableSet_le measurable_const measurable_Dt
  have hinv := setIntegral_lower_det_inverse_twist (Φ' := Φ') c hH s h0.meas hnull
    (fun F mF lF => (hT inv2 (Or.inl rfl)).2 F mF lF) mth' lth'
  have hw1 := hw (s - 1) (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  have hw2 := hw s (by linarith)
  have hWB : IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s * th Φ g)
      (𝓕 ∩ {g | Dt g < 1}) μ := hWi.mono_set Set.inter_subset_left
  have hpt := fun g => integrand_theta_eq (H := H) c s g (hth g)
  have hVi : IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ (s - 1) * th Φ' (inv2 g))
      (𝓕 ∩ {g | Dt g < 1}) μ := by
    have := (hWB.sub (hw1.const_mul (Φ' 0))).add (hw2.const_mul (Φ 0))
    refine this.congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [Pi.add_apply, Pi.sub_apply, hpt g]
    ring
  have hsplit : Zg μ 𝓕 H c Φ s = Zp μ 𝓕 H c Φ s +
      ∫ g in 𝓕 ∩ {g | Dt g < 1}, H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s * th Φ g ∂μ := by
    have hd : 𝓕 \ {g | 1 ≤ Dt g} = 𝓕 ∩ {g | Dt g < 1} := by
      ext g; simp
    rw [← hd]
    exact (integral_inter_add_diff hA hWi).symm
  have hB : ∫ g in 𝓕 ∩ {g | Dt g < 1}, H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s * th Φ g ∂μ =
      Zp μ 𝓕 H c⁻¹ Φ' (1 - s) + Φ' 0 * Jl μ 𝓕 H c (s - 1) - Φ 0 * Jl μ 𝓕 H c s := by
    have i1 : Integrable (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ (s - 1) * th Φ' (inv2 g)
        + Φ' 0 * (H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ (s - 1))) (μ.restrict (𝓕 ∩ {g | Dt g < 1})) :=
      hVi.add (hw1.const_mul _)
    simp only [hpt]
    rw [integral_sub i1 (hw2.const_mul _), integral_add hVi (hw1.const_mul _),
      integral_const_mul, integral_const_mul, hinv, Jl, Jl]
  rw [hsplit, hB]; ring

end GlobalTheory.CompanionTheory.RSZeta
end

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_zeta_integral_functional_equation : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (Φ Φ' : (Fin 2 → 𝔸[ℚ]) → ℂ) (c : HeckeCharacter ℚ),
  Ad3.R.G1a → Ad3.R.G3 → Set0 μ 𝓕 mK 𝓓 → Aut H → Φ ∈ Adele2.schwartzBruhat2 ℚ → Φ' ∈ Adele2.schwartzBruhat2 ℚ →
  (∀ g, th Φ g + Φ 0 = (((Dt g)⁻¹ : ℝ) : ℂ) * (th Φ' (inv2 g) + Φ' 0)) →
  (∀ t : ℂ, 0 < t.re → IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ t) (𝓕 ∩ {g | Dt g < 1}) μ) →
  ∀ s : ℂ, 1 < s.re → Zg μ 𝓕 H c Φ s = GlobalTheory.CompanionTheory.RSZeta.Zp μ 𝓕 H c Φ s + GlobalTheory.CompanionTheory.RSZeta.Zp μ 𝓕 H c⁻¹ Φ' (1 - s)
    + Φ' 0 * GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c (s - 1) - Φ 0 * GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c s := by
  atlas_forward_decl GlobalTheory.CompanionTheory.RSZeta.Zg_decomposition
end

section
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RSZeta

theorem two_cpow_ne_one {s : ℂ} (hs : 0 < s.re) : (1 : ℂ) - 2 ^ (-s) ≠ 0 := by
  intro h
  have h1 : ‖(2 : ℂ) ^ (-s)‖ = 1 := by rw [← sub_eq_zero.1 h]; simp
  have h2 : ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by simp, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    simp
  have h3 : (2 : ℝ) ^ (-s.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  linarith

def Jh (μ : Measure G2) (𝓕 : Set G2) (H : G2 → ℂ) (c : HeckeCharacter ℚ) (s : ℂ) : ℂ :=
  Bd μ 𝓕 H c s * 2 ^ (-s) / (1 - 2 ^ (-s))

def Ed (μ : Measure G2) (𝓕 : Set G2) (H : G2 → ℂ) (c : HeckeCharacter ℚ) (Φ Φ' : (Fin 2 → 𝔸[ℚ]) → ℂ) (s : ℂ) : ℂ :=
  (1 - 2 ^ (1 - s)) * (Zp μ 𝓕 H c Φ s + Zp μ 𝓕 H c⁻¹ Φ' (1 - s) - Φ 0 * Jh μ 𝓕 H c s)
    + Φ' 0 * 2 ^ (1 - s) * Bd μ 𝓕 H c (s - 1)

theorem Ed_diff {μ : Measure G2} {𝓕 : Set G2} {H : G2 → ℂ} {c : HeckeCharacter ℚ} {Φ Φ' : (Fin 2 → 𝔸[ℚ]) → ℂ}
    (h1 : Differentiable ℂ (Zp μ 𝓕 H c Φ)) (h2 : Differentiable ℂ (Zp μ 𝓕 H c⁻¹ Φ'))
    (h3 : Differentiable ℂ (Bd μ 𝓕 H c)) : DifferentiableOn ℂ (Ed μ 𝓕 H c Φ Φ') {s | 0 < s.re} := by
  have hp : ∀ f : ℂ → ℂ, Differentiable ℂ f → Differentiable ℂ fun s => (2 : ℂ) ^ f s := fun f hf s =>
    (hf s).const_cpow (Or.inl (by norm_num))
  have e1 : Differentiable ℂ fun s : ℂ => (2 : ℂ) ^ (1 - s) := hp _ (by fun_prop)
  have e2 : Differentiable ℂ fun s : ℂ => (2 : ℂ) ^ (-s) := hp _ (by fun_prop)
  have e3 : Differentiable ℂ fun s : ℂ => Zp μ 𝓕 H c⁻¹ Φ' (1 - s) := h2.comp (by fun_prop)
  have e4 : Differentiable ℂ fun s : ℂ => Bd μ 𝓕 H c (s - 1) := h3.comp (by fun_prop)
  have e5 : DifferentiableOn ℂ (Jh μ 𝓕 H c) {s | 0 < s.re} := by
    intro s hs
    refine DifferentiableAt.differentiableWithinAt ?_
    exact ((h3 s).mul (e2 s)).div ((differentiableAt_const _).sub (e2 s)) (two_cpow_ne_one hs)
  unfold Ed
  exact (((differentiable_const _).sub e1).differentiableOn.mul
    ((h1.add e3).differentiableOn.sub ((differentiable_const _).differentiableOn.mul e5))).add
    (((differentiable_const _).mul e1).mul e4).differentiableOn

theorem Ed_eq {μ : Measure G2} {𝓕 : Set G2} {H : G2 → ℂ} {c : HeckeCharacter ℚ} {Φ Φ' : (Fin 2 → 𝔸[ℚ]) → ℂ} {s : ℂ}
    (hs : 1 < s.re)
    (hz : Zg μ 𝓕 H c Φ s = Zp μ 𝓕 H c Φ s + Zp μ 𝓕 H c⁻¹ Φ' (1 - s) + Φ' 0 * Jl μ 𝓕 H c (s - 1) - Φ 0 * Jl μ 𝓕 H c s)
    (h0 : Jl μ 𝓕 H c s * (1 - 2 ^ (-s)) = Bd μ 𝓕 H c s * 2 ^ (-s))
    (h1 : Jl μ 𝓕 H c (s - 1) * (1 - 2 ^ (-(s - 1))) = Bd μ 𝓕 H c (s - 1) * 2 ^ (-(s - 1))) :
    Ed μ 𝓕 H c Φ Φ' s = (1 - 2 ^ (1 - s)) * Zg μ 𝓕 H c Φ s := by
  have n0 := two_cpow_ne_one (s := s) (by linarith)
  have e : Jh μ 𝓕 H c s = Jl μ 𝓕 H c s := by rw [Jh, ← h0, mul_div_assoc, div_self n0, mul_one]
  rw [neg_sub] at h1
  rw [Ed, e, hz]
  linear_combination (-Φ' 0) * h1

theorem Ed_fe {μ : Measure G2} {𝓕 : Set G2} {H : G2 → ℂ} {c : HeckeCharacter ℚ} {Φ Φ' : (Fin 2 → 𝔸[ℚ]) → ℂ} {s : ℂ}
    (hs : Strip s)
    (b0 : Bd μ 𝓕 H c⁻¹ (-s) = 2 ^ (-s) * Bd μ 𝓕 H c s)
    (b1 : Bd μ 𝓕 H c⁻¹ (-(s - 1)) = 2 ^ (-(s - 1)) * Bd μ 𝓕 H c (s - 1)) :
    (1 - 2 ^ s) * Ed μ 𝓕 H c Φ Φ' s = (1 - 2 ^ (1 - s)) * Ed μ 𝓕 H c⁻¹ Φ' Φ (1 - s) := by
  have n0 := two_cpow_ne_one (s := s) hs.1
  have n1 := two_cpow_ne_one (s := 1 - s) (by simpa using hs.2)
  have x0 : (2 : ℂ) ^ s ≠ 0 := by simp
  have x1 : (2 : ℂ) ^ (1 - s) ≠ 0 := by simp
  have i0 : (2 : ℂ) ^ (-s) = (2 ^ s)⁻¹ := Complex.cpow_neg _ _
  have i1 : (2 : ℂ) ^ (-(1 - s)) = (2 ^ (1 - s))⁻¹ := Complex.cpow_neg _ _
  rw [neg_sub] at b1
  simp only [Ed, Jh, inv_inv, sub_sub_cancel, show 1 - s - 1 = -s by ring, b0, b1]
  rw [i0] at n0 ⊢
  rw [i1] at n1 ⊢
  generalize (2 : ℂ) ^ s = x at *
  generalize (2 : ℂ) ^ (1 - s) = y at *
  generalize Bd μ 𝓕 H c s = A at *
  generalize Bd μ 𝓕 H c (s - 1) = M at *
  have hx : x - 1 ≠ 0 := fun h => n0 (by rw [sub_eq_zero.1 h]; simp)
  have hy : y - 1 ≠ 0 := fun h => n1 (by rw [sub_eq_zero.1 h]; simp)
  have hx' : 1 - x⁻¹ = (x - 1) / x := by field_simp
  have hy' : 1 - y⁻¹ = (y - 1) / y := by field_simp
  rw [hx', hy']
  field_simp
  ring

end GlobalTheory.CompanionTheory.RSZeta

theorem GlobalTheory.CompanionTheory.RSZeta.functional_equation : Ad3.R.G1a → Ad3.R.G3 → Ad3.R.AdelicThetaPoissonSummation → Ad3.R.G4 := by
  intro hG1 hG3 hG4a μ 𝓕 mK 𝓓 hS H hH Φ hΦ c hc
  obtain ⟨hΦ', hΦ'', hrel⟩ := hG4a Φ hΦ
  have hci : IsOfFinOrder c⁻¹ := hc.inv
  have hrel' : ∀ g, th (sFA Φ) g + sFA Φ 0 = (((Dt g)⁻¹ : ℝ) : ℂ) * (th Φ (inv2 g) + Φ 0) := by
    intro g
    have h := hrel (inv2 g)
    rw [GlobalTheory.CompanionTheory.RSZeta.det_inverse_twist_involutive, GlobalTheory.CompanionTheory.RSZeta.module_det_inverse_twist, inv_inv] at h
    rw [h, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (GlobalTheory.CompanionTheory.RSZeta.Dt_pos g).ne']
    simp
  have I1 := GlobalTheory.T.integrableOn_lower_zeta_integrand μ 𝓕 mK 𝓓 H c hG1 hS hH hc
  have I2 := GlobalTheory.T.integrableOn_lower_zeta_integrand μ 𝓕 mK 𝓓 H c⁻¹ hG1 hS hH hci
  have d1 := GlobalTheory.T.differentiable_partial_zeta_integral μ 𝓕 mK 𝓓 H Φ c hG3 hS hH hΦ
  have d2 := GlobalTheory.T.differentiable_partial_zeta_integral μ 𝓕 mK 𝓓 H (sFA Φ) c⁻¹ hG3 hS hH hΦ'
  have d1' := GlobalTheory.T.differentiable_partial_zeta_integral μ 𝓕 mK 𝓓 H Φ c⁻¹⁻¹ hG3 hS hH hΦ
  have d2' := GlobalTheory.T.differentiable_partial_zeta_integral μ 𝓕 mK 𝓓 H (sFA Φ) c⁻¹ hG3 hS hH hΦ'
  have b1 := GlobalTheory.T.differentiable_boundary_zeta_term μ 𝓕 mK 𝓓 H c hS hH
  have b2 := GlobalTheory.T.differentiable_boundary_zeta_term μ 𝓕 mK 𝓓 H c⁻¹ hS hH
  refine ⟨GlobalTheory.CompanionTheory.RSZeta.Ed μ 𝓕 H c Φ (sFA Φ), GlobalTheory.CompanionTheory.RSZeta.Ed μ 𝓕 H c⁻¹ (sFA Φ) Φ,
    GlobalTheory.CompanionTheory.RSZeta.Ed_diff d1 d2 b1, GlobalTheory.CompanionTheory.RSZeta.Ed_diff d2' d1' b2, ?_, ?_, ?_⟩
  · intro s hs
    have hs1 : 0 < (s - 1).re := by simp; linarith
    have hs0 : 0 < s.re := by linarith
    refine ⟨GlobalTheory.CompanionTheory.RSZeta.Ed_eq hs (GlobalTheory.T.global_zeta_integral_functional_equation μ 𝓕 mK 𝓓 H Φ (sFA Φ) c hG1 hG3 hS hH hΦ hΦ' hrel I1 s hs)
      (GlobalTheory.T.lower_zeta_integral_boundary_relation μ 𝓕 mK 𝓓 H c hG1 hS hH hc s (I1 s hs0)) (GlobalTheory.T.lower_zeta_integral_boundary_relation μ 𝓕 mK 𝓓 H c hG1 hS hH hc _ (I1 _ hs1)),
      GlobalTheory.CompanionTheory.RSZeta.Ed_eq hs (GlobalTheory.T.global_zeta_integral_functional_equation μ 𝓕 mK 𝓓 H (sFA Φ) Φ c⁻¹ hG1 hG3 hS hH hΦ' hΦ hrel' I2 s hs)
      (GlobalTheory.T.lower_zeta_integral_boundary_relation μ 𝓕 mK 𝓓 H c⁻¹ hG1 hS hH hci s (I2 s hs0)) (GlobalTheory.T.lower_zeta_integral_boundary_relation μ 𝓕 mK 𝓓 H c⁻¹ hG1 hS hH hci _ (I2 _ hs1))⟩
  · intro s hs
    exact GlobalTheory.CompanionTheory.RSZeta.Ed_fe hs (GlobalTheory.T.boundary_zeta_term_functional_equation μ 𝓕 mK 𝓓 H c hG1 hS hH hc s) (GlobalTheory.T.boundary_zeta_term_functional_equation μ 𝓕 mK 𝓓 H c hG1 hS hH hc (s - 1))
  · intro h1 h0
    apply h1
    have : GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c 0 = 0 := by
      simpa [GlobalTheory.CompanionTheory.RSZeta.Bd] using h0
    simp [GlobalTheory.CompanionTheory.RSZeta.Ed, this]
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_zeta_integral_convergence : Ad3.R.G1a → Ad3.R.G3 → Ad3.R.AdelicThetaPoissonSummation → Ad3.R.G4 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.RSZeta.functional_equation
end
