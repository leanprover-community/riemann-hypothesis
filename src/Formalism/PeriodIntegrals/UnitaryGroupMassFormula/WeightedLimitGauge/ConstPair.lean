import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE

section
noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

def pairF (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (x : Mt k r) : ℂ :=
  herm (Hpk k r) (Matrix.of x *ᵥ z') z

def pairConst (k : ℕ) (T T' : ℝ) : ℝ := 2 * volU k ^ 2 / ((T * T') ^ k * volU (k - 1))

def RhsTest : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    WbData k r z z' μW μW' a a' μsec → ∀ g : ℂ → ℝ≥0∞, Measurable g →
      rhsW k r z z' μW μW' μsec (fun x => g (pairF k r z z' x)) =
        ENNReal.ofReal (a * a') * ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * g ζ

def PairPush : Prop :=
  ∀ (k r : ℕ) (νg : Measure (Mt k r)), 1 ≤ k → IsGaugeOn k r (UWb k r) νg →
    ∀ z z' : Fin (2 * r + k + 1) → ℂ, inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ g : ℂ → ℝ≥0∞, Measurable g →
      ∫⁻ x, g (pairF k r z z' x) ∂νg = ENNReal.ofReal (pairConst k (Tz k r z) (Tz k r z')) *
        ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * g ζ

def rmulM {k r : ℕ} (p : Mat k r) (x : Mt k r) : Mt k r := Matrix.of x * p

def TransW : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∃ p ∈ UWb k r, p *ᵥ ((Real.sqrt (Tz k r z) : ℂ) • wLast k r) = z

def UnimodW : Prop :=
  ∀ (k r : ℕ) (ν : Measure (Mt k r)), 1 ≤ k → IsGaugeOn k r (UWb k r) ν →
    ∀ p ∈ UWb k r, ν.map (rmulM p) = ν

def OrbitPushG : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z' → 0 < Tz k r z' →
    ∀ νg : Measure (Mt k r), IsGaugeOn k r (UWb k r) νg →
    ∀ f : (Fin k → ℂ) × ℂ → ℝ≥0∞, Measurable f →
      ∫⁻ x, f (fun i => (Matrix.of x *ᵥ z') (wI k r (Fin.castSucc i)),
          (Matrix.of x *ᵥ z') (wI k r (Fin.last k))) ∂νg =
        ENNReal.ofReal (volU k * 2 ^ (k + 1) / Tz k r z' ^ k) * hypMeas k (Tz k r z') f

theorem volU_pos (j : ℕ) : 0 < volU j :=
  Finset.prod_pos fun i _ => by positivity

theorem continuous_pairF (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Continuous (pairF k r z z') := by
  unfold pairF herm
  exact continuous_const.dotProduct (continuous_const.matrix_mulVec
    ((show Continuous fun x : Mt k r => Matrix.of x from continuous_id).matrix_mulVec continuous_const))

theorem gauge_of_lim {k r : ℕ} (νg : Measure (Mt k r)) (hH : IsHaarOn (UWb k r) νg)
    (hL : ∀ m ∈ UWb k r, Tendsto (fun ρ : ℝ => (νg (tBall k r m ρ)).toReal / bVol k r ρ) (𝓝[>] 0) (𝓝 1)) :
    IsGaugeOn k r (UWb k r) νg := by
  refine ⟨hH, ?_⟩
  have h1 : (1 : Mat k r) ∈ UWb k r := by
    refine ⟨?_, fun a => ⟨?_, ?_⟩⟩ <;> simp [UH]
  have e : ∀ ρ, tBall k r 1 ρ = expBall (k := k) (r := r) (UWb k r) ρ := fun ρ => by
    ext x
    simp [tBall, bBall]
  have h2 := hL 1 h1
  simp only [e] at h2
  exact h2

def annU (T T' : ℝ) : Set ℂ := {ζ | T * T' < Complex.normSq ζ ∧ Complex.normSq ζ < 4 * (T * T')}

theorem annU_open (T T' : ℝ) : IsOpen (annU T T') :=
  (isOpen_lt continuous_const Complex.continuous_normSq).inter
    (isOpen_lt Complex.continuous_normSq continuous_const)

theorem testJ (k : ℕ) (T T' : ℝ) (hTT : 0 < T * T') :
    0 < ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k T T' ζ) * (annU T T').indicator 1 ζ ∧
      ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k T T' ζ) * (annU T T').indicator 1 ζ < ⊤ := by
  have hAo : IsOpen (annU T T') := annU_open T T'
  constructor
  ·
    have hVo : IsOpen {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')} :=
      (isOpen_lt continuous_const Complex.continuous_normSq).inter
        (isOpen_lt Complex.continuous_normSq continuous_const)
    have hVne : {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')}.Nonempty := by
      refine ⟨((Real.sqrt (5 / 2 * (T * T')) : ℝ) : ℂ), ?_, ?_⟩ <;>
        rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by positivity)] <;> linarith
    have hVpos := hVo.measure_pos volume hVne
    have hle : ∀ ζ, ENNReal.ofReal ((T * T') ^ (k - 1)) *
        {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')}.indicator 1 ζ ≤
        ENNReal.ofReal (zWeight k T T' ζ) * (annU T T').indicator 1 ζ := by
      intro ζ
      by_cases hζ : 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')
      · have hU : ζ ∈ annU T T' := ⟨by linarith [hζ.1], by linarith [hζ.2]⟩
        have hV : ζ ∈ {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')} := hζ
        rw [Set.indicator_of_mem hV, Set.indicator_of_mem hU, Pi.one_apply, mul_one, mul_one]
        apply ENNReal.ofReal_le_ofReal
        unfold zWeight
        rw [if_pos (by linarith [hζ.1])]
        exact pow_le_pow_left₀ hTT.le (by linarith [hζ.1]) _
      · have hV : ζ ∉ {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')} := hζ
        simp [Set.indicator_apply, hV]
    calc (0 : ℝ≥0∞) < ENNReal.ofReal ((T * T') ^ (k - 1)) *
          volume {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')} :=
          ENNReal.mul_pos (ENNReal.ofReal_pos.2 (pow_pos hTT _)).ne' hVpos.ne'
      _ = ∫⁻ ζ, ENNReal.ofReal ((T * T') ^ (k - 1)) *
          {ζ : ℂ | 2 * (T * T') < Complex.normSq ζ ∧ Complex.normSq ζ < 3 * (T * T')}.indicator 1 ζ := by
          rw [lintegral_const_mul _ (measurable_one.indicator hVo.measurableSet),
            lintegral_indicator_one hVo.measurableSet]
      _ ≤ _ := lintegral_mono hle
  · have hM : ∀ ζ, ENNReal.ofReal (zWeight k T T' ζ) * (annU T T').indicator 1 ζ ≤
        ENNReal.ofReal ((3 * (T * T')) ^ (k - 1)) * (annU T T').indicator 1 ζ := by
      intro ζ
      by_cases hζ : ζ ∈ annU T T'
      · rw [Set.indicator_of_mem hζ, Pi.one_apply, mul_one, mul_one]
        apply ENNReal.ofReal_le_ofReal
        unfold zWeight
        rw [if_pos hζ.1.le]
        exact pow_le_pow_left₀ (by linarith [hζ.1]) (by linarith [hζ.2]) _
      · simp [Set.indicator_apply, hζ]
    have hsub : annU T T' ⊆ Metric.ball 0 (2 * Real.sqrt (T * T') + 1) := by
      intro ζ hζ
      rw [Metric.mem_ball, dist_zero_right]
      have h1 : ‖ζ‖ ^ 2 < (2 * Real.sqrt (T * T')) ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, mul_pow, Real.sq_sqrt hTT.le]
        linarith [hζ.2]
      have h2 := lt_of_pow_lt_pow_left₀ 2 (by positivity) h1
      linarith
    have hfin : volume (annU T T') < ⊤ := (measure_mono hsub).trans_lt measure_ball_lt_top
    calc _ ≤ ∫⁻ ζ, ENNReal.ofReal ((3 * (T * T')) ^ (k - 1)) * (annU T T').indicator 1 ζ :=
          lintegral_mono hM
      _ = ENNReal.ofReal ((3 * (T * T')) ^ (k - 1)) * volume (annU T T') := by
          rw [lintegral_const_mul _ (measurable_one.indicator hAo.measurableSet),
            lintegral_indicator_one hAo.measurableSet]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

theorem constVal_of (hR : RhsTest) (hP : PairPush) : ConstVal := by
  intro k r z z' μW μW' a a' μsec hW νg c hH hL hrep
  have hg := gauge_of_lim νg hH hL
  have hT := hW.T_pos
  have hT' := hW.T'_pos
  have hTT : 0 < Tz k r z * Tz k r z' := mul_pos hT hT'
  have hgm : Measurable ((annU (Tz k r z) (Tz k r z')).indicator (1 : ℂ → ℝ≥0∞)) :=
    measurable_one.indicator (annU_open _ _).measurableSet
  have hφm : Measurable (fun x => (annU (Tz k r z) (Tz k r z')).indicator (1 : ℂ → ℝ≥0∞)
      (pairF k r z z' x)) := hgm.comp (continuous_pairF k r z z').measurable
  have h1 := hR k r z z' μW μW' a a' μsec hW _ hgm
  have h2 := hP k r νg hW.k_pos hg z z' hW.z_mem hW.z'_mem hT hT' _ hgm
  have h3 := hrep _ hφm
  obtain ⟨hJ0, hJt⟩ := testJ k (Tz k r z) (Tz k r z') hTT
  rw [h3, h2, ← mul_assoc] at h1

  have h4 := (ENNReal.mul_left_inj hJ0.ne' hJt.ne).1 h1
  have hv := volU_pos k
  have hv1 := volU_pos (k - 1)
  have hpc : 0 < pairConst k (Tz k r z) (Tz k r z') := by
    unfold pairConst
    positivity
  have ha := hW.a_pos
  have ha' := hW.a'_pos
  have h5 := congrArg ENNReal.toReal h4
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hpc.le, ENNReal.toReal_ofReal (by positivity)] at h5
  have hc : c.toReal = a * a' / pairConst k (Tz k r z) (Tz k r z') := by
    rw [← h5]
    field_simp
  rw [hc]
  unfold pairConst wbConst
  have hTk : 0 < (Tz k r z * Tz k r z') ^ k := pow_pos hTT k
  field_simp

end PI.RhsWLim.W
end
end

section
noncomputable section

namespace PI.RhsWLim.W

open PI.RhsWLim

theorem volURatio : VolURatio := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [volU, Finset.prod_range_succ, Nat.add_sub_cancel]
  ring

end PI.RhsWLim.W
end
end

section
noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

variable {k r : ℕ}

theorem herm_mulVec_right {p : Mat k r} (hp : p ∈ UH (Hpk k r)) (v u : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v (p *ᵥ u) = herm (Hpk k r) (p⁻¹ *ᵥ v) u := by
  have hu := HU.isUnit_of_uh hp
  have hp' : pᴴ * Hpk k r * p = Hpk k r := hp
  have key : pᴴ * Hpk k r = Hpk k r * p⁻¹ := by
    calc pᴴ * Hpk k r = pᴴ * Hpk k r * (p * p⁻¹) := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
      _ = (pᴴ * Hpk k r * p) * p⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Hpk k r * p⁻¹ := by rw [hp']
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec]

theorem tau_wLast : HU.tau k r (wI k r (Fin.last k)) = wI k r (Fin.last k) := by
  unfold HU.tau wI
  apply Fin.ext
  simp only [Fin.val_last]
  split_ifs <;> omega

theorem sgn_wLast : HU.sgn k r (wI k r (Fin.last k)) = -1 := by
  unfold HU.sgn wI
  simp

theorem hpk_mulVec_wLast (v : Fin (2 * r + k + 1) → ℂ) :
    (Hpk k r *ᵥ v) (wI k r (Fin.last k)) = -v (wI k r (Fin.last k)) := by
  simp only [Matrix.mulVec, dotProduct, HU.hpk_row, tau_wLast, sgn_wLast, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem herm_wLast (v : Fin (2 * r + k + 1) → ℂ) (s : ℝ) :
    herm (Hpk k r) v ((s : ℂ) • wLast k r) = -((s : ℂ) * v (wI k r (Fin.last k))) := by
  have hs : star ((s : ℂ) • wLast k r) = Pi.single (wI k r (Fin.last k)) (s : ℂ) := by
    funext j
    simp only [wLast, bvec, Pi.star_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp [Complex.conj_ofReal]
  unfold herm
  rw [hs, single_dotProduct, hpk_mulVec_wLast, mul_neg]

theorem pairF_std (z' : Fin (2 * r + k + 1) → ℂ) (s : ℝ) (x : Mt k r) :
    pairF k r ((s : ℂ) • wLast k r) z' x = -((s : ℂ) * (Matrix.of x *ᵥ z') (wI k r (Fin.last k))) :=
  herm_wLast _ _

theorem rmulM_cont (p : Mat k r) : Continuous (rmulM p : Mt k r → Mt k r) := by
  unfold rmulM
  exact (continuous_id (X := Mat k r)).matrix_mul continuous_const

theorem continuous_coords (z' : Fin (2 * r + k + 1) → ℂ) :
    Continuous fun x : Mt k r => ((fun i : Fin k => (Matrix.of x *ᵥ z') (wI k r (Fin.castSucc i))),
      (Matrix.of x *ᵥ z') (wI k r (Fin.last k))) := by
  have hc : Continuous fun x : Mt k r => Matrix.of x *ᵥ z' :=
    Continuous.matrix_mulVec (continuous_id (X := Mat k r)) continuous_const
  exact (continuous_pi fun i => (continuous_apply (wI k r (Fin.castSucc i))).comp hc).prodMk
    ((continuous_apply (wI k r (Fin.last k))).comp hc)

theorem orbitPushG_of (hO : OrbitPush) (hT : TransW) (hU : UnimodW) : OrbitPushG := by
  intro k r z' hk hz' hT' νg hG f hf
  obtain ⟨p, hp, hpz⟩ := hT k r z' hz' hT'
  set zs := ((Real.sqrt (Tz k r z') : ℂ) • wLast k r) with hzs
  have hFm := hf.comp (continuous_coords (k := k) (r := r) zs).measurable
  have e : ∀ x : Mt k r, Matrix.of x *ᵥ z' = Matrix.of (rmulM p x) *ᵥ zs := by
    intro x
    rw [← hpz]
    show Matrix.of x *ᵥ (p *ᵥ zs) = (Matrix.of x * p) *ᵥ zs
    rw [Matrix.mulVec_mulVec]
  calc ∫⁻ x, f (fun i => (Matrix.of x *ᵥ z') (wI k r (Fin.castSucc i)),
          (Matrix.of x *ᵥ z') (wI k r (Fin.last k))) ∂νg
      = ∫⁻ x, (fun y : Mt k r => f (fun i => (Matrix.of y *ᵥ zs) (wI k r (Fin.castSucc i)),
          (Matrix.of y *ᵥ zs) (wI k r (Fin.last k)))) (rmulM p x) ∂νg := by
        refine lintegral_congr fun x => ?_
        simp only [e x]
    _ = ∫⁻ y, f (fun i => (Matrix.of y *ᵥ zs) (wI k r (Fin.castSucc i)),
          (Matrix.of y *ᵥ zs) (wI k r (Fin.last k))) ∂(νg.map (rmulM p)) :=
        (lintegral_map hFm (rmulM_cont p).measurable).symm
    _ = _ := by
        rw [hU k r νg hk hG p hp]
        exact hO k r (Tz k r z') hk hT' νg hG f hf

theorem pairPush_of (hT : TransW) (hO : OrbitPushG) (h4 : PolarHyp) (h5 : VolURatio) : PairPush := by
  intro k r νg hk hG z z' hz hz' hTz hTz' g hg
  obtain ⟨p, hp, hpz⟩ := hT k r z hz hTz
  set s := Real.sqrt (Tz k r z) with hs
  have hs0 : (s : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact (Real.sqrt_pos.2 hTz).ne'
  set zs := ((s : ℂ) • wLast k r) with hzs

  have e1 : ∀ x : Mt k r, pairF k r z z' x = pairF k r zs z' (lmulM p⁻¹ x) := by
    intro x
    unfold pairF
    rw [← hpz, herm_mulVec_right hp.1, Matrix.mulVec_mulVec]
    rfl
  have hgm : Measurable fun y : Mt k r => g (pairF k r zs z' y) := hg.comp (continuous_pairF k r zs z').measurable
  have hpinv := HU.uwb_inv hp
  have step1 : ∫⁻ x, g (pairF k r z z' x) ∂νg = ∫⁻ y, g (pairF k r zs z' y) ∂νg := by
    calc ∫⁻ x, g (pairF k r z z' x) ∂νg = ∫⁻ x, (fun y => g (pairF k r zs z' y)) (lmulM p⁻¹ x) ∂νg := by
          refine lintegral_congr fun x => ?_
          simp only [e1 x]
      _ = ∫⁻ y, g (pairF k r zs z' y) ∂(νg.map (lmulM p⁻¹)) :=
          (lintegral_map hgm (HU.lmulM_cont _).measurable).symm
      _ = _ := by rw [hG.1.2.2.2 _ hpinv]

  set f : (Fin k → ℂ) × ℂ → ℝ≥0∞ := fun v => g (-((s : ℂ) * v.2)) with hf
  have hfm : Measurable f := hg.comp (continuous_const.mul continuous_snd).neg.measurable
  have step2 := hO k r z' hk hz' hTz' νg hG f hfm

  set G : ℝ → ℂ → ℝ≥0∞ := fun _ c => g (-((s : ℂ) * c)) with hGdef
  have hGm : Measurable (Function.uncurry G) :=
    hg.comp (continuous_const.mul continuous_snd).neg.measurable
  have step3 := h4 k (Tz k r z) (Tz k r z') hk hTz hTz' G hGm
  rw [← hs] at step3
  have hcancel : ∀ ζ : ℂ, -((s : ℂ) * -(ζ / (s : ℂ))) = ζ := by
    intro ζ; field_simp
  rw [step1]
  have e2 : ∫⁻ y, g (pairF k r zs z' y) ∂νg = ∫⁻ x, f (fun i => (Matrix.of x *ᵥ z') (wI k r (Fin.castSucc i)),
          (Matrix.of x *ᵥ z') (wI k r (Fin.last k))) ∂νg := by
    refine lintegral_congr fun x => ?_
    rw [pairF_std]
  rw [e2, step2]
  have e3 : hypMeas k (Tz k r z') f =
      hypMeas k (Tz k r z') (fun v => G ‖(WithLp.equiv 2 (Fin k → ℂ)).symm v.1‖ v.2) := rfl
  rw [e3, step3]
  simp only [hGdef, hcancel]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by have := volU_pos k; positivity)]
  congr 2
  have hV := h5 k hk
  have h1 := volU_pos (k - 1)
  have h2 : ((k - 1).factorial : ℝ) ≠ 0 := by positivity
  have h3 := Real.pi_pos
  have h4 : Tz k r z ≠ 0 := hTz.ne'
  have h5 : Tz k r z' ≠ 0 := hTz'.ne'
  unfold pairConst
  rw [hV]
  field_simp
  ring

theorem constVal_of_polarHyp (hR : RhsTest) (hT : TransW) (hU : UnimodW) (hO : OrbitPush) (h4 : PolarHyp) :
    ConstVal :=
  constVal_of hR (pairPush_of hT (orbitPushG_of hO hT hU) h4 volURatio)

end PI.RhsWLim.W
end
end
