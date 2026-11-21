import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Assembly
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsSphereLaw
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SphereMean
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PFibreMahlerForms
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsLocalGlobalIndex
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLatticeOfLocalisations
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLocalChange
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLocalLatticeIndex
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsLocalLatticeIndex

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ProbabilityTheory

noncomputable section

namespace SphereLawBasic

def firstRow (N : ℕ) : (Fin 1 × Fin N → ℂ) →ₗ[ℝ] (Fin N → ℂ) where
  toFun u j := u (0, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem firstRow_apply (N : ℕ) (u : Fin 1 × Fin N → ℂ) (j : Fin N) : firstRow N u j = u (0, j) :=
  rfl

theorem sphereNormalize_eq (N : ℕ) (u : Fin 1 × Fin N → ℂ) :
    (fun j ↦ sphereNormalize (HermNorm.std N) 1 u (0, j)) =
      ((√(∑ i, ‖u (0, i)‖ ^ 2) : ℝ) : ℂ)⁻¹ • firstRow N u := by
  ext j
  simp [sphereNormalize, HermNorm.std_norm_eq, firstRow_apply]

theorem firstRow_eq_zero (N : ℕ) (u : Fin 1 × Fin N → ℂ) (h : ∑ i, ‖u (0, i)‖ ^ 2 ≤ 0) :
    firstRow N u = 0 := by
  have h' := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ sq_nonneg ‖u (0, i)‖)).mp
    (le_antisymm h (Finset.sum_nonneg fun i _ ↦ sq_nonneg _))
  ext j
  simpa [firstRow_apply] using h' j (Finset.mem_univ j)

theorem volume_firstRow_mem (N : ℕ) (S : Submodule ℂ (Fin N → ℂ)) (hS : S ≠ ⊤) :
    volume {u : Fin 1 × Fin N → ℂ | firstRow N u ∈ S} = 0 := by
  let T : Submodule ℝ (Fin 1 × Fin N → ℂ) := (S.restrictScalars ℝ).comap (firstRow N)
  have hT : T ≠ ⊤ := by
    intro h
    apply hS
    rw [eq_top_iff]
    intro v _
    let u : Fin 1 × Fin N → ℂ := fun ij ↦ v ij.2
    have hu : u ∈ T := h ▸ Submodule.mem_top
    exact hu
  exact Measure.addHaar_submodule volume T hT

end SphereLawBasic

open SphereLawBasic in

theorem SphereLawBasic.proof : SphereLawBasic.Statement := by
  intro N hN
  have hf : Measurable fun (u : Fin 1 × Fin N → ℂ) (j : Fin N) ↦
      sphereNormalize (HermNorm.std N) 1 u (0, j) := by
    unfold sphereNormalize
    simp only [HermNorm.std_norm_eq]
    fun_prop
  have hbot : (⊥ : Submodule ℂ (Fin N → ℂ)) ≠ ⊤ := by
    intro h
    have hmem : (Pi.single ⟨0, hN⟩ 1 : Fin N → ℂ) ∈ (⊥ : Submodule ℂ (Fin N → ℂ)) :=
      h ▸ Submodule.mem_top
    simpa using congrFun ((Submodule.mem_bot ℂ).mp hmem) ⟨0, hN⟩
  have h0 : ∀ᵐ u ∂(volume[|sphereBall (HermNorm.std N) 1]), firstRow N u ≠ 0 := by
    refine cond_absolutelyContinuous.ae_le ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (volume_firstRow_mem N ⊥ hbot)] with u hu
    simpa using hu
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [sphereLaw, ae_map_iff hf.aemeasurable (measurableSet_eq_fun (by fun_prop) measurable_const)]
    filter_upwards [h0] with u hu
    have hs : 0 < ∑ i, ‖u (0, i)‖ ^ 2 := lt_of_not_ge fun h ↦ hu (firstRow_eq_zero N u h)
    have key : ∀ j, ‖sphereNormalize (HermNorm.std N) 1 u (0, j)‖ ^ 2 =
        (∑ i, ‖u (0, i)‖ ^ 2)⁻¹ * ‖u (0, j)‖ ^ 2 := by
      intro j
      have e := congrFun (sphereNormalize_eq N u) j
      rw [e]
      simp only [Pi.smul_apply, smul_eq_mul, firstRow_apply, norm_mul, norm_inv,
        Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow,
        Real.sq_sqrt hs.le]
    simp only [key, ← Finset.mul_sum]
    exact inv_mul_cancel₀ hs.ne'
  · intro S hS
    have hSm : MeasurableSet (S : Set (Fin N → ℂ)) :=
      (S.restrictScalars ℝ).closed_of_finiteDimensional.measurableSet
    rw [sphereLaw, Measure.map_apply hf hSm]
    refine measure_mono_null ?_ (cond_absolutelyContinuous (volume_firstRow_mem N S hS))
    intro u hu
    simp only [Set.mem_preimage, SetLike.mem_coe] at hu
    rw [sphereNormalize_eq] at hu
    show firstRow N u ∈ S
    by_cases hc : ((√(∑ i, ‖u (0, i)‖ ^ 2) : ℝ) : ℂ) = 0
    · have hle : ∑ i, ‖u (0, i)‖ ^ 2 ≤ 0 := Real.sqrt_eq_zero'.mp (by exact_mod_cast hc)
      rw [firstRow_eq_zero N u hle]
      exact S.zero_mem
    · have := S.smul_mem ((√(∑ i, ‖u (0, i)‖ ^ 2) : ℝ) : ℂ) hu
      rwa [smul_smul, mul_inv_cancel₀ hc, one_smul] at this

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ProbabilityTheory Set Real

noncomputable section

namespace SphereLawFirstCoord

open SphereMean

theorem volume_annulus {a : ℝ} (ha : 0 ≤ a) (s : ℝ) :
    volume {w : ℂ | a ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 < s} = ENNReal.ofReal (s - a) * NNReal.pi := by
  rcases le_or_gt s a with hsa | hsa
  · have : {w : ℂ | a ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 < s} = ∅ := by
      ext w
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
      intro h
      linarith
    rw [this, measure_empty, ENNReal.ofReal_of_nonpos (by linarith), zero_mul]
  · have hset : {w : ℂ | a ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 < s} = Metric.ball 0 √s \ Metric.ball 0 √a := by
      ext w
      simp only [mem_ofPred_eq, mem_sdiff, Metric.mem_ball, dist_zero_right, not_lt]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(Real.lt_sqrt (norm_nonneg w)).2 h2, Real.sqrt_le_iff.2 ⟨norm_nonneg w, h1⟩⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(Real.sqrt_le_iff.1 h2).2, (Real.lt_sqrt (norm_nonneg w)).1 h1⟩
    rw [hset, measure_sdiff (Metric.ball_subset_ball (Real.sqrt_le_sqrt hsa.le))
      measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne, Complex.volume_ball,
      Complex.volume_ball, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (ha.trans hsa.le), Real.sq_sqrt ha,
      ← ENNReal.sub_mul (fun _ _ ↦ ENNReal.coe_ne_top), ENNReal.ofReal_sub _ ha]

theorem volume_capSet {m : ℕ} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    volume {v : Fin (m + 1) → ℂ | c * sqNorm v ≤ ‖v 0‖ ^ 2 ∧ sqNorm v < 1} =
      (∫⁻ y : Fin m → ℂ, ENNReal.ofReal (1 - sqNorm y / (1 - c))) * NNReal.pi := by
  have h1c : 0 < 1 - c := by linarith
  have he := volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℂ) 0
  set A : Set (ℂ × (Fin m → ℂ)) :=
    {p | c * (‖p.1‖ ^ 2 + sqNorm p.2) ≤ ‖p.1‖ ^ 2 ∧ ‖p.1‖ ^ 2 + sqNorm p.2 < 1} with hA_def
  have hA : MeasurableSet A := by
    have h1 : Continuous fun p : ℂ × (Fin m → ℂ) ↦ ‖p.1‖ ^ 2 + sqNorm p.2 :=
      ((continuous_norm.comp continuous_fst).pow 2).add ((continuous_sqNorm m).comp continuous_snd)
    exact (measurableSet_le (continuous_const.mul h1).measurable
      ((continuous_norm.comp continuous_fst).pow 2).measurable).inter
      (measurableSet_lt h1.measurable measurable_const)
  have hpre : {v : Fin (m + 1) → ℂ | c * sqNorm v ≤ ‖v 0‖ ^ 2 ∧ sqNorm v < 1} =
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℂ) 0 ⁻¹' A := by
    ext v
    simp only [mem_ofPred_eq, mem_preimage, piFinSuccAbove_zero_apply, hA_def, sqNorm_succ]
  rw [hpre, he.measure_preimage hA.nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_apply_symm hA, ← lintegral_mul_const' _ _ ENNReal.coe_ne_top]
  congr 1
  funext y
  have hfib : (fun x : ℂ ↦ (x, y)) ⁻¹' A =
      {w : ℂ | c * sqNorm y / (1 - c) ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 < 1 - sqNorm y} := by
    ext w
    simp only [mem_preimage, hA_def, mem_ofPred_eq, div_le_iff₀ h1c]
    constructor
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith
  rw [hfib, volume_annulus (div_nonneg (mul_nonneg hc0 (sqNorm_nonneg y)) h1c.le)]
  congr 2
  field_simp
  ring

theorem lintegral_scale {m : ℕ} {c : ℝ} (hc1 : c < 1) :
    ∫⁻ y : Fin m → ℂ, ENNReal.ofReal (1 - sqNorm y / (1 - c)) =
      ENNReal.ofReal ((1 - c) ^ m) * ∫⁻ y : Fin m → ℂ, ENNReal.ofReal (1 - sqNorm y) := by
  have h1c : 0 < 1 - c := by linarith
  have hr0 : √(1 - c) ≠ 0 := (Real.sqrt_pos.2 h1c).ne'
  set f : (Fin m → ℂ) → ENNReal := fun y ↦ ENNReal.ofReal (1 - sqNorm y / (1 - c)) with hf
  have hfm : Measurable f :=
    ENNReal.measurable_ofReal.comp (measurable_const.sub ((measurable_sqNorm m).div_const _))
  have hfr : ∀ y, f (√(1 - c) • y) = ENNReal.ofReal (1 - sqNorm y) := by
    intro y
    simp only [hf, sqNorm_smul, Real.sq_sqrt h1c.le]
    congr 2
    field_simp
  have key : ∫⁻ y : Fin m → ℂ, ENNReal.ofReal (1 - sqNorm y) =
      ENNReal.ofReal (((1 - c) ^ m)⁻¹) * ∫⁻ y, f y := by
    simp_rw [← hfr]
    have hmap' : ∫⁻ y, f (√(1 - c) • y) =
        ∫⁻ y, f y ∂(Measure.map (fun y : Fin m → ℂ ↦ √(1 - c) • y) volume) :=
      (lintegral_map hfm (by fun_prop)).symm
    rw [hmap', Measure.map_addHaar_smul (volume : Measure (Fin m → ℂ)) hr0, lintegral_smul_measure,
      finrank_fun_complex, pow_mul, Real.sq_sqrt h1c.le, abs_of_pos (inv_pos.2 (pow_pos h1c m))]
    rfl
  rw [key, ← mul_assoc, ← ENNReal.ofReal_mul (pow_pos h1c m).le,
    mul_inv_cancel₀ (pow_pos h1c m).ne', ENNReal.ofReal_one, one_mul]

theorem volume_capSet_eq {m : ℕ} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    volume {v : Fin (m + 1) → ℂ | c * sqNorm v ≤ ‖v 0‖ ^ 2 ∧ sqNorm v < 1} =
      ENNReal.ofReal ((1 - c) ^ m) * volume (ballSet (m + 1) 1) := by
  have h0 := volume_capSet (m := m) le_rfl zero_lt_one
  have hb : {v : Fin (m + 1) → ℂ | 0 * sqNorm v ≤ ‖v 0‖ ^ 2 ∧ sqNorm v < 1} =
      ballSet (m + 1) 1 := by
    ext v
    simp [ballSet]
  rw [hb] at h0
  simp only [sub_zero, div_one] at h0
  rw [volume_capSet hc0 hc1, lintegral_scale hc1, mul_assoc, ← h0]

theorem density_Ici (k : ℕ) (c : ℝ) :
    (volume.withDensity fun x : ℝ ↦ ENNReal.ofReal
        (Set.indicator (Set.Icc 0 1) (fun x ↦ (k + 1 : ℝ) * (1 - x) ^ k) x)) (Ici c) =
      ENNReal.ofReal ((1 - min (max c 0) 1) ^ (k + 1)) := by
  rw [withDensity_apply _ measurableSet_Ici]
  have hind : ∀ x : ℝ, ENNReal.ofReal (Set.indicator (Set.Icc 0 1)
      (fun x ↦ (k + 1 : ℝ) * (1 - x) ^ k) x) =
      Set.indicator (Set.Icc 0 1) (fun x ↦ ENNReal.ofReal ((k + 1 : ℝ) * (1 - x) ^ k)) x := by
    intro x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1 <;> simp [hx]
  simp_rw [hind]
  rw [setLIntegral_indicator measurableSet_Icc]
  have hI : Icc (0 : ℝ) 1 ∩ Ici c = Icc (max c 0) 1 := by
    ext x
    simp only [mem_inter_iff, mem_Ici, mem_Icc, max_le_iff]
    tauto
  rw [hI]
  rcases le_or_gt (max c 0) 1 with hd | hd
  · rw [min_eq_left hd, ← ofReal_integral_eq_lintegral_ofReal]
    · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hd,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_left (fun x ↦ x ^ k) (1 : ℝ), integral_pow]
      congr 1
      field_simp
      simp
    · exact (by fun_prop : Continuous fun x : ℝ ↦ (k + 1 : ℝ) * (1 - x) ^ k).integrableOn_Icc
    · refine ae_restrict_of_forall_mem measurableSet_Icc fun x hx ↦ ?_
      exact mul_nonneg (by positivity) (pow_nonneg (by linarith [hx.2]) k)
  · rw [Icc_eq_empty (not_le.2 hd), Measure.restrict_empty, lintegral_zero_measure,
      min_eq_right hd.le]
    simp

theorem law_Ici (k : ℕ) (c : ℝ) :
    ((sphereLaw (k + 1 + 1)).map (fun z ↦ ‖z 0‖ ^ 2)) (Ici c) =
      ENNReal.ofReal ((1 - min (max c 0) 1) ^ (k + 1)) := by
  have hGm : Measurable fun (u : Fin 1 × Fin (k + 1 + 1) → ℂ) (j : Fin (k + 1 + 1)) ↦
      sphereNormalize (HermNorm.std (k + 1 + 1)) 1 u (0, j) := by
    unfold sphereNormalize
    simp only [HermNorm.std_norm_eq]
    fun_prop
  have hFm : Measurable fun z : Fin (k + 1 + 1) → ℂ ↦ ‖z 0‖ ^ 2 := by fun_prop
  have hBm : MeasurableSet (sphereBall (HermNorm.std (k + 1 + 1)) 1) :=
    (isOpen_sphereBall_std _).measurableSet
  rw [Measure.map_apply hFm measurableSet_Ici, sphereLaw,
    Measure.map_apply hGm (hFm measurableSet_Ici), cond_apply hBm]

  set eq := Equiv.uniqueProd (Fin (k + 1 + 1)) (Fin 1)
  set P := MeasurableEquiv.piCongrLeft (fun _ : Fin (k + 1 + 1) ↦ ℂ) eq
  have hP : MeasurePreserving P volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin (k + 1 + 1) ↦ ℂ) eq
  have hPapp : ∀ u j, P u j = u (0, j) := by
    intro u j
    have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin (k + 1 + 1) ↦ ℂ) eq u (0, j)
    simpa [eq] using this
  have hPu : ∀ u : Fin 1 × Fin (k + 1 + 1) → ℂ, (fun j ↦ u (0, j)) = P u :=
    fun u ↦ funext fun j ↦ (hPapp u j).symm
  have hB : sphereBall (HermNorm.std (k + 1 + 1)) 1 = P ⁻¹' ballSet (k + 1 + 1) 1 := by
    ext u
    simp only [sphereBall, mem_ofPred_eq, mem_preimage, ballSet, std_norm_eq, Fin.forall_fin_one,
      hPu, Real.sqrt_lt' one_pos, one_pow]
  set T : Set (Fin (k + 1 + 1) → ℂ) :=
    {v | sqNorm v < 1 ∧ c ≤ ‖((√(sqNorm v) : ℝ) : ℂ)⁻¹ * v 0‖ ^ 2} with hT_def
  have hT : sphereBall (HermNorm.std (k + 1 + 1)) 1 ∩
      ((fun (u : Fin 1 × Fin (k + 1 + 1) → ℂ) (j : Fin (k + 1 + 1)) ↦
        sphereNormalize (HermNorm.std (k + 1 + 1)) 1 u (0, j)) ⁻¹'
        ((fun z : Fin (k + 1 + 1) → ℂ ↦ ‖z 0‖ ^ 2) ⁻¹' Ici c)) = P ⁻¹' T := by
    rw [hB]
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Ici, sphereNormalize, std_norm_eq, hPu, hT_def,
      mem_ofPred_eq, ballSet, hPapp]
  rw [hT, hB, hP.measure_preimage_equiv, hP.measure_preimage_equiv]
  have hV0 := (volume_ballSet_one_pos (k + 1 + 1)).ne'
  have hVt := volume_ballSet_one_ne_top (k + 1 + 1)
  have hnorm : ∀ v : Fin (k + 1 + 1) → ℂ,
      ‖((√(sqNorm v) : ℝ) : ℂ)⁻¹ * v 0‖ ^ 2 = ‖v 0‖ ^ 2 / sqNorm v := by
    intro v
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      inv_pow, Real.sq_sqrt (sqNorm_nonneg v)]
    ring

  have hTpos : 0 < c → T = {v | c * sqNorm v ≤ ‖v 0‖ ^ 2 ∧ sqNorm v < 1} \ {0} := by
    intro hc
    ext v
    simp only [hT_def, mem_ofPred_eq, mem_sdiff, mem_singleton_iff, hnorm]
    by_cases hv : v = 0
    · subst hv
      simp [sqNorm]
      exact hc
    · have hs := sqNorm_pos_of_ne_zero hv
      rw [le_div_iff₀ hs]
      tauto
  rcases le_or_gt c 0 with hc | hc
  · have hTB : T = ballSet (k + 1 + 1) 1 := by
      ext v
      simp only [hT_def, mem_ofPred_eq, ballSet, and_iff_left_iff_imp]
      intro _
      exact hc.trans (by positivity)
    rw [hTB, ENNReal.inv_mul_cancel hV0 hVt, max_eq_right hc, min_eq_left zero_le_one]
    simp
  rcases lt_or_ge c 1 with hc1 | hc1
  · rw [hTpos hc, measure_sdiff_null (volume_singleton_zero _), volume_capSet_eq hc.le hc1,
      ← mul_assoc, mul_comm _ (ENNReal.ofReal _), mul_assoc, ENNReal.inv_mul_cancel hV0 hVt,
      mul_one, max_eq_left hc.le, min_eq_left hc1.le]
  ·
    have he := volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1 + 1) ↦ ℂ) 0
    have hsub : T ⊆ MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1 + 1) ↦ ℂ) 0 ⁻¹'
        (univ ×ˢ {0}) := by
      rw [hTpos hc]
      rintro v ⟨⟨h1, _⟩, hv⟩
      simp only [mem_preimage, piFinSuccAbove_zero_apply, mem_prod, mem_univ, true_and,
        mem_singleton_iff]
      by_contra htl
      have := sqNorm_pos_of_ne_zero htl
      rw [sqNorm_succ] at h1
      nlinarith [sqNorm_nonneg (Fin.tail v), norm_nonneg (v 0)]
    have h0 : volume T = 0 := by
      refine measure_mono_null hsub ?_
      rw [he.measure_preimage (MeasurableSet.univ.prod (measurableSet_singleton _)).nullMeasurableSet,
        Measure.volume_eq_prod, Measure.prod_prod, volume_singleton_zero, mul_zero]
    rw [h0, mul_zero, max_eq_left hc.le, min_eq_right hc1, sub_self, zero_pow (Nat.succ_ne_zero _),
      ENNReal.ofReal_zero]

end SphereLawFirstCoord

theorem SphereLawFirstCoord.proof : SphereLawFirstCoord.Statement := by
  intro N hN
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 + 1 := ⟨N - 2, by omega⟩
  show (sphereLaw (k + 1 + 1)).map (fun z ↦ ‖z 0‖ ^ 2) = _
  have hd : (fun x : ℝ ↦ ENNReal.ofReal (Set.indicator (Set.Icc 0 1)
      (fun x ↦ ((k + 1 + 1 : ℕ) - 1 : ℝ) * (1 - x) ^ (k + 1 + 1 - 2)) x)) =
      fun x ↦ ENNReal.ofReal (Set.indicator (Set.Icc 0 1) (fun x ↦ (k + 1 : ℝ) * (1 - x) ^ k) x) := by
    have h2 : k + 1 + 1 - 2 = k := by omega
    simp only [h2]
    push_cast
    ring_nf
  rw [hd]
  have := (sphereLaw (k + 1 + 1)).isFiniteMeasure_map fun z : Fin (k + 1 + 1) → ℂ ↦ ‖z 0‖ ^ 2
  refine Measure.ext_of_Ici _ _ fun c ↦ ?_
  rw [SphereLawFirstCoord.law_Ici, SphereLawFirstCoord.density_Ici]

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem SphereLawBasic.full : SphereLawBasic.Statement := SphereLawBasic.proof

theorem SphereLawFirstCoord.full : SphereLawFirstCoord.Statement := SphereLawFirstCoord.proof

theorem FibreMahlerForms.full : FibreMahlerForms.Statement := FibreMahlerForms.proof

theorem SpherePhase.full : SpherePhase.Statement :=
  SpherePhase.full_of_sphereLawBasic SphereLawBasic.full

theorem SphereProjectionLaw.full : SphereProjectionLaw.Statement :=
  SphereProjectionLaw.full_of SphereLawBasic.full SphereLawFirstCoord.full

theorem PointwiseLelong.full : PointwiseLelong.Statement :=
  PointwiseLelong.full_of SphereLawBasic.full SphereLawFirstCoord.full

theorem HeightOfCycle.full : HeightOfCycle.Statement :=
  HeightOfCycle.full_of_fibreMahlerForms FibreMahlerForms.full

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField TensorProduct IsDedekindDomain Submodule
open GroundTheory.Heights₂.Heights

noncomputable section

namespace LocalGlobalIndex

variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_approx_finset (T : Finset (HeightOneSpectrum (𝓞 K))) (N : 𝓞 K) (hN : N ≠ 0)
    (r : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K)
    (hr : ∀ v ∈ T, r v ∈ v.adicCompletionIntegers K) :
    ∃ a : 𝓞 K, ∀ v ∈ T, ∃ o ∈ v.adicCompletionIntegers K,
      algebraMap K (v.adicCompletion K) (a : K) - r v =
        algebraMap K (v.adicCompletion K) (N : K) * o := by
  classical
  have h : ∀ v ∈ T, ∃ c : 𝓞 K, (∃ o ∈ v.adicCompletionIntegers K,
        algebraMap K (v.adicCompletion K) (c : K) - r v =
          algebraMap K (v.adicCompletion K) (N : K) * o) ∧
      ∀ u ∈ T, u ≠ v → ∃ o ∈ u.adicCompletionIntegers K,
        algebraMap K (u.adicCompletion K) (c : K) = algebraMap K (u.adicCompletion K) (N : K) * o :=
    fun v hv => Theta.Ex1GL.exists_approx v T N hN (hr v hv)
  choose! c hc hc' using h
  refine ⟨∑ w ∈ T, c w, fun v hv => ?_⟩
  obtain ⟨o, ho, hov⟩ := hc v hv
  have hw : ∀ w ∈ T.erase v, ∃ o ∈ v.adicCompletionIntegers K,
      algebraMap K (v.adicCompletion K) (c w : K) = algebraMap K (v.adicCompletion K) (N : K) * o :=
    fun w hw => hc' w (Finset.mem_of_mem_erase hw) v hv (Finset.ne_of_mem_erase hw).symm
  choose! o' ho' hov' using hw
  refine ⟨o + ∑ w ∈ T.erase v, o' w, add_mem ho (sum_mem fun w hw => ho' w hw), ?_⟩
  have e : ((∑ w ∈ T, c w : 𝓞 K) : K) = (c v : K) + ∑ w ∈ T.erase v, (c w : K) := by
    rw [← Finset.add_sum_erase T c hv]
    push_cast
    rfl
  rw [e, map_add, map_sum, Finset.sum_congr rfl hov', ← Finset.mul_sum, mul_add, ← hov]
  ring

theorem exists_mem_near (L : Submodule (𝓞 K) V) (hL : L.FG) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (N : 𝓞 K) (hN : N ≠ 0) (y : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K ⊗[K] V)
    (hy : ∀ v ∈ T, y v ∈ localLattice v L) :
    ∃ x ∈ L, ∀ v ∈ T, ∃ w ∈ localLattice v L,
      toLocal v x - y v = algebraMap K (v.adicCompletion K) (N : K) • w := by
  classical
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hL
  have hLv : ∀ v : HeightOneSpectrum (𝓞 K), localLattice v L =
      span (v.adicCompletionIntegers K) (Set.range fun i => toLocal v (g i)) := fun v => by
    rw [← hg, LatticeOfLocalisations.localLattice_span, ← Set.range_comp]
    rfl
  have hc : ∀ v ∈ T, ∃ cc : Fin n → v.adicCompletionIntegers K,
      ∑ i, cc i • toLocal v (g i) = y v := by
    intro v hv
    have h := hy v hv
    rw [hLv v] at h
    exact (mem_span_range_iff_exists_fun _).mp h
  choose! cc hcc using hc
  have ha : ∀ i, ∃ a : 𝓞 K, ∀ v ∈ T, ∃ o ∈ v.adicCompletionIntegers K,
      algebraMap K (v.adicCompletion K) (a : K) - (cc v i : v.adicCompletion K) =
        algebraMap K (v.adicCompletion K) (N : K) * o :=
    fun i => exists_approx_finset T N hN (fun v => (cc v i : v.adicCompletion K))
      fun v _ => (cc v i).2
  choose a hav using ha
  refine ⟨∑ i, a i • g i, sum_mem fun i _ => L.smul_mem _ (hg ▸ subset_span ⟨i, rfl⟩),
    fun v hv => ?_⟩
  choose o ho hov using fun i => hav i v hv
  refine ⟨∑ i, (⟨o i, ho i⟩ : v.adicCompletionIntegers K) • toLocal v (g i), ?_, ?_⟩
  · rw [hLv v]
    exact sum_mem fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩)
  · rw [← hcc v hv, map_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LatticeOfLocalisations.toLocal_smul', ← algebraMap_smul (v.adicCompletion K) (cc v i),
      ← algebraMap_smul (v.adicCompletion K) (⟨o i, ho i⟩ : v.adicCompletionIntegers K),
      smul_smul]
    convert congrArg (· • toLocal v (g i)) (hov i) using 1
    · exact (sub_smul (algebraMap K (v.adicCompletion K) (a i : K)) (cc v i : v.adicCompletion K)
        (toLocal v (g i))).symm
    · rfl

theorem mem_of_forall_toLocal_mem (M : FullLattice K V) {x : V}
    (hx : ∀ v, toLocal v x ∈ localLattice v M.carrier) : x ∈ M.carrier := by
  classical
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp M.fg
  have hgK : span K (Set.range g) = ⊤ := by
    rw [eq_top_iff, ← M.span_eq, span_le, ← hg]
    exact fun x hx => span_le_restrictScalars (𝓞 K) K (Set.range g) hx
  have : Module.Finite K V :=
    ⟨⟨Finset.univ.image g, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, hgK]⟩⟩
  let e := Module.finBasis K V
  obtain ⟨c, hc, hcF⟩ := LatticeOfLocalisations.exists_smul_mem_span_basis e g
  let F₀ : FullLattice K V := ⟨span (𝓞 K) (Set.range e), fg_span (Set.finite_range e),
    by rw [Submodule.span_span_of_tower, e.span_eq]⟩
  obtain ⟨d, hd, hdF⟩ := exists_smulSub_le M F₀
  set b := d * c with hb_def
  have hb : b ≠ 0 := mul_ne_zero hd hc
  have hbK : (b : K) ≠ 0 := by exact_mod_cast hb
  set T := (finite_mem_asIdeal hb).toFinset with hT
  obtain ⟨x₁, hx₁, hnear⟩ :=
    exists_mem_near M.carrier M.fg T b hb (fun v => toLocal v x) fun v _ => hx v
  set z : V := (b : K)⁻¹ • (x - x₁) with hz
  have hzv : ∀ v, toLocal v z ∈ localLattice v M.carrier := by
    intro v
    have hz' : toLocal v z =
        (algebraMap K (v.adicCompletion K) (b : K))⁻¹ • (toLocal v x - toLocal v x₁) := by
      rw [hz, map_smul, map_sub, ← algebraMap_smul (v.adicCompletion K) (b : K)⁻¹, map_inv₀]
    by_cases hv : v ∈ T
    · obtain ⟨w, hw, hxw⟩ := hnear v hv
      rw [hz', ← neg_sub, hxw, smul_neg, smul_smul, inv_mul_cancel₀ ((map_ne_zero _).mpr hbK),
        one_smul]
      exact neg_mem hw
    · have hbv : b ∉ v.asIdeal := by simpa [hT] using hv
      rw [hz']
      exact LatticeOfLocalisations.smul_mem_of_mem_integers v _
        (Theta.Ex1GL.inv_mem_of_notMem v hbv) (sub_mem (hx v) (subset_span ⟨x₁, hx₁, rfl⟩))
  have hcz : c • z ∈ span (𝓞 K) (Set.range e) := by
    refine LatticeOfLocalisations.mem_span_of_forall_toLocal_mem e fun v => ?_
    rw [LatticeOfLocalisations.toLocal_smul']
    exact LatticeOfLocalisations.smul_localLattice_mem v c
      (fun m hm => hcF m (by rw [hg]; exact hm)) (hzv v)
  have hbz : b • z ∈ M.carrier := by
    rw [hb_def, mul_smul]
    exact hdF (mem_smulSub_of_mem d hcz)
  have hxz : b • z = x - x₁ := by
    rw [← algebraMap_smul K b z, hz, smul_smul, ← RingOfIntegers.coe_eq_algebraMap,
      mul_inv_cancel₀ hbK, one_smul]
  have h := add_mem hbz hx₁
  rwa [hxz, sub_add_cancel] at h

end LocalGlobalIndex

open LocalGlobalIndex in

theorem LocalGlobalIndex.proof : LocalGlobalIndex.Statement := by
  intro K _ _ V _ _ _ _ M₁ M₂ h21
  classical
  obtain ⟨b, hb, hbM⟩ := exists_smulSub_le M₂ M₁
  have hbM' : ∀ m ∈ M₁.carrier, b • m ∈ M₂.carrier := fun m hm => hbM (mem_smulSub_of_mem b hm)
  have hbK : (b : K) ≠ 0 := by exact_mod_cast hb
  set S := (finite_mem_asIdeal hb).toFinset with hS
  have hout : ∀ v, v ∉ S → localLattice v M₁.carrier ≤ localLattice v M₂.carrier := by
    intro v hv y hy
    have hbv : b ∉ v.asIdeal := by simpa [hS] using hv
    have e : y = (algebraMap K (v.adicCompletion K) (b : K))⁻¹ •
        (algebraMap K (v.adicCompletion K) (b : K) • y) := by
      rw [smul_smul, inv_mul_cancel₀ ((map_ne_zero _).mpr hbK), one_smul]
    rw [e]
    exact LatticeOfLocalisations.smul_mem_of_mem_integers v _
      (Theta.Ex1GL.inv_mem_of_notMem v hbv) (LatticeOfLocalisations.smul_localLattice_mem v b hbM' hy)
  let A := fun v : HeightOneSpectrum (𝓞 K) => (localLattice v M₁.carrier).toAddSubgroup
  let B := fun v : HeightOneSpectrum (𝓞 K) => (localLattice v M₂.carrier).toAddSubgroup
  let ι : ∀ v, M₁.carrier →+ A v := fun v =>
    { toFun := fun m => ⟨toLocal v (m : V), subset_span ⟨m, m.2, rfl⟩⟩
      map_zero' := by ext; simp
      map_add' := fun m m' => by ext; simp }
  let Φ : M₁.carrier →+ ∀ v : S, A v.1 ⧸ (B v.1).addSubgroupOf (A v.1) :=
    AddMonoidHom.pi fun v => (QuotientAddGroup.mk' _).comp (ι v.1)
  have hΦ : ∀ (m : M₁.carrier) (v : S), Φ m v = 0 ↔ toLocal v.1 (m : V) ∈ localLattice v.1 M₂.carrier := by
    intro m v
    show QuotientAddGroup.mk' _ (ι v.1 m) = 0 ↔ _
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    rfl
  have hker : Φ.ker = (M₂.carrier.comap M₁.carrier.subtype).toAddSubgroup := by
    ext m
    rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, Submodule.mem_comap,
      Submodule.coe_subtype]
    constructor
    · intro h
      refine mem_of_forall_toLocal_mem M₂ fun v => ?_
      by_cases hv : v ∈ S
      · exact (hΦ m ⟨v, hv⟩).mp (congrFun h ⟨v, hv⟩)
      · exact hout v hv (subset_span ⟨m, m.2, rfl⟩)
    · intro h
      funext v
      exact (hΦ m v).mpr (subset_span ⟨m, h, rfl⟩)
  have hsurj : Function.Surjective Φ := by
    intro q
    choose y hy using fun v : S => QuotientAddGroup.mk'_surjective _ (q v)
    obtain ⟨x, hx, hnear⟩ := exists_mem_near M₁.carrier M₁.fg S b hb
      (fun v => if h : v ∈ S then ((y ⟨v, h⟩ : A v) : v.adicCompletion K ⊗[K] V) else 0)
      (fun v hv => by simp only [dif_pos hv]; exact (y ⟨v, hv⟩).2)
    refine ⟨⟨x, hx⟩, funext fun v => ?_⟩
    rw [← hy v]
    show QuotientAddGroup.mk' _ (ι v.1 ⟨x, hx⟩) = _
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq,
      AddSubgroup.mem_addSubgroupOf]
    obtain ⟨w, hw, hxw⟩ := hnear v.1 v.2
    rw [dif_pos v.2] at hxw
    have e : ((-(ι v.1 ⟨x, hx⟩) + y v : A v.1) : v.1.adicCompletion K ⊗[K] V) =
        -(algebraMap K (v.1.adicCompletion K) (b : K) • w) := by
      rw [← hxw]
      push_cast
      show -(toLocal v.1 x) + _ = _
      abel
    show _ ∈ localLattice v.1 M₂.carrier
    rw [e]
    exact neg_mem (LatticeOfLocalisations.smul_localLattice_mem v.1 b hbM' hw)
  have hcard : Nat.card (M₁.carrier ⧸ M₂.carrier.comap M₁.carrier.subtype) =
      ∏ v : S, Nat.card (A v.1 ⧸ (B v.1).addSubgroupOf (A v.1)) := by
    rw [← Nat.card_pi]
    exact Nat.card_congr ((QuotientAddGroup.quotientAddEquivOfEq hker.symm).toEquiv.trans
      (QuotientAddGroup.quotientKerEquivOfSurjective Φ hsurj).toEquiv)
  rw [hcard, Nat.cast_prod, finprod_eq_prod_of_mulSupport_subset (s := S), ← Finset.prod_coe_sort S]
  · rfl
  · intro v hv
    by_contra hvS
    apply hv
    have h1 : (localLattice v M₂.carrier).toAddSubgroup.relIndex
        (localLattice v M₁.carrier).toAddSubgroup = 1 :=
      AddSubgroup.relIndex_eq_one.mpr fun y hy => hout v hvS hy
    simp only [h1, Nat.cast_one]

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField IsDedekindDomain TensorProduct
open GroundTheory.Heights₂.Heights

universe u v

theorem LocalIndex.proof (h₁ : LocalGlobalIndex.Statement.{u, v})
    (h₂ : LocalLatticeIndex.Statement.{u, v}) : LocalIndex.Statement.{u, v} := by
  intro K _ _ V _ _ _ _ M₁ M₂ g hle hloc
  rw [h₁ K V M₁ M₂ hle]
  refine finprod_congr fun w ↦ ?_
  exact h₂ K V w _ _ (g w) (localLattice_isLocalLattice w M₁) (hloc w)
    (Submodule.span_mono (Set.image_mono hle))

end GroundTheory.Heights₂.Heights.LatticeLemmas
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

universe u v

theorem LocalGlobalIndex.full : LocalGlobalIndex.Statement.{u, v} := LocalGlobalIndex.proof

theorem LocalLatticeIndex.full : LocalLatticeIndex.Statement.{u, v} := LocalLatticeIndex.proof

theorem LocalIndex.full : LocalIndex.Statement.{u, v} :=
  LocalIndex.proof LocalGlobalIndex.full LocalLatticeIndex.full

theorem LocalChange.full : LocalChange.Statement.{u, v} :=
  LocalChange.full_of_localIndex LocalIndex.full

end GroundTheory.Heights₂.Heights.LatticeLemmas
end
