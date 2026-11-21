import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.UnitPreserving

section
open NumberField NumberField.mixedEmbedding MeasureTheory
open scoped ENNReal Pointwise Classical

noncomputable section

namespace PI.Residue

theorem latticeCount_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (B : Set E) (hB : MeasurableSet B) :
    μ B ≤ (∑' x : L, (B - B).indicator (fun _ => (1 : ℝ≥0∞)) (x : E)) *
      ENNReal.ofReal (ZLattice.covolume L μ) := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  have hF := ZLattice.isAddFundamentalDomain b μ
  set F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ) with hFdef
  have hfin : μ F ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have hcov : ENNReal.ofReal (ZLattice.covolume L μ) = μ F := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L μ hF, measureReal_def,
      ENNReal.ofReal_toReal hfin]
  haveI : VAddInvariantMeasure L E μ :=
    ⟨fun c s _ => measure_preimage_add μ (c : E) s⟩
  have hm : ∀ g : L, MeasurableSet (g +ᵥ B) := fun g => hB.const_vadd g
  have h2 : ∀ g : L, μ ((g +ᵥ B) ∩ F) =
      ∫⁻ t in F, (g +ᵥ B).indicator (fun _ => (1 : ℝ≥0∞)) t ∂μ := by
    intro g
    rw [lintegral_indicator_const (hm g), one_mul, Measure.restrict_apply (hm g)]
  have hpt : ∀ t : E, ∑' g : L, (g +ᵥ B).indicator (fun _ => (1 : ℝ≥0∞)) t ≤
      ∑' x : L, (B - B).indicator (fun _ => (1 : ℝ≥0∞)) (x : E) := by
    intro t
    by_cases h : ∃ g0 : L, t ∈ g0 +ᵥ B
    · obtain ⟨g0, hg0⟩ := h
      rw [← (Equiv.addRight g0).tsum_eq]
      refine ENNReal.tsum_le_tsum fun g => ?_
      by_cases hg : t ∈ ((Equiv.addRight g0) g) +ᵥ B
      · have : (g : E) ∈ B - B := by
          obtain ⟨b0, hb0, e0⟩ := hg0
          obtain ⟨b1, hb1, e1⟩ := hg
          refine ⟨b0, hb0, b1, hb1, ?_⟩
          have e0' : (g0 : E) + b0 = t := e0
          have e1' : ((g : E) + (g0 : E)) + b1 = t := e1
          have : (g0 : E) + b0 = ((g : E) + (g0 : E)) + b1 := e0'.trans e1'.symm
          rw [sub_eq_iff_eq_add]
          apply add_left_cancel (a := (g0 : E))
          rw [this]; abel
        rw [Set.indicator_of_mem hg, Set.indicator_of_mem this]
      · rw [Set.indicator_of_notMem hg]; exact zero_le
    · push Not at h
      have : ∀ g : L, (g +ᵥ B).indicator (fun _ => (1 : ℝ≥0∞)) t = 0 :=
        fun g => Set.indicator_of_notMem (h g) _
      simp [this]
  calc μ B = ∑' g : L, μ ((g +ᵥ B) ∩ F) := hF.measure_eq_tsum B
    _ = ∫⁻ t in F, ∑' g : L, (g +ᵥ B).indicator (fun _ => (1 : ℝ≥0∞)) t ∂μ := by
        rw [lintegral_tsum fun g => (measurable_const.indicator (hm g)).aemeasurable]
        exact tsum_congr h2
    _ ≤ ∫⁻ _ in F, ∑' x : L, (B - B).indicator (fun _ => (1 : ℝ≥0∞)) (x : E) ∂μ :=
        lintegral_mono hpt
    _ = _ := by rw [setLIntegral_const, hcov]

theorem latticeCount : LatticeCount := fun _ _ _ L _ _ B hB => latticeCount_gen volume L B hB

end PI.Residue
end
end

section
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped nonZeroDivisors ENNReal Classical Pointwise

noncomputable section

namespace PI.Residue

variable (K : Type) [Field K] [NumberField K]

theorem measurableSet_box (r : InfinitePlace K → ℝ) : MeasurableSet (box K r) := by
  have : box K r = ⋂ w, {y | normAtPlace w y < r w} := by
    ext y; simp [box]
  rw [this]
  exact MeasurableSet.iInter fun w =>
    measurableSet_lt (continuous_normAtPlace w).measurable measurable_const

theorem measurableSet_hit (ρ : ℝ) (x : mixedSpace K) : MeasurableSet (hit K ρ x) := by
  have : hit K ρ x = ⋂ w, {y | normAtPlace w y * normAtPlace w x < ρ} := by
    ext y; simp [hit]
  rw [this]
  exact MeasurableSet.iInter fun w =>
    measurableSet_lt ((continuous_normAtPlace w).measurable.mul_const _) measurable_const

theorem measurableSet_shell : MeasurableSet (shell K) := by
  have : shell K = fundamentalCone K ∩
      ({y | 1 / 2 < mixedEmbedding.norm y} ∩ {y | mixedEmbedding.norm y ≤ 1}) := by
    ext y
    simp only [shell, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [this]
  exact (measurableSet_fundamentalCone K).inter
    ((measurableSet_lt measurable_const (mixedEmbedding.continuous_norm K).measurable).inter
      (measurableSet_le (mixedEmbedding.continuous_norm K).measurable measurable_const))

variable {K}

theorem normAtPlace_pos_of_norm_pos {y : mixedSpace K} (hy : 0 < mixedEmbedding.norm y)
    (w : InfinitePlace K) : 0 < normAtPlace w y := by
  refine lt_of_le_of_ne (normAtPlace_nonneg w y) fun h => ?_
  exact hy.ne' (mixedEmbedding.norm_eq_zero_iff.mpr ⟨w, h.symm⟩)

theorem prod_radius (ρ : ℝ) (y : mixedSpace K) :
    ∏ w : InfinitePlace K, (ρ / (2 * normAtPlace w y)) ^ mult w
      = (ρ / 2) ^ Module.finrank ℚ K / mixedEmbedding.norm y := by
  rw [mixedEmbedding.norm_apply, ← sum_mult_eq, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← div_pow, div_div]

theorem mem_hit_of_mem_sub {ρ : ℝ} {y x : mixedSpace K} (hy : 0 < mixedEmbedding.norm y)
    (hx : x ∈ box K (fun w => ρ / (2 * normAtPlace w y)) -
      box K (fun w => ρ / (2 * normAtPlace w y))) : y ∈ hit K ρ x := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_sub.mp hx
  intro w
  have hw := normAtPlace_pos_of_norm_pos hy w
  have h1 : normAtPlace w (a - b) ≤ normAtPlace w a + normAtPlace w b := by
    rw [sub_eq_add_neg]
    refine (normAtPlace_add_le w a (-b)).trans ?_
    rw [normAtPlace_neg]
  have ha' : normAtPlace w a < ρ / (2 * normAtPlace w y) := ha w
  have hb' : normAtPlace w b < ρ / (2 * normAtPlace w y) := hb w
  have h2 : normAtPlace w (a - b) < ρ / normAtPlace w y := by
    have : ρ / (2 * normAtPlace w y) + ρ / (2 * normAtPlace w y) = ρ / normAtPlace w y := by
      field_simp
      ring
    linarith
  rw [lt_div_iff₀ hw] at h2
  rw [mul_comm]
  exact h2

theorem count_pointwise (hB : BoxVolume) (J : (Ideal (𝓞 K))⁰) {ρ : ℝ} (hρ : 0 < ρ)
    {y : mixedSpace K} (hy : y ∈ shell K) :
    vfac K * ENNReal.ofReal ((ρ / 2) ^ Module.finrank ℚ K) ≤
      (∑' x : lat K J, (hit K ρ (x : mixedSpace K)).indicator (fun _ => (1 : ℝ≥0∞)) y) *
        ENNReal.ofReal (ZLattice.covolume (lat K J)) := by
  have hy0 : 0 < mixedEmbedding.norm y := lt_trans (by norm_num) hy.2.1
  set r : InfinitePlace K → ℝ := fun w => ρ / (2 * normAtPlace w y) with hr
  have hrpos : ∀ w, 0 < r w := fun w =>
    div_pos hρ (mul_pos two_pos (normAtPlace_pos_of_norm_pos hy0 w))
  have hvol := hB K r hrpos
  rw [hr, prod_radius] at hvol
  have hcount := latticeCount K (lat K J) (box K r) (measurableSet_box K r)
  have h1 : vfac K * ENNReal.ofReal ((ρ / 2) ^ Module.finrank ℚ K) ≤ volume (box K r) := by
    rw [hr, hvol]
    gcongr
    rw [le_div_iff₀ hy0]
    have hp : 0 ≤ (ρ / 2) ^ Module.finrank ℚ K := by positivity
    nlinarith [hy.2.2]
  refine h1.trans (hcount.trans ?_)
  gcongr with x
  by_cases hx : (x : mixedSpace K) ∈ box K r - box K r
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (mem_hit_of_mem_sub hy0 hx)]
  · rw [Set.indicator_of_notMem hx]
    exact zero_le

theorem countIntegral_of (hB : BoxVolume) : CountIntegral := by
  intro K _ _ J ρ hρ
  have hm : ∀ x : lat K J, Measurable
      (fun y => (hit K ρ (x : mixedSpace K)).indicator (fun _ => (1 : ℝ≥0∞)) y) :=
    fun x => measurable_const.indicator (measurableSet_hit K ρ x)
  calc vfac K * ENNReal.ofReal ((ρ / 2) ^ Module.finrank ℚ K) * volume (shell K)
      = ∫⁻ _ in shell K, vfac K * ENNReal.ofReal ((ρ / 2) ^ Module.finrank ℚ K) := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ y in shell K,
          (∑' x : lat K J, (hit K ρ (x : mixedSpace K)).indicator (fun _ => (1 : ℝ≥0∞)) y) *
            ENNReal.ofReal (ZLattice.covolume (lat K J)) :=
        setLIntegral_mono' (measurableSet_shell K) fun y hy => count_pointwise hB J hρ hy
    _ = (∫⁻ y in shell K,
          (∑' x : lat K J, (hit K ρ (x : mixedSpace K)).indicator (fun _ => (1 : ℝ≥0∞)) y)) *
            ENNReal.ofReal (ZLattice.covolume (lat K J)) :=
        lintegral_mul_const _ (Measurable.tsum hm)
    _ = (∑' x : lat K J, volume (shell K ∩ hit K ρ (x : mixedSpace K))) *
          ENNReal.ofReal (ZLattice.covolume (lat K J)) := by
        rw [lintegral_tsum fun x => (hm x).aemeasurable]
        congr 1
        refine tsum_congr fun x => ?_
        rw [lintegral_indicator_const (measurableSet_hit K ρ x), one_mul,
          Measure.restrict_apply (measurableSet_hit K ρ x), Set.inter_comm]
  exact le_rfl

end PI.Residue
end
end
