module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatCalcC
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLocA

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

section Helpers

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
  {s : Fin n → ι → Y → ℂ} {De : MvPolynomial (Fin n) ℂ}

end Helpers

section Det

variable {n : ℕ}

theorem flL_det_eq (f : V n →L[ℂ] V n) :
    f.det = ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℂ) * ∏ c, f (bas n c) (σ c) := by

  simp only [ContinuousLinearMap.det]
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp [LinearMap.toMatrix_apply, bas, Units.smul_def, zsmul_eq_mul]

theorem flL_det_contDiffAt {G : V n → V n →L[ℂ] V n} {y : V n} (hG : ContDiffAt ℂ ∞ G y) :
    ContDiffAt ℂ ∞ (fun v => (G v).det) y := by

  have e : (fun v => (G v).det) = fun v => ∑ σ : Equiv.Perm (Fin n),
      (Equiv.Perm.sign σ : ℂ) * ∏ c, G v (bas n c) (σ c) := funext fun v => flL_det_eq (G v)
  rw [e]
  refine ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun c _ => ?_)
  exact ((EuclideanSpace.proj (σ c)).comp
    (ContinuousLinearMap.apply ℂ (V n) (bas n c))).contDiff.contDiffAt.comp y hG

end Det

theorem leviAt_congr {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) (i : ι) (f g : Y → ℝ) (y : Y) (hy : y ∈ (A.chart i).source)
    (h : f =ᶠ[𝓝 y] g) (ξ : Fin n → ℂ) : A.leviAt i f y ξ = A.leviAt i g y ξ := by

  unfold WeightedAtlas.leviAt
  congr 1
  apply leviV_congr
  have hc := (A.chart i).continuousAt_symm ((A.chart i).map_source hy)
  rw [ContinuousAt, (A.chart i).left_inv hy] at hc
  filter_upwards [hc.eventually h] with v hv
  simp only [hv]

theorem leviAt_add {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) (i : ι) (f g : Y → ℝ) (y : Y)
    (hf : ContDiffAt ℝ 2 (f ∘ (A.chart i).symm) (A.chart i y))
    (hg : ContDiffAt ℝ 2 (g ∘ (A.chart i).symm) (A.chart i y)) (ξ : Fin n → ℂ) :
    A.leviAt i (fun x => f x + g x) y ξ = A.leviAt i f y ξ + A.leviAt i g y ξ := by

  unfold WeightedAtlas.leviAt
  rw [← Complex.add_re]
  congr 1
  simp only [Complex.ofReal_add]
  have hf1 : ContDiffAt ℝ 2 (fun v => ((f ((A.chart i).symm v) : ℝ) : ℂ)) (A.chart i y) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ hf
  have hg1 : ContDiffAt ℝ 2 (fun v => ((g ((A.chart i).symm v) : ℝ) : ℂ)) (A.chart i y) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ hg
  unfold leviV
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hw : wdb n k (fun v => ((f ((A.chart i).symm v) : ℝ) : ℂ) + ((g ((A.chart i).symm v) : ℝ) : ℂ))
      =ᶠ[𝓝 (A.chart i y)] fun v => wdb n k (fun v => ((f ((A.chart i).symm v) : ℝ) : ℂ)) v +
        wdb n k (fun v => ((g ((A.chart i).symm v) : ℝ) : ℂ)) v := by
    filter_upwards [hf1.eventually (by simp), hg1.eventually (by simp)] with v a b
    exact wdb_add (a.differentiableAt (by simp)) (b.differentiableAt (by simp))
  rw [wd_congr hw, wd_add (differentiableAt_wdb hf1) (differentiableAt_wdb hg1)]
  ring

theorem leviAt_log_normSq {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) (i : ι) (h : Y → ℂ) (y : Y) (hy : y ∈ (A.chart i).source)
    (hh : ∀ᶠ v in 𝓝 (A.chart i y), DifferentiableAt ℂ (h ∘ (A.chart i).symm) v)
    (hne : h y ≠ 0) (ξ : Fin n → ℂ) :
    A.leviAt i (fun x => Real.log (‖h x‖ ^ 2)) y ξ = 0 := by

  have hp0 : h ((A.chart i).symm (A.chart i y)) ≠ 0 := by rw [(A.chart i).left_inv hy]; exact hne
  have hH' : ∀ᶠ v in 𝓝 (A.chart i y), DifferentiableAt ℂ (fun v => h ((A.chart i).symm v)) v := hh
  obtain ⟨t, ht, hto, hpt⟩ := eventually_nhds_iff.1 hH'
  have hHt : DifferentiableOn ℂ (fun v => h ((A.chart i).symm v)) t :=
    fun v hv => (ht v hv).differentiableWithinAt
  have hne' : ∀ᶠ v in 𝓝 (A.chart i y), h ((A.chart i).symm v) ≠ 0 :=
    (hH'.self_of_nhds).continuousAt.eventually_ne hp0
  have key : ∀ j k, wd n j (wdb n k (fun v => ((Real.log (‖h ((A.chart i).symm v)‖ ^ 2) : ℝ) : ℂ)))
      (A.chart i y) = 0 := by
    intro j k
    have hQd : DifferentiableAt ℂ (fun v => fderiv ℂ (fun v => h ((A.chart i).symm v)) v (bas n k) *
        (h ((A.chart i).symm v))⁻¹) (A.chart i y) :=
      ((ReciprocityTheory.L2DbarEstimates.C.holoDeriv n t _ hto hHt (bas n k)).differentiableAt (hto.mem_nhds hpt)).mul
        ((hH'.self_of_nhds).inv hp0)
    have hev : wdb n k (fun v => ((Real.log (‖h ((A.chart i).symm v)‖ ^ 2) : ℝ) : ℂ)) =ᶠ[𝓝 (A.chart i y)]
        fun v => (starRingEnd ℂ) (fderiv ℂ (fun v => h ((A.chart i).symm v)) v (bas n k) *
          (h ((A.chart i).symm v))⁻¹) := by
      filter_upwards [hto.mem_nhds hpt, hne'] with v hvt hv0
      have hd : DifferentiableAt ℂ (fun v => h ((A.chart i).symm v)) v := ht v hvt
      have hdR := hd.restrictScalars ℝ
      have hN : ‖h ((A.chart i).symm v)‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hv0)
      rw [wdb_ofReal_comp (k := Real.log) (v := fun v => ‖h ((A.chart i).symm v)‖ ^ 2)
        (Real.differentiableAt_log hN) (by first | exact DifferentiableAt.norm_sq ℝ hdR | exact hdR.norm_sq (𝕜 := ℝ) | exact hdR.norm_sq ℂ)]
      have hsq : (fun y => (((‖h ((A.chart i).symm y)‖ ^ 2 : ℝ)) : ℂ)) =
          fun y => h ((A.chart i).symm y) * (starRingEnd ℂ) (h ((A.chart i).symm y)) := by
        funext y
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        try push_cast
        try ring
      have hcR : DifferentiableAt ℝ (fun y => (starRingEnd ℂ) (h ((A.chart i).symm y))) v :=
        Complex.conjCLE.differentiable.differentiableAt.comp v hdR
      have hc : ((‖h ((A.chart i).symm v)‖ ^ 2 : ℝ) : ℂ) =
          h ((A.chart i).symm v) * (starRingEnd ℂ) (h ((A.chart i).symm v)) := congrFun hsq v
      have hca : (starRingEnd ℂ) (h ((A.chart i).symm v)) ≠ 0 := (map_ne_zero _).2 hv0
      rw [hsq, wdb_mul hdR hcR, wdb_of_differentiableAt hd, wdb_conj hdR, wd_of_differentiableAt hd]
      simp only [Real.deriv_log, Complex.ofReal_inv, hc, map_mul, map_inv₀]
      field_simp
      ring
    rw [wd_congr hev, wd_conj (hQd.restrictScalars ℝ), wdb_of_differentiableAt hQd, map_zero]
  unfold WeightedAtlas.leviAt leviV
  simp only [key, zero_mul, Finset.sum_const_zero, Complex.zero_re]

end

end ReciprocityTheory.L2DbarEstimates.Y
