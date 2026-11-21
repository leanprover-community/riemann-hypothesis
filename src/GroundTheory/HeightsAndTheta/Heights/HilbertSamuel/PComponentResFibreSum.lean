import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComponentResFibreSum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgeSheet
import GroundTheory.HeightsAndTheta.Heights.Intersections.FourierIntegralBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartImageNull
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothMetricOfIsSmoothHerm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentResBridge

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (Res logH)

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
  (R : Res ι W e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

set_option linter.unusedSectionVars false

def resW (x : R.R.M) : ((k : K) → ι k) → ℂ :=
  (Ψ (segre (R.pt x)) 0)⁻¹ • segre (R.pt x)

theorem pt_mem (x : R.R.M) : R.pt x ∈ ReciprocityTheory.AnForm.R.conePts W :=
  R.liftAt_mem (R.mem_src_idx x)

theorem mem_mcPts_of_conePts {P : Ideal (MRing ι)}
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ ReciprocityTheory.AnForm.R.conePts W) : z ∈ mcPts P ∧ z ∈ zeroLocus ℂ W := by
  refine ⟨⟨hz.1, fun f hf => hz.2 _ (hW.1.2 (Ideal.mem_map_of_mem _ hf))⟩, fun f hf => ?_⟩
  simpa [MvPolynomial.coe_aeval_eq_eval] using hz.2 f hf

theorem projection_ne_zero_of_not_mem_badLocus {x : R.R.M} (hx : x ∉ resBad R Ψ) : Ψ (segre (R.pt x)) 0 ≠ 0 :=
  fun h => hx (Or.inl (Or.inr h))

theorem notMem_cone_of_notMem_resBad {x : R.R.M} (hx : x ∉ resBad R Ψ) :
    R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D :=
  fun h => hx (Or.inl (Or.inl h))

theorem resGood {x : R.R.M} (hx : x ∉ resBad R Ψ) (j : Fin R.atlas.n) (hj : x ∈ (R.atlas.chart j).source) :
    AnalyticAt ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) (R.atlas.chart j x) ∧
      LinearMap.det (fderiv ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) (R.atlas.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0 := by
  by_contra h
  exact hx (Or.inr ⟨j, hj, h⟩)

theorem resProj_eq_local {x z : R.R.M} (hz : z ∈ R.R.src (R.idx x)) :
    resProj R Ψ z = fun i => Ψ (segre (R.liftAt x z)) i.succ / Ψ (segre (R.liftAt x z)) 0 := by
  obtain ⟨c, hc, hzc⟩ := R.sameOrbit_liftAt (R.mem_src_idx z) hz
  have hpc : ∏ k, c k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hzc' : R.liftAt z z = fun q => c q.1 * R.liftAt x z q := hzc
  funext i
  simp only [resProj, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res.pt, hzc', segre_smul, map_smul, Pi.smul_apply,
    smul_eq_mul]
  exact mul_div_mul_left _ _ hpc

theorem analyticAt_segre_liftAt (x : R.R.M) (j : Fin R.atlas.n) {u : Fin e → ℂ}
    (hu : u ∈ (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x)) :
    AnalyticAt ℂ (fun v => Ψ (segre (R.liftAt x ((R.atlas.chart j).symm v)))) u := by
  have hl := R.analyticAt_liftAt_pi x j hu
  have hs : AnalyticAt ℂ (fun v => segre (R.liftAt x ((R.atlas.chart j).symm v))) u := by
    refine analyticAt_pi_iff.mpr fun i => ?_
    simp only [segre]
    exact Finset.analyticAt_fun_prod _ fun k _ => analyticAt_pi_iff.mp hl _
  exact (LinearMap.toContinuousLinearMap Ψ).analyticAt _ |>.comp hs

theorem analyticAt_resProj (x : R.R.M) (j : Fin R.atlas.n) (hj : x ∈ (R.atlas.chart j).source)
    (h0 : Ψ (segre (R.pt x)) 0 ≠ 0) :
    AnalyticAt ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) (R.atlas.chart j x) := by
  set u := R.atlas.chart j x
  have hsu : (R.atlas.chart j).symm u = x := (R.atlas.chart j).left_inv hj
  have hu : u ∈ (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x) :=
    ⟨(R.atlas.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact R.mem_src_idx x⟩
  have hH := analyticAt_segre_liftAt R Ψ x j hu
  have hH0 : AnalyticAt ℂ (fun v => Ψ (segre (R.liftAt x ((R.atlas.chart j).symm v))) 0) u :=
    analyticAt_pi_iff.mp hH 0
  have hne : Ψ (segre (R.liftAt x ((R.atlas.chart j).symm u))) 0 ≠ 0 := by rw [hsu]; exact h0
  have hF : AnalyticAt ℂ (fun v => fun i : Fin e =>
      Ψ (segre (R.liftAt x ((R.atlas.chart j).symm v))) i.succ /
        Ψ (segre (R.liftAt x ((R.atlas.chart j).symm v))) 0) u :=
    analyticAt_pi_iff.mpr fun i => (analyticAt_pi_iff.mp hH i.succ).div hH0 hne
  refine hF.congr ?_
  filter_upwards [((R.atlas.chart j).isOpen_inter_preimage_symm (R.R.isOpen_alt_bis (R.idx x))).mem_nhds hu,
    hH0.continuousAt.eventually_ne hne] with v hv hv0
  exact (resProj_eq_local R Ψ hv.2).symm

theorem resProj_image_null_of
    (hS : ∀ j, volume ((R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' resBad R Ψ) = 0) :
    volume (resProj R Ψ '' (resBad R Ψ ∩ {x | Ψ (segre (R.pt x)) 0 ≠ 0})) = 0 := by
  set T := resBad R Ψ ∩ {x | Ψ (segre (R.pt x)) 0 ≠ 0}
  have hsub : resProj R Ψ '' T ⊆ ⋃ j, (resProj R Ψ ∘ (R.atlas.chart j).symm) ''
      ((R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' T) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, hj⟩ := R.atlas.cover x
    refine Set.mem_iUnion.mpr ⟨j, R.atlas.chart j x, ⟨(R.atlas.chart j).map_source hj, ?_⟩, ?_⟩
    · rw [Set.mem_preimage, (R.atlas.chart j).left_inv hj]; exact hx
    · simp [(R.atlas.chart j).left_inv hj]
  refine measure_mono_null hsub (measure_iUnion_null fun j => ?_)
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
    (measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left))
      (hS j))
  intro u hu
  have hx := (R.atlas.chart j).map_target hu.1
  have hcu : R.atlas.chart j ((R.atlas.chart j).symm u) = u := (R.atlas.chart j).right_inv hu.1
  have := analyticAt_resProj R Ψ _ j hx hu.2.2
  rw [hcu] at this
  exact (this.differentiableAt.restrictScalars ℝ).differentiableWithinAt

theorem exists_sheet_resW {P : Ideal (MRing ι)} (L : Fin e → HermLine ι) (hP : IsArithVar P (e + 1))
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) (hL : ∀ j, IsSmoothHerm (L j))
    (x : R.R.M) (hx : x ∉ resBad R Ψ) :
    ∃ γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ, IsSheet P Ψ (resProj R Ψ x) (resW R Ψ x) γ ∧
      maDensity (fun j y' => pot L j (γ y')) (resProj R Ψ x) =
        pushDens R.atlas (fun j => R.pot (logH (L j))) (resProj R Ψ) x := by
  classical
  obtain ⟨k0⟩ := hP.1
  have hPh : IsMultiHomogIdeal P := hP.2.1.2.1
  set j := chartIdx R.atlas x with hjdef
  have hj : x ∈ (R.atlas.chart j).source := Classical.choose_spec (R.atlas.cover x)
  set u := R.atlas.chart j x with hudef
  have hsu : (R.atlas.chart j).symm u = x := (R.atlas.chart j).left_inv hj
  have huU : u ∈ (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x) :=
    ⟨(R.atlas.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact R.mem_src_idx x⟩
  obtain ⟨hQa, hQd⟩ := resGood R Ψ hx j hj
  set Q := resProj R Ψ ∘ (R.atlas.chart j).symm with hQdef
  set Df := fderiv ℂ Q u with hDf
  have hdet : Df.det ≠ 0 := hQd
  set Ce := Df.toContinuousLinearEquivOfDetNeZero hdet with hCe
  have hCe' : (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) = Df :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero Df hdet
  have hstrict : HasStrictFDerivAt Q (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) u := by
    rw [hCe']; exact hQa.hasStrictFDerivAt
  set F := hstrict.toOpenPartialHomeomorph Q with hF
  have hFc : (F : (Fin e → ℂ) → (Fin e → ℂ)) = Q := hstrict.toOpenPartialHomeomorph_coe
  have hus : u ∈ F.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hyt : Q u ∈ F.target := hstrict.image_mem_toOpenPartialHomeomorph_target
  have hσu : F.symm (Q u) = u := by
    have := F.left_inv hus
    rwa [hFc] at this
  have hy0 : Q u = resProj R Ψ x := by simp only [hQdef, Function.comp_apply, hsu]
  have hσa : AnalyticAt ℂ F.symm (Q u) := by
    refine F.analyticAt_symm (i := Ce) hyt ?_ ?_
    · rw [hσu, hFc]; exact hQa
    · rw [hσu, hFc, hCe']
  have hσd : HasFDerivAt F.symm (Ce.symm : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) (Q u) := by
    refine F.hasFDerivAt_symm hyt ?_
    rw [hσu, hFc, hCe']
    exact hQa.differentiableAt.hasFDerivAt
  set γ₀ : (Fin e → ℂ) → (Σ k, ι k) → ℂ :=
    fun y' => R.liftAt x ((R.atlas.chart j).symm (F.symm y')) with hγ₀
  have hγ₀a : AnalyticAt ℂ γ₀ (Q u) := (R.analyticAt_liftAt_pi x j huU).comp_of_eq hσa hσu
  have hγ₀u : γ₀ (Q u) = R.pt x := by simp only [hγ₀, hσu, hsu]; rfl
  set ψ0 : (Fin e → ℂ) → ℂ := fun y' => Ψ (segre (γ₀ y')) 0 with hψ0
  have hψ0a : AnalyticAt ℂ ψ0 (Q u) :=
    analyticAt_pi_iff.mp ((analyticAt_segre_liftAt R Ψ x j huU).comp_of_eq hσa hσu) 0
  have hψ0u : ψ0 (Q u) ≠ 0 := by
    simp only [hψ0, hγ₀u]; exact projection_ne_zero_of_not_mem_badLocus R Ψ hx
  set c : (Fin e → ℂ) → K → ℂ := fun y' => Function.update (fun _ => (1 : ℂ)) k0 (ψ0 y')⁻¹
    with hcdef
  have hc_ne : ∀ y', ψ0 y' ≠ 0 → ∀ k, c y' k ≠ 0 := by
    intro y' h k
    by_cases hk : k = k0
    · subst hk; simp [hcdef, h]
    · simp [hcdef, Function.update_of_ne hk]
  have hca : ∀ k, AnalyticAt ℂ (fun y' => c y' k) (Q u) := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp only [hcdef, Function.update_self]; exact hψ0a.inv hψ0u
    · simp only [hcdef, Function.update_of_ne hk]; exact analyticAt_const
  set γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun y' => bsmul (c y') (γ₀ y') with hγdef
  have hγa : AnalyticAt ℂ γ (Q u) :=
    analyticAt_pi_iff.mpr fun p => (hca p.1).mul (analyticAt_pi_iff.mp hγ₀a p)
  have hprod : ∀ y', ∏ k, c y' k = (ψ0 y')⁻¹ := fun y' => by
    simp [hcdef, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  have hseg : ∀ y', segre (γ y') = (ψ0 y')⁻¹ • segre (γ₀ y') := fun y' => by
    rw [← hprod y']; exact segre_smul (c y') (γ₀ y')
  refine ⟨γ, ⟨?_, ?_⟩, ?_⟩
  · rw [← hy0, hseg]
    simp only [hψ0, hγ₀u]
    rfl
  · rw [← hy0]
    have hU : ∀ᶠ y' in 𝓝 (Q u),
        F.symm y' ∈ (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x) :=
      hσa.continuousAt.preimage_mem_nhds (by
        rw [hσu]
        exact ((R.atlas.chart j).isOpen_inter_preimage_symm (R.R.isOpen_alt_bis (R.idx x))).mem_nhds huU)
    filter_upwards [hγa.eventually_analyticAt, hU, F.open_target.mem_nhds hyt,
      hψ0a.continuousAt.eventually_ne hψ0u] with y' ha hUy ht h0
    refine ⟨ha.differentiableAt, mcPts_smul hPh (c y') (hc_ne y' h0)
      (mem_mcPts_of_conePts hW (R.liftAt_mem hUy.2)).1, ?_⟩
    have hq : Q (F.symm y') = y' := by
      have := F.right_inv ht
      rwa [hFc] at this
    rw [hQdef, Function.comp_apply, resProj_eq_local R Ψ hUy.2] at hq
    rw [hseg, map_smul]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero]
      exact inv_mul_cancel₀ h0
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
      rw [← congrFun hq i, div_eq_inv_mul]
  · rw [← hy0]
    have hblk : ∀ k, ∃ i, γ₀ (Q u) ⟨k, i⟩ ≠ 0 := by
      rw [hγ₀u]; exact (pt_mem R x).1
    have hH : ∀ i, cxHessian (fun y' => pot L i (γ y')) (Q u) =
        cxHessian (fun y' => pot L i (γ₀ y')) (Q u) := by
      intro i
      set G : (Fin e → ℂ) → ℂ :=
        fun y' => ((-((L i).a k0 : ℝ) : ℝ) : ℂ) * Complex.log (ψ0 y' / ψ0 (Q u)) with hG
      set C : ℝ := -(((L i).a k0 : ℝ) * Real.log ‖ψ0 (Q u)‖) with hC
      have hGa : AnalyticAt ℂ G (Q u) := by
        refine analyticAt_const.mul ((hψ0a.div analyticAt_const hψ0u).clog ?_)
        show ψ0 (Q u) / ψ0 (Q u) ∈ Complex.slitPlane
        rw [div_self hψ0u]
        exact Complex.one_mem_slitPlane
      have heq : (fun y' => pot L i (γ y')) =ᶠ[𝓝 (Q u)]
          fun y' => pot L i (γ₀ y') + (G y').re + C := by
        filter_upwards [hψ0a.continuousAt.eventually_ne hψ0u,
          hγ₀a.continuousAt.eventually (isOpen_blockNonzero.mem_nhds hblk)] with y' h0 hb
        have hpos : 0 < (L i).h (γ₀ y') := (L i).pos _ hb
        have hn0 : ‖(ψ0 y')⁻¹‖ ^ (L i).a k0 ≠ 0 :=
          zpow_ne_zero _ (norm_ne_zero_iff.mpr (inv_ne_zero h0))
        simp only [pot, hγdef]
        rw [show bsmul (c y') (γ₀ y') = fun p => c y' p.1 * γ₀ y' p from rfl, (L i).smul _ _ (hc_ne y' h0),
          prod_norm_update_zpow, Real.log_mul hn0 hpos.ne',
          hG, hC, Complex.re_ofReal_mul, Complex.log_re, norm_div,
          Real.log_div (norm_ne_zero_iff.mpr h0) (norm_ne_zero_iff.mpr hψ0u), Real.log_zpow,
          norm_inv, Real.log_inv]
        ring
      rw [cxHessian_congr heq, cxHessian_add_re (φ := fun y' => pot L i (γ₀ y')) C
        (pot_contDiffAt (hL i) hγ₀a hblk) hGa]
    have hmd : maDensity (fun i y' => pot L i (γ y')) (Q u) =
        maDensity (fun i y' => pot L i (γ₀ y')) (Q u) := by
      simp only [maDensity, hH]
    rw [hmd, maDensity_eq_maDens]
    have hcd : ∀ i, ContDiffAt ℝ 2 (fun v => pot L i (R.liftAt x ((R.atlas.chart j).symm v)))
        (F.symm (Q u)) := by
      intro i
      rw [hσu]
      exact pot_contDiffAt (hL i) (R.analyticAt_liftAt_pi x j huU)
        (by rw [hsu]; exact (pt_mem R x).1)
    have hcomp : ReciprocityTheory.AnForm.maDens (fun i y' => pot L i (γ₀ y')) (Q u) =
        ReciprocityTheory.AnForm.maDens (fun i v => pot L i (R.liftAt x ((R.atlas.chart j).symm v)))
          (F.symm (Q u)) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC F.symm (Q u)).det :=
      ReciprocityTheory.AnForm.A.maDens_comp (fun i v => pot L i (R.liftAt x ((R.atlas.chart j).symm v)))
        F.symm (Q u) hσa hcd
    have hdetinv : LinearMap.det ((Ce.symm : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = (LinearMap.det (Df : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)))⁻¹ := by
      have := ContinuousLinearEquiv.det_coe_symm Ce
      rw [hCe'] at this
      exact this
    have hloc : ReciprocityTheory.AnForm.maDens (fun i v => pot L i (R.liftAt x ((R.atlas.chart j).symm v))) u =
        locDens R.atlas (fun i => R.pot (logH (L i))) j u := by
      unfold locDens
      rw [hsu]
      rfl
    rw [hcomp, hσu, ReciprocityTheory.AnForm.A.det_jacC, hσd.fderiv, hdetinv, hloc, Complex.normSq_inv,
      Complex.normSq_eq_norm_sq]
    unfold pushDens
    rw [div_eq_mul_inv]

end GroundTheory.Heights₂.Heights.HilbertSamuel.ComponentResBridge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace ComponentResBridge

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (Res logH)

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
  (R : Res ι W e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

set_option linter.unusedSectionVars false

theorem isMultiHomogIdeal_of_mem_minimalPrimes {P : Ideal (MRing ι)} (hP : IsArithVar P (e + 1))
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) :
    IsMultiHomogIdeal W := by
  have hPCh : IsMultiHomogIdeal (P.map (MvPolynomial.map (Int.castRingHom ℂ))) := by
    obtain ⟨T, hT, hPT⟩ := hP.2.1.2.1
    refine ⟨MvPolynomial.map (Int.castRingHom ℂ) '' T, ?_, by rw [hPT, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hT f hf
    exact ⟨a, fun d hd k => ha d (MvPolynomial.support_map_subset _ _ hd) k⟩
  exact (GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiHomogIdeal_iff W).mp
    (GroundTheory.Heights₂.Heights.NumbersDVR.MinimalPrimeMultiHomog.proof ℂ K ι _ W
      ((GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiHomogIdeal_iff _).mpr hPCh) hW)

theorem mem_zeroLocus_smul {J : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hJ : IsMultiHomogIdeal J) (c : K → ℂ)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ zeroLocus ℂ J) : (fun q => c q.1 * z q) ∈ zeroLocus ℂ J := by
  intro f hf
  have := ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hJ c z
    (fun g hg => by simpa [MvPolynomial.coe_aeval_eq_eval] using hz g hg) f hf
  simpa [MvPolynomial.coe_aeval_eq_eval] using this

theorem resW_mem_fibre {P : Ideal (MRing ι)} (hP : IsArithVar P (e + 1))
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) {x : R.R.M}
    (h0 : Ψ (segre (R.pt x)) 0 ≠ 0) : resW R Ψ x ∈ fibre P Ψ (resProj R Ψ x) := by
  obtain ⟨k0⟩ := hP.1
  let c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre (R.pt x)) 0)⁻¹
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [c, h0]
    · simp [c, Function.update_of_ne hk]
  have hpc : ∏ k, c k = (Ψ (segre (R.pt x)) 0)⁻¹ := by
    simp [c, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  refine ⟨fun p => c p.1 * R.pt x p,
    mcPts_smul hP.2.1.2.1 c hc (mem_mcPts_of_conePts hW (pt_mem R x)).1, ?_, ?_⟩
  · rw [segre_smul, hpc]; rfl
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [resW, h0]
    · simp only [resW, map_smul, Pi.smul_apply, smul_eq_mul, Fin.cons_succ, resProj]
      rw [div_eq_inv_mul]

theorem resW_injOn : Set.InjOn (resW R Ψ)
    {x | R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D ∧ Ψ (segre (R.pt x)) 0 ≠ 0} := by
  intro x hx x' hx' hw
  refine R.R.inj _ _ x (R.mem_src_idx x) x' (R.mem_src_idx x') hx.1 ?_
  refine sameOrbit_of_segre (pt_mem R x').1
    (Ψ (segre (R.pt x)) 0 * (Ψ (segre (R.pt x')) 0)⁻¹) (by simp [hx.2, hx'.2]) ?_
  have := congrArg (fun v => Ψ (segre (R.pt x)) 0 • v) hw
  simp only [resW, smul_smul, mul_inv_cancel₀ hx.2, one_smul] at this
  exact this

theorem exists_of_lift {P : Ideal (MRing ι)} {y : Fin e → ℂ} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts P) (hzW : z ∈ zeroLocus ℂ W) (hzD : z ∉ ReciprocityTheory.AnForm.R.conePts R.D)
    (hΨz : Ψ (segre z) = Fin.cons 1 y) :
    ∃ x, R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D ∧ Ψ (segre (R.pt x)) 0 ≠ 0 ∧
      resProj R Ψ x = y ∧ resW R Ψ x = segre z := by
  have hD : IsMultiHomogIdeal R.D := (GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiHomogIdeal_iff R.D).mp R.homog
  have hzc : z ∈ ReciprocityTheory.AnForm.R.conePts W :=
    ⟨hz.1, fun f hf => by simpa [MvPolynomial.coe_aeval_eq_eval] using hzW f hf⟩
  obtain ⟨i, x, hx, c1, hc1, h1⟩ := R.R.surj z hzc hzD
  obtain ⟨c2, hc2, h2⟩ := R.R.compat i (R.idx x) x ⟨hx, R.mem_src_idx x⟩
  set c : K → ℂ := fun k => c1 k / c2 k with hcdef
  have hc : ∀ k, c k ≠ 0 := fun k => div_ne_zero (hc1 k) (hc2 k)
  have hxc : R.pt x = fun q => c q.1 * z q := by
    funext q
    have e : c2 q.1 * R.pt x q = c1 q.1 * z q := (congrFun h2 q).symm.trans (congrFun h1 q)
    rw [hcdef, div_mul_eq_mul_div, eq_div_iff (hc2 q.1), ← e]
    ring
  have hseg : segre (R.pt x) = (∏ k, c k) • segre z := by rw [hxc, segre_smul]
  have hpc : ∏ k, c k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hΨx : Ψ (segre (R.pt x)) = (∏ k, c k) • Fin.cons 1 y := by rw [hseg, map_smul, hΨz]
  have h0 : Ψ (segre (R.pt x)) 0 = ∏ k, c k := by simp [hΨx]
  refine ⟨x, fun h => hzD ?_, by rw [h0]; exact hpc, ?_, ?_⟩
  · have hz' : z = fun q => (c q.1)⁻¹ * R.pt x q := by
      funext q
      rw [hxc, ← mul_assoc, inv_mul_cancel₀ (hc q.1), one_mul]
    refine ⟨hz.1, ?_⟩
    rw [hz']
    exact ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hD (fun k => (c k)⁻¹) (R.pt x) h.2
  · funext i
    simp only [resProj, hΨx, h0, Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
    field_simp
  · rw [resW, h0, hseg, smul_smul, inv_mul_cancel₀ hpc, one_smul]

theorem coneD_null (hA : ChartDimLt.Statement) (hB : ChartRatioImageNull.Statement) {P : Ideal (MRing ι)}
    (hP : IsArithVar P (e + 1)) (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) :
    volume {y : Fin e → ℂ | ∃ z ∈ zeroLocus ℂ W, z ∈ ReciprocityTheory.AnForm.R.conePts R.D ∧
      Ψ (segre z) = Fin.cons 1 y} = 0 := by
  classical
  set PC : Ideal (MvPolynomial (Σ k, ι k) ℂ) := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hPC

  have hdimW : ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ W) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    set PQ : Ideal (MvPolynomial (Σ k, ι k) ℚ) := P.map (MvPolynomial.map (Int.castRingHom ℚ)) with hPQ
    have hvar := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isProjVarQ_of_isArithVar hP
    have : PQ.IsPrime := hvar.1.isPrime
    have hext : ReciprocityTheory.AnForm.R.extC PQ = PC := by
      rw [ReciprocityTheory.AnForm.R.extC, hPQ, hPC, Ideal.map_map]
      congr 1
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun q => ?_)
      · simp only [RingHom.comp_apply, MvPolynomial.map_C]
        congr 1
      · simp
    rw [← hext] at hW
    rw [ReciprocityTheory.AnForm.R.ringKrullDim_of_mem_minimalPrimes_extC PQ W hW]
    exact hvar.2
  have hWh : IsMultiHomogIdeal W := isMultiHomogIdeal_of_mem_minimalPrimes hP hW
  have hDh : IsMultiHomogIdeal R.D :=
    (GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiHomogIdeal_iff R.D).mp R.homog
  have hsuph : IsMultiHomogIdeal (W ⊔ R.D) := by
    obtain ⟨T, hT, hWT⟩ := hWh
    obtain ⟨T', hT', hDT⟩ := hDh
    exact ⟨T ∪ T', fun f hf => hf.elim (hT f) (hT' f), by rw [Ideal.span_union, ← hWT, ← hDT]⟩

  have hsup : ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ (W ⊔ R.D)) <
      ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    have : W.IsPrime := hW.1.1
    obtain ⟨g, hgD, hgW⟩ : ∃ g ∈ R.D, g ∉ W := by
      by_contra hcon
      push_neg at hcon
      exact R.not_le hcon
    have hg0 : Ideal.Quotient.mk W g ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hg0)
    have eqv : ((MvPolynomial (Σ k, ι k) ℂ ⧸ W) ⧸ Ideal.span {Ideal.Quotient.mk W g}) ≃+*
        MvPolynomial (Σ k, ι k) ℂ ⧸ (W ⊔ Ideal.span {g}) :=
      (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
        (DoubleQuot.quotQuotEquivQuotSup W (Ideal.span {g}))
    rw [ringKrullDim_eq_of_ringEquiv eqv, hdimW] at h1
    have hle : W ⊔ Ideal.span {g} ≤ W ⊔ R.D :=
      sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr hgD) W
    have h2 := ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hle)
    generalize ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ (W ⊔ Ideal.span {g})) = a at h1 h2
    generalize ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ (W ⊔ R.D)) = b at h2 ⊢
    refine lt_of_le_of_lt h2 ?_
    induction a using WithBot.recBotCoe with
    | bot => exact WithBot.bot_lt_coe _
    | coe a =>
      induction a using ENat.recTopCoe with
      | top => exact absurd h1 (by exact_mod_cast (show ¬ ((⊤ : ℕ∞) + 1 ≤ ((e + Fintype.card K : ℕ) : ℕ∞)) by simp))
      | coe a =>
        have : a + 1 ≤ e + Fintype.card K := by exact_mod_cast h1
        exact_mod_cast (show a < e + Fintype.card K by omega)

  refine measure_mono_null (t := ⋃ p : (k : K) → ι k,
      {y : Fin e → ℂ | ∃ z ∈ zeroLocus ℂ (ReciprocityTheory.AnForm.R.chartIdeal (W ⊔ R.D) p), Ψ (segre z) 0 ≠ 0 ∧
        (Fin.cons 1 y : Fin (e + 1) → ℂ) = (Ψ (segre z) 0)⁻¹ • Ψ (segre z)}) ?_ ?_
  · rintro y ⟨z, hzW, hzD, hzy⟩
    choose p hp using hzD.1
    simp only [Set.mem_iUnion]
    refine ⟨p, ReciprocityTheory.AnForm.R.affCoord p z, ?_, ?_⟩
    · have hcone : z ∈ ReciprocityTheory.AnForm.R.conePts (W ⊔ R.D) := by
        refine ⟨hzD.1, fun f hf => ?_⟩
        have hker : W ⊔ R.D ≤ RingHom.ker (eval z) := sup_le
          (fun f hf => RingHom.mem_ker.mpr (by simpa [MvPolynomial.coe_aeval_eq_eval] using hzW f hf))
          (fun f hf => RingHom.mem_ker.mpr (hzD.2 f hf))
        exact RingHom.mem_ker.mp (hker hf)
      have h := (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hsuph p z hp).1 hcone
      intro f hf
      have hf' := h f hf
      rwa [← MvPolynomial.coe_aeval_eq_eval] at hf'
    · have hc : (∏ k, z ⟨k, p k⟩)⁻¹ ≠ 0 := inv_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => hp k)
      have hseg : segre (ReciprocityTheory.AnForm.R.affCoord p z) = (∏ k, z ⟨k, p k⟩)⁻¹ • segre z := by
        funext i
        simp only [segre, ReciprocityTheory.AnForm.R.affCoord, Pi.smul_apply, smul_eq_mul, Finset.prod_div_distrib]
        rw [div_eq_inv_mul]
      have hΨ : Ψ (segre (ReciprocityTheory.AnForm.R.affCoord p z)) =
          (∏ k, z ⟨k, p k⟩)⁻¹ • (Fin.cons 1 y : Fin (e + 1) → ℂ) := by
        rw [hseg, map_smul, hzy]
      rw [hΨ, Pi.smul_apply, Fin.cons_zero, smul_eq_mul, mul_one, smul_smul, inv_mul_cancel₀ hc, one_smul]
      exact ⟨hc, rfl⟩
  · refine measure_iUnion_null fun p => ?_
    exact hB K ι _ e Ψ (hA K ι (W ⊔ R.D) e p hsuph hsup)

end ComponentResBridge

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M ComponentResBridge

theorem ComponentResFibreSum.proof (h₁ : ComponentResBadNull.Statement) (hA : ChartDimLt.Statement)
    (hB : ChartRatioImageNull.Statement) : ComponentResFibreSum.Statement := by
  classical
  intro K _ _ ι _ P e L W R Ψ hP hL hW hΨ

  let A : HermLine ι := HermLine.ofWeight (fun _ => (1 : ℝ)) (fun _ _ _ => rfl)
  have hA1 : ∀ z, logNorm A 1 z = 1 := fun z => by
    simp [logNorm, A, HermLine.ofWeight, Real.exp_neg]
  have hAs : IsSmoothHerm A := contDiffOn_const
  have hs : IsSectionOn P A 1 := by
    refine ⟨0, fun k => by simp [A, HermLine.ofWeight], fun m hm k => ?_, fun h => ?_⟩
    · rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
      subst hm
      simp
    · exact hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  have hWh : IsMultiHomogIdeal W := isMultiHomogIdeal_of_mem_minimalPrimes hP hW

  have hN : volume (resProj R Ψ '' (resBad R Ψ ∩ {x | Ψ (segre (R.pt x)) 0 ≠ 0}) ∪
      {y : Fin e → ℂ | ∃ z ∈ zeroLocus ℂ W, z ∈ ReciprocityTheory.AnForm.R.conePts R.D ∧
        Ψ (segre z) = Fin.cons 1 y}) = 0 :=
    measure_union_null (resProj_image_null_of R Ψ (h₁ K ι P e W R Ψ hP hW hΨ))
      (coneD_null R Ψ hA hB hP hW)
  filter_upwards [compl_mem_ae_iff.mpr hN, sheetIndep K ι P e Ψ L A 1 hP hΨ hL hAs hs] with y hyN hind
  have hy1 : y ∉ resProj R Ψ '' (resBad R Ψ ∩ {x | Ψ (segre (R.pt x)) 0 ≠ 0}) := fun h => hyN (Or.inl h)
  have hy2 : ¬ ∃ z ∈ zeroLocus ℂ W, z ∈ ReciprocityTheory.AnForm.R.conePts R.D ∧ Ψ (segre z) = Fin.cons 1 y :=
    fun h => hyN (Or.inr h)

  have hsub : resW R Ψ '' (resProj R Ψ ⁻¹' {y} \ resBad R Ψ) ⊆ fibre P Ψ y := by
    rintro _ ⟨x, hx, rfl⟩
    have := resW_mem_fibre R Ψ hP hW (projection_ne_zero_of_not_mem_badLocus R Ψ hx.2)
    rwa [show resProj R Ψ x = y from hx.1] at this

  have hzero : ∀ w ∈ fibre P Ψ y, w ∉ resW R Ψ '' (resProj R Ψ ⁻¹' {y} \ resBad R Ψ) →
      sheetDensity P Ψ (pot L) ((mcPts P ∩ zeroLocus ℂ W).indicator fun _ => (1 : ℝ)) y w = 0 := by
    intro w hw hwS
    obtain ⟨-, -, -, hΨw⟩ := hw
    unfold sheetDensity
    split_ifs with hγ
    · rw [Set.indicator_of_notMem, zero_mul]
      rintro ⟨hzP, hzW⟩
      have hseg : segre (hγ.choose y) = w := hγ.choose_spec.1
      have hΨz : Ψ (segre (hγ.choose y)) = Fin.cons 1 y := by rw [hseg]; exact hΨw
      by_cases hzD : hγ.choose y ∈ ReciprocityTheory.AnForm.R.conePts R.D
      · exact hy2 ⟨_, hzW, hzD, hΨz⟩
      · obtain ⟨x, -, hx0, hxy, hxw⟩ := exists_of_lift R Ψ hzP hzW hzD hΨz
        exact hwS ⟨x, ⟨hxy, fun hbad => hy1 ⟨x, ⟨hbad, hx0⟩, hxy⟩⟩, hxw.trans hseg⟩
    · rfl
  rw [finsum_mem_inter_support_eq' _ (fibre P Ψ y) (resW R Ψ '' (resProj R Ψ ⁻¹' {y} \ resBad R Ψ))
    fun w hw => ⟨fun h => by_contra fun h' => hw (hzero w h h'), fun h => hsub h⟩]
  rw [finsum_mem_image ((resW_injOn R Ψ).mono fun x hx => show _ ∧ _ from
    ⟨notMem_cone_of_notMem_resBad R Ψ hx.2, projection_ne_zero_of_not_mem_badLocus R Ψ hx.2⟩)]
  refine finsum_mem_congr rfl fun x hx => ?_
  obtain ⟨γ, hγ, hval⟩ := exists_sheet_resW R Ψ L hP hW hL x hx.2
  rw [show resProj R Ψ x = y from hx.1] at hγ hval
  have hex : ∃ γ, IsSheet P Ψ y (resW R Ψ x) γ := ⟨γ, hγ⟩
  unfold sheetDensity
  rw [dif_pos hex]
  have hc := hex.choose_spec

  have hmem : hex.choose y ∈ mcPts P ∩ zeroLocus ℂ W := by
    refine ⟨hc.2.self_of_nhds.2.1, ?_⟩
    have hseg : segre (hex.choose y) = (Ψ (segre (R.pt x)) 0)⁻¹ • segre (R.pt x) := hc.1
    obtain ⟨c, -, hcz⟩ := sameOrbit_of_segre (pt_mem R x).1 _
      (inv_ne_zero (projection_ne_zero_of_not_mem_badLocus R Ψ hx.2)) hseg
    rw [hcz]
    exact mem_zeroLocus_smul hWh c (mem_mcPts_of_conePts hW (pt_mem R x)).2
  rw [Set.indicator_of_mem hmem, one_mul]
  have := hind _ _ _ hc hγ
  rw [hA1, hA1, one_mul, one_mul] at this
  exact this.trans hval

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end
