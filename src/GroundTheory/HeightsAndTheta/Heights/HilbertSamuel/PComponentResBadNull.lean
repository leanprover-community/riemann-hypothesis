import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComponentResBadNull
import GroundTheory.HeightsAndTheta.Heights.Intersections.UnitChartOperator
import GroundTheory.HeightsAndTheta.Heights.Intersections.FourierIntegralBound
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeK
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeL

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Topology Filter

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)

omit [Fintype K] in

theorem homogD : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal R.D :=
  (GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff R.D).mp R.homog

theorem mem_D_of_sameOrbit {z z' : (Σ k, ι k) → ℂ} (h : ReciprocityTheory.AnForm.R.SameOrbit z z')
    (hz' : z' ∈ ReciprocityTheory.AnForm.R.conePts R.D) : z ∈ ReciprocityTheory.AnForm.R.conePts R.D := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => ?_, ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul (homogD R) c z' hz'.2⟩
  obtain ⟨i, hi⟩ := hz'.1 k
  exact ⟨i, mul_ne_zero (hc k) hi⟩

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem sameOrbit_symm {z z' : (Σ k, ι k) → ℂ} (h : ReciprocityTheory.AnForm.R.SameOrbit z z') :
    ReciprocityTheory.AnForm.R.SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext q
  rw [← mul_assoc, inv_mul_cancel₀ (hc q.1), one_mul]

theorem pt_mem_D_iff {x y : R.R.M} (hy : y ∈ R.R.src (R.idx x)) :
    R.pt y ∈ ReciprocityTheory.AnForm.R.conePts R.D ↔ R.liftAt x y ∈ ReciprocityTheory.AnForm.R.conePts R.D := by
  have h := GroundTheory.Heights₂.Heights.Inter.res_compat R x y hy (R.mem_src_idx y)
  exact ⟨fun hp => mem_D_of_sameOrbit R h hp, fun hl => mem_D_of_sameOrbit R (sameOrbit_symm h) hl⟩

theorem psi_pt_eq {x y : R.R.M} (hy : y ∈ R.R.src (R.idx x))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    ∃ μ : ℂ, μ ≠ 0 ∧ Ψ (segre (R.pt y)) = μ • Ψ (segre (R.liftAt x y)) := by
  obtain ⟨c, hc, hyc⟩ := GroundTheory.Heights₂.Heights.Inter.res_compat R y x (R.mem_src_idx y) hy
  refine ⟨∏ k, c k, Finset.prod_ne_zero_iff.mpr fun k _ => hc k, ?_⟩
  rw [show R.pt y = R.liftAt y y from rfl, hyc, segre_smul, map_smul]

theorem resProj_eq_local (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {x y : R.R.M}
    (hy : y ∈ R.R.src (R.idx x)) :
    resProj R Ψ y = fun i => Ψ (segre (R.liftAt x y)) i.succ / Ψ (segre (R.liftAt x y)) 0 := by
  obtain ⟨μ, hμ, hμeq⟩ := psi_pt_eq R hy Ψ
  funext i
  simp only [resProj, hμeq, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hμ

theorem analyticAt_segre_liftAt (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.R.M)
    (j : Fin R.atlas.n) {u : Fin e → ℂ}
    (hu : u ∈ (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x)) :
    AnalyticAt ℂ (fun v => Ψ (segre (R.liftAt x ((R.atlas.chart j).symm v)))) u := by
  have hl := R.analyticAt_liftAt_pi x j hu
  have hs : AnalyticAt ℂ (fun v => segre (R.liftAt x ((R.atlas.chart j).symm v))) u := by
    refine analyticAt_pi_iff.mpr fun i => ?_
    simp only [segre]
    exact Finset.analyticAt_fun_prod _ fun k _ => analyticAt_pi_iff.mp hl _
  exact (LinearMap.toContinuousLinearMap Ψ).analyticAt _ |>.comp hs

theorem analyticAt_resProj (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.R.M)
    (j : Fin R.atlas.n) (hj : x ∈ (R.atlas.chart j).source) (h0 : Ψ (segre (R.pt x)) 0 ≠ 0) :
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

theorem det_resProj_chart (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {x : R.R.M}
    {j k : Fin R.atlas.n} (hj : x ∈ (R.atlas.chart j).source) (hk : x ∈ (R.atlas.chart k).source)
    (h0 : Ψ (segre (R.pt x)) 0 ≠ 0) :
    LinearMap.det (fderiv ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) (R.atlas.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
      LinearMap.det (fderiv ℂ (resProj R Ψ ∘ (R.atlas.chart k).symm) (R.atlas.chart k x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) *
      LinearMap.det (fderiv ℂ (R.atlas.chart k ∘ (R.atlas.chart j).symm) (R.atlas.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := by
  set u := R.atlas.chart j x
  have hsu : (R.atlas.chart j).symm u = x := (R.atlas.chart j).left_inv hj
  set T := R.atlas.chart k ∘ (R.atlas.chart j).symm with hTdef
  have huk : u ∈ (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' (R.atlas.chart k).source :=
    ⟨(R.atlas.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact hk⟩
  have hT : AnalyticAt ℂ T u := R.atlas.holo j k u huk
  have hTu : T u = R.atlas.chart k x := by simp only [hTdef, Function.comp_apply, hsu]
  have hQk := analyticAt_resProj R Ψ x k hk h0
  have heq : resProj R Ψ ∘ (R.atlas.chart j).symm =ᶠ[𝓝 u] (resProj R Ψ ∘ (R.atlas.chart k).symm) ∘ T := by
    filter_upwards [((R.atlas.chart j).isOpen_inter_preimage_symm (R.atlas.chart k).open_source).mem_nhds
      huk] with v hv
    simp only [hTdef, Function.comp_apply, (R.atlas.chart k).left_inv hv.2]
  rw [heq.fderiv_eq, fderiv_comp u (by rw [hTu]; exact hQk.differentiableAt) hT.differentiableAt, hTu]
  exact LinearMap.det_comp _ _

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem mcPts_of_conePts {P : Ideal (MRing ι)}
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ ReciprocityTheory.AnForm.R.conePts W) : z ∈ mcPts P :=
  ⟨hz.1, fun _ hf => hz.2 _ (hW.1.2 (Ideal.mem_map_of_mem _ hf))⟩

theorem pt_mem_mcPts {P : Ideal (MRing ι)}
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) (x : R.R.M) :
    R.pt x ∈ mcPts P :=
  mcPts_of_conePts hW (GroundTheory.Heights₂.Heights.Inter.res_mem R x (R.mem_src_idx x))

def resW (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.R.M) : ((k : K) → ι k) → ℂ :=
  (Ψ (segre (R.pt x)) 0)⁻¹ • segre (R.pt x)

theorem resW_mem_fibre {P : Ideal (MRing ι)}
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) (hK : Nonempty K)
    (hPh : IsMultiHomogIdeal P) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {x : R.R.M}
    (h0 : Ψ (segre (R.pt x)) 0 ≠ 0) : resW R Ψ x ∈ fibre P Ψ (resProj R Ψ x) := by
  obtain ⟨k0⟩ := hK
  let c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre (R.pt x)) 0)⁻¹
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [c, h0]
    · simp [c, Function.update_of_ne hk]
  have hpc : ∏ k, c k = (Ψ (segre (R.pt x)) 0)⁻¹ := by
    simp [c, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  refine ⟨fun p => c p.1 * R.pt x p, mcPts_smul hPh c hc (pt_mem_mcPts R hW x), ?_, ?_⟩
  · rw [segre_smul, hpc]; rfl
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [resW, h0]
    · simp only [resW, map_smul, Pi.smul_apply, smul_eq_mul, Fin.cons_succ, resProj]
      rw [div_eq_inv_mul]

theorem resW_injOn (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    Set.InjOn (resW R Ψ) {x | R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D ∧ Ψ (segre (R.pt x)) 0 ≠ 0} := by
  intro x hx x' hx' hw
  refine R.R.inj (R.idx x) (R.idx x') x (R.mem_src_idx x) x' (R.mem_src_idx x') hx.1 ?_
  have hseg : segre (R.pt x) = (Ψ (segre (R.pt x)) 0 * (Ψ (segre (R.pt x')) 0)⁻¹) • segre (R.pt x') := by
    have := congrArg (fun v => Ψ (segre (R.pt x)) 0 • v) hw
    simp only [resW, smul_smul, mul_inv_cancel₀ hx.2, one_smul] at this
    exact this
  obtain ⟨c, hc, h⟩ := sameOrbit_of_segre
    (GroundTheory.Heights₂.Heights.Inter.res_mem R x' (R.mem_src_idx x')).1
    (Ψ (segre (R.pt x)) 0 * (Ψ (segre (R.pt x')) 0)⁻¹) (by simp [hx.2, hx'.2]) hseg
  exact ⟨c, hc, h⟩

theorem resFib_finite {P : Ideal (MRing ι)} (hP : IsArithVar P (e + 1))
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (hΨ : IsGoodProj P Ψ) (y : Fin e → ℂ) :
    (resProj R Ψ ⁻¹' {y} ∩
      {x | R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D ∧ Ψ (segre (R.pt x)) 0 ≠ 0}).Finite := by
  refine Set.Finite.of_finite_image (f := resW R Ψ) ((fibreFinite K ι P e Ψ hP hΨ y).subset ?_)
    ((resW_injOn R Ψ).mono fun x hx => hx.2)
  rintro _ ⟨x, hx, rfl⟩
  have := resW_mem_fibre R hW hP.1 hP.2.1.2.1 Ψ hx.2.2
  rwa [show resProj R Ψ x = y from hx.1] at this

end GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Topology Filter Set

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)

theorem isAnalyticSubset_D :
    R.atlas.IsAnalyticSubset {x | R.pt x ∈ ReciprocityTheory.AnForm.R.conePts R.D} := by
  intro x
  set i := R.idx x
  obtain ⟨n, g, hg⟩ :=
    (Submodule.fg_iff_exists_fin_generating_family).mp (IsNoetherian.noetherian (R.R.bd i))
  refine ⟨R.R.src i, R.R.isOpen_alt_bis i, R.mem_src_idx x, n, fun l y => eval (R.R.coord i y) (g l),
    fun l => R.isGoodAtlas.1 i (g l), ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hyD, hy⟩
    refine ⟨hy, fun l => ?_⟩
    have hz := (R.R.zero_bd i y hy).mpr ((pt_mem_D_iff R hy).mp hyD)
    have hgl : g l ∈ R.R.bd i := by
      rw [← hg]
      exact Submodule.subset_span ⟨l, rfl⟩
    exact hz _ hgl
  · rintro ⟨hy, hz⟩
    refine ⟨(pt_mem_D_iff R hy).mpr ((R.R.zero_bd i y hy).mp fun h hh => ?_), hy⟩
    rw [← hg] at hh
    induction hh using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨l, rfl⟩ := ha
      exact hz l
    | zero => simp
    | add a b _ _ ha hb => simp [ha, hb]
    | smul a b _ hb => simp [smul_eq_mul, hb]

theorem interior_D : interior {x | R.pt x ∈ ReciprocityTheory.AnForm.R.conePts R.D} = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  set i := R.idx x
  have hxi : x ∈ R.R.src i := R.mem_src_idx x
  set sd := R.R.sncAt i x hxi
  have hcont : ContinuousOn (fun y => eval (R.R.coord i y) sd.h) (R.R.src i) :=
    (MvPolynomial.continuous_eval sd.h).comp_continuousOn
      (continuousOn_iff_continuous_domRestrict.mpr (R.R.isEmbedding i).continuous)
  set O := interior {x | R.pt x ∈ ReciprocityTheory.AnForm.R.conePts R.D} ∩
    (R.R.src i ∩ (fun y => eval (R.R.coord i y) sd.h) ⁻¹' {0}ᶜ) with hOdef
  have hO : IsOpen O :=
    isOpen_interior.inter (hcont.isOpen_inter_preimage (R.R.isOpen_alt_bis i) isOpen_compl_singleton)
  have hxO : x ∈ O := ⟨hx, hxi, sd.eval_h⟩
  obtain ⟨ψ, -, hxψ, hsub, hform⟩ := R.isGoodAtlas.2 i x hxi sd.r sd.span_eq O hO hxO
  have hnull : volume ψ.target = 0 := by
    refine measure_mono_null (t := ⋃ l : Fin e, {u : Fin e → ℂ | u l = 0}) ?_
      (measure_iUnion_null fun l => ?_)
    · intro u hu
      have hy : ψ.symm u ∈ ψ.source := ψ.map_target hu
      have hyO := hsub hy
      have hyD : R.pt (ψ.symm u) ∈ ReciprocityTheory.AnForm.R.conePts R.D :=
        (interior_subset (s := {x | R.pt x ∈ ReciprocityTheory.AnForm.R.conePts R.D}) hyO.1.1 :)
      have hbd := (R.R.zero_bd i (ψ.symm u) hyO.2).mpr ((pt_mem_D_iff R (x := x) hyO.2).mp hyD)
      have h0 := hbd _ sd.mem_bd
      rw [map_mul, map_prod] at h0
      have hprod := (mul_eq_zero.mp h0).resolve_left hyO.1.2.2
      obtain ⟨l, -, hl0⟩ := Finset.prod_eq_zero_iff.mp hprod
      have hu' : u = ReciprocityTheory.AnForm.R.evalFam sd.r (R.R.coord i (ψ.symm u)) :=
        (ψ.right_inv hu).symm.trans (hform _ hy)
      exact Set.mem_iUnion.mpr ⟨l, (congrFun hu' l).trans hl0⟩
    · rw [MeasureTheory.volume_pi]
      exact Measure.pi_hyperplane _ l 0
  exact (ψ.open_target.measure_pos volume ⟨ψ x, ψ.map_source hxψ⟩).ne' hnull

theorem D_null (j : Fin R.atlas.n) :
    volume ((R.atlas.chart j).target ∩
      (R.atlas.chart j).symm ⁻¹' {x | R.pt x ∈ ReciprocityTheory.AnForm.R.conePts R.D}) = 0 := by
  refine measure_mono_null ?_
    (ReciprocityTheory.AnForm.M.analyticNull R.atlas _ (isAnalyticSubset_D R) (interior_D R) j)
  rintro u ⟨hu, hD⟩
  exact ⟨(R.atlas.chart j).symm u, ⟨hD, (R.atlas.chart j).map_target hu⟩, (R.atlas.chart j).right_inv hu⟩

theorem isOpen_chart_notD (j : Fin R.atlas.n) :
    IsOpen ((R.atlas.chart j).target ∩
      (R.atlas.chart j).symm ⁻¹' {x | R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D}) := by
  rw [isOpen_iff_mem_nhds]
  rintro u1 ⟨hu1, hB1⟩
  set x1 := (R.atlas.chart j).symm u1
  have hV : (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x1) ∈ 𝓝 u1 :=
    ((R.atlas.chart j).isOpen_inter_preimage_symm (R.R.isOpen_alt_bis _)).mem_nhds
      ⟨hu1, R.mem_src_idx x1⟩
  have hnot : ¬ ∀ f ∈ R.D, eval (R.liftAt x1 x1) f = 0 := fun h =>
    hB1 ⟨(GroundTheory.Heights₂.Heights.Inter.res_mem R x1 (R.mem_src_idx x1)).1, h⟩
  push Not at hnot
  obtain ⟨f, hfD, hf0⟩ := hnot
  have hcont : ContinuousAt (fun u => eval (R.liftAt x1 ((R.atlas.chart j).symm u)) f) u1 :=
    (MvPolynomial.continuous_eval _).continuousAt.comp
      (R.analyticAt_liftAt_pi x1 j ⟨hu1, R.mem_src_idx x1⟩).continuousAt
  filter_upwards [hV, hcont.eventually_ne hf0] with u hu hne
  refine ⟨hu.1, fun hB => ?_⟩
  exact hne (((pt_mem_D_iff R hu.2).mp hB).2 f hfD)

theorem not_flat {P : Ideal (MRing ι)} (hP : IsArithVar P (e + 1))
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (hΨ : IsGoodProj P Ψ) (j : Fin R.atlas.n)
    {O : Set (Fin e → ℂ)} (hO : IsOpen O) (hOt : O ⊆ (R.atlas.chart j).target) (hne : O.Nonempty)
    (h0 : ∀ u ∈ O, Ψ (segre (R.pt ((R.atlas.chart j).symm u))) 0 ≠ 0)
    (han : AnalyticOnNhd ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) O)
    (hdet : ∀ u ∈ O, LinearMap.det (fderiv ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) u :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0) : False := by
  set O' := O ∩ ((R.atlas.chart j).target ∩
    (R.atlas.chart j).symm ⁻¹' {x | R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D}) with hO'def
  have hO' : IsOpen O' := hO.inter (isOpen_chart_notD R j)
  have hne' : O'.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    obtain ⟨u, hu⟩ := hne
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO u hu
    have hsub : Metric.ball u r ⊆ (R.atlas.chart j).target ∩
        (R.atlas.chart j).symm ⁻¹' {x | R.pt x ∈ ReciprocityTheory.AnForm.R.conePts R.D} := by
      intro v hv
      have hvO := hball hv
      refine ⟨hOt hvO, ?_⟩
      by_contra hB
      have : v ∈ O' := ⟨hvO, hOt hvO, hB⟩
      rw [h] at this
      exact this
    exact (Metric.measure_ball_pos volume u hr).ne' (measure_mono_null hsub (D_null R j))
  obtain ⟨y, hy⟩ := exists_infinite_fibre hO' hne' (han.mono inter_subset_left)
    (fun u hu => hdet u hu.1)
  refine (resFib_finite R hP hW Ψ hΨ y).not_infinite ((Set.Infinite.image
    ((R.atlas.chart j).symm.injOn.mono fun u hu => hOt hu.1.1) hy).mono ?_)
  rintro _ ⟨u, ⟨huO, hqu⟩, rfl⟩
  exact ⟨hqu, huO.2.2, h0 u huO.1⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel.ResBridge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Topology Filter Set

namespace ResBridge

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)

theorem ram_null {P : Ideal (MRing ι)} (hP : IsArithVar P (e + 1))
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (hΨ : IsGoodProj P Ψ) (j : Fin R.atlas.n) :
    volume ((R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' {x | Ψ (segre (R.pt x)) 0 ≠ 0 ∧
      ∃ k, x ∈ (R.atlas.chart k).source ∧
        LinearMap.det (fderiv ℂ (resProj R Ψ ∘ (R.atlas.chart k).symm) (R.atlas.chart k x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0}) = 0 := by
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, h00, -⟩
  set x0 := (R.atlas.chart j).symm u0
  set V := (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x0) with hVdef
  have hV : IsOpen V := (R.atlas.chart j).isOpen_inter_preimage_symm (R.R.isOpen_alt_bis _)
  have hgc : ContinuousOn (fun u => Ψ (segre (R.liftAt x0 ((R.atlas.chart j).symm u))) 0) V :=
    fun u hu => (analyticAt_pi_iff.mp (analyticAt_segre_liftAt R Ψ x0 j hu) 0).continuousAt.continuousWithinAt
  set O := V ∩ (fun u => Ψ (segre (R.liftAt x0 ((R.atlas.chart j).symm u))) 0) ⁻¹' {0}ᶜ with hOdef
  have hO : IsOpen O := hgc.isOpen_inter_preimage hV isOpen_compl_singleton
  have hu0O : u0 ∈ O := ⟨⟨hu0, R.mem_src_idx x0⟩, h00⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO u0 hu0O
  have h0 : ∀ u ∈ Metric.ball u0 r, Ψ (segre (R.pt ((R.atlas.chart j).symm u))) 0 ≠ 0 := by
    intro u hu
    obtain ⟨μ, hμ, hμeq⟩ := psi_pt_eq R (hball hu).1.2 Ψ
    rw [hμeq, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hμ (hball hu).2
  have hQa : AnalyticOnNhd ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) (Metric.ball u0 r) := by
    intro u hu
    have := analyticAt_resProj R Ψ _ j ((R.atlas.chart j).map_target (hball hu).1.1) (h0 u hu)
    rwa [(R.atlas.chart j).right_inv (hball hu).1.1] at this
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, fun u => LinearMap.det
      (fderiv ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)),
    fun u hu => analyticAt_det_fderiv (hQa u hu), ?_, ?_⟩
  · by_contra hall
    push Not at hall
    exact not_flat R hP hW Ψ hΨ j Metric.isOpen_ball (fun u hu => (hball hu).1.1)
      ⟨u0, Metric.mem_ball_self hr⟩ h0 hQa hall
  · rintro w ⟨⟨hwt, hw0, k, hk, hdk⟩, -⟩
    have := det_resProj_chart R Ψ (j := j) ((R.atlas.chart j).map_target hwt) hk hw0
    rw [(R.atlas.chart j).right_inv hwt] at this
    show LinearMap.det (fderiv ℂ (resProj R Ψ ∘ (R.atlas.chart j).symm) w :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0
    rw [this, hdk, zero_mul]

theorem psi0_null {P : Ideal (MRing ι)} (hP : IsArithVar P (e + 1))
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (hΨ : IsGoodProj P Ψ) (j : Fin R.atlas.n) :
    volume ((R.atlas.chart j).target ∩
      (R.atlas.chart j).symm ⁻¹' {x | Ψ (segre (R.pt x)) 0 = 0}) = 0 := by
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, -⟩
  set x0 := (R.atlas.chart j).symm u0
  set V := (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x0) with hVdef
  have hV : IsOpen V := (R.atlas.chart j).isOpen_inter_preimage_symm (R.R.isOpen_alt_bis _)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV u0 ⟨hu0, R.mem_src_idx x0⟩
  set f : (Fin e → ℂ) → ℂ := fun u => Ψ (segre (R.liftAt x0 ((R.atlas.chart j).symm u))) 0 with hfdef
  have hfa : AnalyticOnNhd ℂ f V := fun u hu =>
    analyticAt_pi_iff.mp (analyticAt_segre_liftAt R Ψ x0 j hu) 0
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, f, hfa.mono hball, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    have hgood := hΨ _ (pt_mem_mcPts R hW x0)
    obtain ⟨i0, hi0⟩ : ∃ i0, Ψ (segre (R.liftAt x0 x0)) i0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hgood (funext h)
    have hi0ne : i0 ≠ 0 := by
      rintro rfl
      exact hi0 (hall u0 (Metric.mem_ball_self hr))
    set m : Fin e := i0.pred hi0ne
    have hm : m.succ = i0 := Fin.succ_pred i0 hi0ne
    set Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) :=
      (LinearMap.funLeft ℂ ℂ (Equiv.swap (0 : Fin (e + 1)) i0)).comp Ψ with hΨ'def
    have hΨ'app : ∀ w i, Ψ' w i = Ψ w (Equiv.swap 0 i0 i) := fun w i => rfl
    have hΨ' : IsGoodProj P Ψ' := by
      intro z hz h
      refine hΨ z hz (funext fun i => ?_)
      have := congrFun h (Equiv.swap 0 i0 i)
      rw [hΨ'app, Equiv.swap_apply_self] at this
      exact this
    have hg'c : ContinuousOn (fun u => Ψ' (segre (R.liftAt x0 ((R.atlas.chart j).symm u))) 0)
        (Metric.ball u0 r) := fun u hu =>
      (analyticAt_pi_iff.mp (analyticAt_segre_liftAt R Ψ' x0 j (hball hu)) 0).continuousAt.continuousWithinAt
    set O := Metric.ball u0 r ∩
      (fun u => Ψ' (segre (R.liftAt x0 ((R.atlas.chart j).symm u))) 0) ⁻¹' {0}ᶜ with hOdef
    have hO : IsOpen O := hg'c.isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton
    have hu0O : u0 ∈ O := by
      refine ⟨Metric.mem_ball_self hr, ?_⟩
      show Ψ' (segre (R.liftAt x0 x0)) 0 ≠ 0
      rw [hΨ'app, Equiv.swap_apply_left]
      exact hi0
    have h0O : ∀ u ∈ O, Ψ' (segre (R.pt ((R.atlas.chart j).symm u))) 0 ≠ 0 := by
      intro u hu
      obtain ⟨μ, hμ, hμeq⟩ := psi_pt_eq R (hball hu.1).2 Ψ'
      rw [hμeq, Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero hμ hu.2
    have hanO : AnalyticOnNhd ℂ (resProj R Ψ' ∘ (R.atlas.chart j).symm) O := by
      intro u hu
      have := analyticAt_resProj R Ψ' _ j ((R.atlas.chart j).map_target (hball hu.1).1) (h0O u hu)
      rwa [(R.atlas.chart j).right_inv (hball hu.1).1] at this
    have hzero : ∀ u ∈ O, (resProj R Ψ' ∘ (R.atlas.chart j).symm) u m = 0 := by
      intro u hu
      simp only [Function.comp_apply, resProj]
      rw [hm, hΨ'app, Equiv.swap_apply_right]
      obtain ⟨μ, hμ, hμeq⟩ := psi_pt_eq R (hball hu.1).2 Ψ
      rw [hμeq, Pi.smul_apply, smul_eq_mul]
      have : f u = 0 := hall u hu.1
      simp only [hfdef] at this
      rw [this, mul_zero, zero_div]
    have hdetO : ∀ u ∈ O, LinearMap.det (fderiv ℂ (resProj R Ψ' ∘ (R.atlas.chart j).symm) u :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0 := by
      intro u hu
      have hcoord : (fun v => (resProj R Ψ' ∘ (R.atlas.chart j).symm) v m) =ᶠ[𝓝 u] fun _ => 0 := by
        filter_upwards [hO.mem_nhds hu] with v hv
        exact hzero v hv
      have hd : HasFDerivAt (fun v => (resProj R Ψ' ∘ (R.atlas.chart j).symm) v m)
          ((ContinuousLinearMap.proj m).comp (fderiv ℂ (resProj R Ψ' ∘ (R.atlas.chart j).symm) u)) u :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) m).hasFDerivAt.comp u
          (hanO u hu).differentiableAt.hasFDerivAt
      have hd0 : HasFDerivAt (fun v => (resProj R Ψ' ∘ (R.atlas.chart j).symm) v m)
          (0 : (Fin e → ℂ) →L[ℂ] ℂ) u :=
        (hasFDerivAt_const (0 : ℂ) u).congr_of_eventuallyEq hcoord
      have hrow := hd.unique hd0
      refine det_eq_zero_of_coord m fun v => ?_
      have := congrArg (fun T : (Fin e → ℂ) →L[ℂ] ℂ => T v) hrow
      simpa using this
    exact not_flat R hP hW Ψ' hΨ' j hO (fun u hu => (hball hu.1).1) ⟨u0, hu0O⟩ h0O hanO hdetO
  · rintro w ⟨⟨hwt, hw0⟩, hwb⟩
    obtain ⟨μ, hμ, hμeq⟩ := psi_pt_eq R (hball hwb).2 Ψ
    have := congrFun hμeq 0
    rw [Pi.smul_apply, smul_eq_mul] at this
    have hw0' : Ψ (segre (R.pt ((R.atlas.chart j).symm w))) 0 = 0 := hw0
    rw [hw0'] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hμ

end ResBridge

theorem ComponentResBadNull.proof : ComponentResBadNull.Statement := by
  intro K _ _ ι _ P e W R Ψ hP hW hΨ j
  refine measure_mono_null ?_ (measure_union_null (measure_union_null (ResBridge.D_null R j)
    (ResBridge.psi0_null R hP hW Ψ hΨ j)) (ResBridge.ram_null R hP hW Ψ hΨ j))
  rintro u ⟨hu, hbad⟩
  rcases hbad with (hD | h0) | ⟨k, hk, hnot⟩
  · exact Or.inl (Or.inl ⟨hu, hD⟩)
  · exact Or.inl (Or.inr ⟨hu, h0⟩)
  · by_cases h0 : Ψ (segre (R.pt ((R.atlas.chart j).symm u))) 0 = 0
    · exact Or.inl (Or.inr ⟨hu, h0⟩)
    · refine Or.inr ⟨hu, h0, k, hk, ?_⟩
      by_contra hdet
      exact hnot ⟨ResBridge.analyticAt_resProj R Ψ _ k hk h0, hdet⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end
