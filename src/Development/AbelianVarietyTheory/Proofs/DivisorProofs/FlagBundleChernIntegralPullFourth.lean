import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLinePullbackForm
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StereographicMeasureChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MobiusChangeOfVariables
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FsOne
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableProdPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleAffinePolynomialCoordsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernRealClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointsMapHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormOneAddMulSmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasPullbackEqChartExpression
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormPullbackHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityPullbackEqNormSqDetMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDensityExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCellFrameOfSpans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprEqZeroOfCardNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSubOfIsForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleCurvatureAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalDensityBoundNearPoint

section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_hermitian_line_pullback_form : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    Measurable v := by
  first | exact @GlobalTheory.CosSqMeas.measurable_cosSq | exact GlobalTheory.CosSqMeas.measurable_cosSq | (intros; apply GlobalTheory.CosSqMeas.measurable_cosSq <;> assumption)
end

section
open MeasureTheory
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stereographic_measure_change : ∀ g : ℝ → ℝ≥0∞, Measurable g →
    ∫⁻ x : ℂ, g (1 / (1 + ‖x‖ ^ 2)) * ENNReal.ofReal (1 / (Real.pi * (1 + ‖x‖ ^ 2) ^ 2)) =
      ∫⁻ t in Set.Ioo (0:ℝ) 1, g t := by
  first | exact @GlobalTheory.FibLine.lintegral_comp_fsDens | exact GlobalTheory.FibLine.lintegral_comp_fsDens | (intros; apply GlobalTheory.FibLine.lintegral_comp_fsDens <;> assumption)
end

section
open MeasureTheory
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mobius_change_of_variables : ∀ (β c : ℂ), c ≠ 0 → ∀ H : ℂ → ℝ≥0∞, Measurable H →
    ∫⁻ x : ℂ, ENNReal.ofReal (‖c / (1 + β * x) ^ 2‖ ^ 2) * H (c * x / (1 + β * x)) = ∫⁻ y : ℂ, H y := by
  first | exact @GlobalTheory.FibLine.MoebiusLintegral.lintegral_moebius | exact GlobalTheory.FibLine.MoebiusLintegral.lintegral_moebius | (intros; apply GlobalTheory.FibLine.MoebiusLintegral.lintegral_moebius <;> assumption)
end

section
section
open MeasureTheory
open scoped ComplexOrder ENNReal

set_option autoImplicit false

namespace GlobalTheory.FibCos

theorem cos_fs_moebius (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.PosDef) (x : ℂ)
    (hx : 1 + G 1 0 / G 0 0 * x ≠ 0) :
    GlobalTheory.FibCos.cos G x = 1 / (1 + ‖(Real.sqrt G.det.re / (G 0 0).re : ℂ) * x / (1 + G 1 0 / G 0 0 * x)‖ ^ 2) ∧
    GlobalTheory.FibCos.fs G x = ‖(Real.sqrt G.det.re / (G 0 0).re : ℂ) / (1 + G 1 0 / G 0 0 * x) ^ 2‖ ^ 2 *
      (1 / (Real.pi * (1 + ‖(Real.sqrt G.det.re / (G 0 0).re : ℂ) * x / (1 + G 1 0 / G 0 0 * x)‖ ^ 2) ^ 2)) := by
  have h00 : (0 : ℂ) < G 0 0 := hG.diag_pos
  have hdet : (0 : ℂ) < G.det := hG.det_pos
  obtain ⟨ha, ha'⟩ := Complex.pos_iff.mp h00
  obtain ⟨hD, -⟩ := Complex.pos_iff.mp hdet
  have h01 : G 0 1 = (starRingEnd ℂ) (G 1 0) := (hG.isHermitian.apply 0 1).symm
  set a : ℝ := (G 0 0).re with ha_def
  set D : ℝ := G.det.re with hD_def
  have hGa : G 0 0 = (a : ℂ) := by
    apply Complex.ext
    · simp [ha_def]
    · simp [← ha']
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  set u : ℝ := ‖1 + G 1 0 / G 0 0 * x‖ ^ 2 with hu_def
  set s : ℝ := ‖x‖ ^ 2 with hs_def
  have hu : 0 < u := by positivity
  have hs : 0 ≤ s := by positivity
  have hnum : ‖G 0 0 + x * G 1 0‖ ^ 2 = a ^ 2 * u := by
    have : G 0 0 + x * G 1 0 = (a : ℂ) * (1 + G 1 0 / G 0 0 * x) := by
      rw [hGa]; field_simp
    rw [this, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hDe : D = a * (G 1 1).re - ((G 1 0).re ^ 2 + (G 1 0).im ^ 2) := by
    rw [hD_def, Matrix.det_fin_two, h01, hGa]
    simp
    ring
  have hn : nrm G x = a * u + D / a * s := by
    have h1 : a * nrm G x = a ^ 2 * u + D * s := by
      rw [← hnum, hDe, hs_def, nrm, h01, hGa]
      simp only [Complex.sq_norm, Complex.normSq_apply]
      simp
      ring
    field_simp
    linarith
  have hc : ‖(Real.sqrt D / a : ℂ)‖ ^ 2 = D / a ^ 2 := by
    rw [norm_div, div_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
      sq_abs, Real.sq_sqrt hD.le]
  have hy : ‖(Real.sqrt D / a : ℂ) * x / (1 + G 1 0 / G 0 0 * x)‖ ^ 2 = D / a ^ 2 * s / u := by
    rw [norm_div, norm_mul, div_pow, mul_pow, hc]
  have hd : ‖(Real.sqrt D / a : ℂ) / (1 + G 1 0 / G 0 0 * x) ^ 2‖ ^ 2 = D / a ^ 2 / u ^ 2 := by
    rw [norm_div, norm_pow, div_pow, hc]
  have hpi := Real.pi_pos
  rw [hy, hd]
  constructor
  · rw [cos, hnum, hn, ← ha_def]
    field_simp
  · rw [fs, hn, ← hD_def]
    field_simp

end GlobalTheory.FibCos
end

open MeasureTheory
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_cosine_explicit_formula : ∀ (G : Matrix (Fin 2) (Fin 2) ℂ), G.PosDef → ∀ x : ℂ, 1 + G 1 0 / G 0 0 * x ≠ 0 →
    GlobalTheory.FibCos.cos G x = 1 / (1 + ‖(Real.sqrt G.det.re / (G 0 0).re : ℂ) * x / (1 + G 1 0 / G 0 0 * x)‖ ^ 2) ∧
    GlobalTheory.FibCos.fs G x = ‖(Real.sqrt G.det.re / (G 0 0).re : ℂ) / (1 + G 1 0 / G 0 0 * x) ^ 2‖ ^ 2 *
      (1 / (Real.pi * (1 + ‖(Real.sqrt G.det.re / (G 0 0).re : ℂ) * x / (1 + G 1 0 / G 0 0 * x)‖ ^ 2) ^ 2)) := by
  atlas_forward_decl GlobalTheory.FibCos.cos_fs_moebius
end

section
section
open MeasureTheory
open scoped ComplexOrder ENNReal

set_option autoImplicit false

namespace GlobalTheory.FibCos

theorem lintegral_indicator_cos_mul_fs (G : Matrix (Fin 2) (Fin 2) ℂ) (hG : G.PosDef) (J : Set ℝ)
    (hJ : MeasurableSet J) :
    ∫⁻ x : ℂ, J.indicator (fun _ => (1 : ENNReal)) (cos G x) * ENNReal.ofReal (fs G x) =
      volume (J ∩ Set.Icc (0 : ℝ) 1) := by
  set β : ℂ := G 1 0 / G 0 0
  set c : ℂ := (Real.sqrt G.det.re / (G 0 0).re : ℂ)
  have hdet : 0 < G.det.re := (Complex.pos_iff.1 hG.det_pos).1
  have ha : 0 < (G 0 0).re := (Complex.pos_iff.1 (hG.diag_pos (i := 0))).1
  have hc : c ≠ 0 := by
    simp only [c]
    exact_mod_cast (div_pos (Real.sqrt_pos.2 hdet) ha).ne'
  set g : ℝ → ℝ≥0∞ := J.indicator (fun _ => (1 : ENNReal))
  have hg : Measurable g := measurable_one.indicator hJ
  set H : ℂ → ℝ≥0∞ := fun y => g (1 / (1 + ‖y‖ ^ 2)) * ENNReal.ofReal (1 / (Real.pi * (1 + ‖y‖ ^ 2) ^ 2))
  have hH : Measurable H := by
    simp only [H]
    fun_prop
  have hnull : volume {x : ℂ | 1 + β * x = 0} = 0 := by
    apply Set.Subsingleton.measure_zero
    intro u hu v hv
    simp only [Set.mem_setOf_eq] at hu hv
    have hb : β ≠ 0 := by rintro hb; simp [hb] at hu
    have : β * u = β * v := by linear_combination hu - hv
    exact mul_left_cancel₀ hb this
  have hae : (fun x : ℂ => g (cos G x) * ENNReal.ofReal (fs G x)) =ᵐ[volume]
      fun x => ENNReal.ofReal (‖c / (1 + β * x) ^ 2‖ ^ 2) * H (c * x / (1 + β * x)) := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun x hx => ?_) hnull
    simp only [Set.mem_setOf_eq] at hx ⊢
    by_contra hne
    apply hx
    obtain ⟨h1, h2⟩ := GlobalTheory.T.fibre_cosine_explicit_formula G hG x hne
    simp only [H]
    rw [h1, h2, ENNReal.ofReal_mul (by positivity)]
    ring
  rw [lintegral_congr_ae hae, GlobalTheory.T.mobius_change_of_variables β c hc H hH, GlobalTheory.T.stereographic_measure_change g hg,
    lintegral_indicator_const hJ, one_mul, Measure.restrict_apply hJ]
  exact measure_congr (Filter.EventuallyEq.inter (Filter.EventuallyEq.refl _ _) Ioo_ae_eq_Icc)

end GlobalTheory.FibCos
end

open MeasureTheory
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_cosine_pushforward_uniform : ∀ (G : Matrix (Fin 2) (Fin 2) ℂ), G.PosDef → ∀ J : Set ℝ, MeasurableSet J →
    ∫⁻ x : ℂ, J.indicator (fun _ => (1 : ENNReal)) (GlobalTheory.FibCos.cos G x) * ENNReal.ofReal (GlobalTheory.FibCos.fs G x) =
      volume (J ∩ Set.Icc (0 : ℝ) 1) := by
  atlas_forward_decl GlobalTheory.FibCos.lintegral_indicator_cos_mul_fs
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

noncomputable section

namespace GlobalTheory.MixDensNull

theorem part_over_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (D : ℕ), IsArithVar p D → ∀ (Z : Set X), IsClosed Z → genericPoint X ∉ Z → ∀ (σ : k →+* ℂ) (ρ : AlgChart p σ D → CxPts p σ → ℝ), part ρ {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} = 0 := by
  intro k _ X p _ D h Z hZ hgen σ ρ
  have hA : MeasurableSet {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} := by
    have : {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} =
        (ptsIn p σ ⟨Zᶜ, hZ.isOpen_compl⟩)ᶜ := by
      ext y
      simp [mem_ptsIn]
    rw [this]
    exact (isOpen_ptsIn _).measurableSet.compl
  exact GlueCoverNull.glueMeas_null _ _ hA fun c => GlobalTheory.ChernNull.chart_null h hZ hgen σ c

end GlobalTheory.MixDensNull
end
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical ENNReal

namespace GlobalTheory.MixDens

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
  {w ρ : AlgChart p σ D → CxPts p σ → ℝ}

theorem IsDens.setLIntegral_part [SecondCountableTopology (CxPts p σ)] (h : IsDens w)
    (c : AlgChart p σ D) {A : Set (CxPts p σ)} (hA : MeasurableSet A) (hc : A ⊆ c.e.source)
    {f : CxPts p σ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y in A, f y ∂(part w) =
      ∫⁻ v in c.e '' A, ENNReal.ofReal (w c (c.e.symm v)) * f (c.e.symm v) := by
  have hS := ChartGlue.measurableSet_image c.e hA hc
  have hSt : c.e '' A ⊆ c.e.target := (Set.image_mono hc).trans c.e.image_source_eq_target.subset
  have hsym : AEMeasurable c.e.symm (volume.restrict (c.e '' A)) :=
    (c.e.continuousOn_symm.mono hSt).aemeasurable hS
  have hφ : AEMeasurable (fun v => ENNReal.ofReal (w c (c.e.symm v)))
      (volume.restrict (c.e '' A)) :=
    (((h.2 c).mono hSt).aemeasurable hS).ennreal_ofReal
  have hsym' := hsym.mono_ac (withDensity_absolutelyContinuous (volume.restrict (c.e '' A))
    fun v => ENNReal.ofReal (w c (c.e.symm v)))
  have key : (part w).restrict A = Measure.map c.e.symm
      ((volume.restrict (c.e '' A)).withDensity fun v => ENNReal.ofReal (w c (c.e.symm v))) := by
    ext B hB
    rw [Measure.restrict_apply hB, h.part_apply c (hB.inter hA) (Set.inter_subset_right.trans hc),
      Measure.map_apply_of_aemeasurable hsym' hB, withDensity_apply',
      Measure.restrict_restrict' hS]
    congr 2
    ext v
    constructor
    · rintro ⟨y, ⟨hyB, hyA⟩, rfl⟩
      exact ⟨by rwa [Set.mem_preimage, c.e.left_inv (hc hyA)], ⟨y, hyA, rfl⟩⟩
    · rintro ⟨hv, ⟨y, hyA, rfl⟩⟩
      rw [Set.mem_preimage, c.e.left_inv (hc hyA)] at hv
      exact ⟨y, ⟨hv, hyA⟩, rfl⟩
  rw [key, lintegral_map' hf.aemeasurable hsym']
  exact lintegral_withDensity_eq_lintegral_mul₀ hφ (hf.comp_aemeasurable hsym)

theorem IsDens.isFiniteMeasure_part [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)]
    [SecondCountableTopology (CxPts p σ)] (h : IsDens w)
    (cov : ∀ y, ∃ c : AlgChart p σ D, y ∈ c.e.source) : IsFiniteMeasure (part w) := by
  have hfin : ∀ y, (part w).FiniteAtFilter (𝓝 y) := fun y => by
    obtain ⟨c, hy⟩ := cov y
    obtain ⟨ε, hε, hεt⟩ := Metric.isOpen_iff.1 c.e.open_target _ (c.e.map_source hy)
    set B := Metric.closedBall (c.e y) (ε / 2) with hBdef
    have hBt : B ⊆ c.e.target := (Metric.closedBall_subset_ball (by linarith)).trans hεt
    set T := c.e.symm '' B with hTdef
    have hTc : IsCompact T :=
      (isCompact_closedBall _ _).image_of_continuousOn (c.e.continuousOn_symm.mono hBt)
    have hTs : T ⊆ c.e.source := by
      rintro _ ⟨v, hv, rfl⟩; exact c.e.map_target (hBt hv)
    have hTB : c.e '' T = B := by
      rw [hTdef, Set.image_image]
      exact (Set.image_congr fun v hv => c.e.right_inv (hBt hv)).trans (Set.image_id' B)
    refine ⟨T, ?_, ?_⟩
    · refine mem_of_superset ((c.e.isOpen_inter_preimage Metric.isOpen_ball).mem_nhds
        ⟨hy, Metric.mem_ball_self (half_pos hε)⟩) fun z hz => ⟨c.e z, ?_, c.e.left_inv hz.1⟩
      exact Metric.ball_subset_closedBall hz.2
    · rw [h.part_apply c hTc.isClosed.measurableSet hTs, hTB]
      exact (((h.2 c).mono hBt).integrableOn_compact (isCompact_closedBall _ _)).lintegral_lt_top
  refine ⟨?_⟩
  simpa using isCompact_univ.measure_lt_top_of_nhdsWithin fun y _ =>
    (hfin y).filter_mono nhdsWithin_le_nhds

theorem IsDens.exists_quotient (hw : IsDens w) (hpos : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, 0 < w c y)
    (cov : ∀ y, ∃ c : AlgChart p σ D, y ∈ c.e.source) (hρ : IsDens ρ) :
    ∃ g : CxPts p σ → ℝ, Continuous g ∧ ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source,
      ρ c y = g y * w c y := by
  choose pick hpick using cov
  have hval : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source,
      ρ c y = ρ (pick y) y / w (pick y) y * w c y := fun c y hy => by
    have hne := (hpos (pick y) y (hpick y)).ne'
    rw [hρ.1 c (pick y) y hy (hpick y), hw.1 c (pick y) y hy (hpick y)]
    field_simp
  refine ⟨fun y => ρ (pick y) y / w (pick y) y, continuous_iff_continuousAt.2 fun y => ?_, hval⟩
  have hcont : ∀ τ : AlgChart p σ D → CxPts p σ → ℝ, IsDens τ →
      ContinuousOn (τ (pick y)) (pick y).e.source := fun τ hτ =>
    ((hτ.2 (pick y)).comp (pick y).e.continuousOn (pick y).e.mapsTo).congr fun z hz => by
      simp [(pick y).e.left_inv hz]
  have ho := (pick y).e.open_source.mem_nhds (hpick y)
  refine (((hcont ρ hρ).continuousAt ho).div ((hcont w hw).continuousAt ho)
    (hpos _ y (hpick y)).ne').congr ?_
  filter_upwards [ho] with z hz
  rw [Pi.div_apply, hval (pick y) z hz, mul_div_assoc, div_self (hpos _ z hz).ne', mul_one]

theorem IsDens.part_eq_withDensity [SecondCountableTopology (CxPts p σ)] (hw : IsDens w)
    (hpos : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, 0 < w c y)
    (cov : ∀ y, ∃ c : AlgChart p σ D, y ∈ c.e.source) {g : CxPts p σ → ℝ} (hg : Continuous g)
    (hρ : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, ρ c y = g y * w c y) :
    part ρ = (part w).withDensity fun y => ENNReal.ofReal (g y) := by
  have hd : IsDens ρ := (hw.mul hg).congr hρ
  refine ChartGlue.ext_of_cover (fun c : AlgChart p σ D => c.e.source) (fun c => c.e.open_source)
    cov fun c A hA hc => ?_
  rw [hd.part_apply c hA hc, withDensity_apply _ hA,
    hw.setLIntegral_part c hA hc hg.measurable.ennreal_ofReal]
  refine setLIntegral_congr_fun (ChartGlue.measurableSet_image c.e hA hc) ?_
  rintro _ ⟨y, hy, rfl⟩
  simp only [c.e.left_inv (hc hy)]
  rw [hρ c y (hc hy), ENNReal.ofReal_mul' (hpos c y (hc hy)).le, mul_comm]

theorem IsDens.total_eq_integral [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)]
    [SecondCountableTopology (CxPts p σ)] (hw : IsDens w)
    (hpos : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, 0 < w c y)
    (cov : ∀ y, ∃ c : AlgChart p σ D, y ∈ c.e.source) {g : CxPts p σ → ℝ} (hg : Continuous g)
    (hρ : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, ρ c y = g y * w c y) :
    total ρ = ∫ y, g y ∂(part w) := by
  haveI := hw.isFiniteMeasure_part cov
  have hI : Integrable g (part w) :=
    integrableOn_univ.1 (hg.continuousOn.integrableOn_compact isCompact_univ)
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hI, total,
    hw.part_eq_withDensity hpos cov hg hρ,
    hw.part_eq_withDensity (ρ := fun c y => -ρ c y) (g := fun y => -g y) hpos cov hg.neg
      fun c y hy => by rw [hρ c y hy, neg_mul],
    withDensity_apply _ MeasurableSet.univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]

theorem exists_isDens_pos [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)]
    (hR : Nonempty (AnRead p σ D)) : ∃ w : AlgChart p σ D → CxPts p σ → ℝ,
      IsDens w ∧ ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, 0 < w c y := by
  obtain ⟨R⟩ := hR
  obtain ⟨s, hs⟩ := R.exists_finite
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate (X := CxPts p σ) (ι := s) isClosed_univ
    (fun i => (R.chart i.1).e.source) (fun i => (R.chart i.1).e.open_source)
    (fun y _ => by
      obtain ⟨i, hi, hy⟩ := hs y
      exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hy⟩)
  have hsrc : ∀ (i : s) (y : CxPts p σ), f i y ≠ 0 → y ∈ (R.chart i.1).e.source := fun i y h =>
    hf i (subset_tsupport _ h)
  refine ⟨fun c y => ∑ i : s, f i y * ‖ChartGlue.transDet c.e (R.chart i.1).e y‖ ^ 2,
    ⟨fun c c' y hy hy' => ?_, fun c => ?_⟩, fun c y hy => ?_⟩
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : f i y = 0
    · simp [h]
    · rw [CurveDens.transDet_trans_chart c c' _ hy hy' (hsrc i y h), norm_mul, mul_pow]
      ring
  · refine continuousOn_finset_sum _ fun i _ => ?_
    have hg : ContinuousOn (fun y => f i y * ‖ChartGlue.transDet c.e (R.chart i.1).e y‖ ^ 2)
        c.e.source := fun y hy => by
      refine ContinuousAt.continuousWithinAt ?_
      by_cases h : y ∈ tsupport (f i)
      · exact (f i).continuous.continuousAt.mul
          ((CurveDens.continuousAt_transDet_chart c _ hy (hf i h)).norm.pow 2)
      · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 h] with z hz
        rw [hz, Pi.zero_apply, zero_mul]
    exact hg.comp c.e.continuousOn_symm fun v hv => c.e.map_target hv
  · obtain ⟨i, hi⟩ := f.exists_pos (Set.mem_univ y)
    refine Finset.sum_pos' (fun j _ => mul_nonneg (f.nonneg j y) (sq_nonneg _))
      ⟨i, Finset.mem_univ _, mul_pos hi (pow_pos (norm_pos_iff.2 ?_) 2)⟩
    exact CurveDens.transDet_chart_ne_zero c _ hy (hsrc i y hi.ne')

theorem exists_refMeasure : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)], Nonempty (AnRead p σ D) → ∃ (ν : Measure (CxPts p σ)) (w : AlgChart p σ D → CxPts p σ → ℝ), IsFiniteMeasure ν ∧ ν = part w ∧ IsDens w ∧ (∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, 0 < w c y) ∧ (∀ ρ : AlgChart p σ D → CxPts p σ → ℝ, IsDens ρ → ∃ g : CxPts p σ → ℝ, Continuous g ∧ ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, ρ c y = g y * w c y) ∧ ∀ (ρ : AlgChart p σ D → CxPts p σ → ℝ) (g : CxPts p σ → ℝ), Continuous g → (∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, ρ c y = g y * w c y) → part ρ = ν.withDensity (fun y => ENNReal.ofReal (g y)) ∧ total ρ = ∫ y, g y ∂ν := by
  intro k _ X p σ D _ _ _ hR
  obtain ⟨w, hw, hpos⟩ := exists_isDens_pos hR
  obtain ⟨R⟩ := hR
  have cov : ∀ y, ∃ c : AlgChart p σ D, y ∈ c.e.source := fun y =>
    let ⟨i, hi⟩ := R.cover y
    ⟨R.chart i, hi⟩
  exact ⟨part w, w, hw.isFiniteMeasure_part cov, rfl, hw, hpos,
    fun ρ hρ => hw.exists_quotient hpos cov hρ, fun ρ g hg hρ =>
      ⟨hw.part_eq_withDensity hpos cov hg hρ, hw.total_eq_integral hpos cov hg hρ⟩⟩

end GlobalTheory.MixDens
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

namespace GlobalTheory.MixDens

theorem part_univ_ne_top {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    {ρ : AlgChart p σ D → CxPts p σ → ℝ} (hp : IsProjOver p) (a : Nonempty (AnRead p σ D)) (h : IsDens ρ) :
    part ρ Set.univ ≠ ⊤ := by
  haveI := CxPts.compactSpace σ hp
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ hp
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hp
  obtain ⟨ν, w, hν, -, -, -, h1, h2⟩ := GlobalTheory.MixDens.exists_refMeasure k X p σ D a
  obtain ⟨g, hg, hgw⟩ := h1 ρ h
  rw [(h2 ρ g hg hgw).1, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hi : Integrable g ν := hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  exact hi.lintegral_lt_top.ne

theorem part_compl_ptsIn {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} [IsIntegral X] {σ : k →+* ℂ} {D : ℕ}
    (hp : IsArithVar p D) (ρ : AlgChart p σ D → CxPts p σ → ℝ) (c : AlgChart p σ D) (hc : c.e.source.Nonempty) :
    part ρ (ptsIn p σ c.U)ᶜ = 0 := by
  have hmem : ∀ y : CxPts p σ, y ∈ ptsIn p σ c.U ↔ y.1 (IsLocalRing.closedPoint ℂ) ∈ c.U := by
    intro y
    constructor
    · intro hy
      exact hy (Set.mem_univ (IsLocalRing.closedPoint ℂ))
    · intro hy x _
      have : x = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
      subst this
      exact hy
  obtain ⟨y, hy⟩ := hc
  have hU : (c.U : Set X).Nonempty := ⟨_, (hmem y).1 (c.source_subset hy)⟩
  have hgen : genericPoint X ∉ (c.U : Set X)ᶜ := by
    intro h
    exact h (((genericPoint_spec X).mem_open_set_iff c.U.isOpen).2 (by simpa using hU))
  have := GlobalTheory.MixDensNull.part_over_closed k X p D hp (c.U : Set X)ᶜ c.U.isOpen.isClosed_compl hgen σ ρ
  refine measure_mono_null (fun x hx => ?_) this
  exact fun h => hx ((hmem x).2 h)

theorem measurePreserving_uncurry {ι : Type} [Fintype ι] {κ : ι → Type} [∀ a, Fintype (κ a)] :
    MeasurePreserving (MeasurableEquiv.piCurry fun a (_ : κ a) => ℂ).symm volume volume := by
  refine ⟨(MeasurableEquiv.piCurry _).symm.measurable, ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (MeasurableEquiv.piCurry _).symm.measurable (MeasurableSet.univ_pi hs)]
  have e : (MeasurableEquiv.piCurry fun a (_ : κ a) => ℂ).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi fun a => Set.univ.pi fun j => s ⟨a, j⟩ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Sigma.forall, MeasurableEquiv.coe_piCurry_symm]
    rfl
  rw [e, volume_pi_pi, Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun a _ => volume_pi_pi _

theorem measurePreserving_elim {τ : Type} [Fintype τ] :
    MeasurePreserving (fun (x : ℂ × (τ → ℂ)) (j : Option τ) => j.elim x.1 x.2) volume volume := by
  have hm : Measurable (fun (x : ℂ × (τ → ℂ)) (j : Option τ) => j.elim x.1 x.2) := by
    refine measurable_pi_lambda _ fun j => ?_
    cases j with
    | none => exact measurable_fst
    | some j => exact (measurable_pi_apply j).comp measurable_snd
  refine ⟨hm, ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have e : (fun (x : ℂ × (τ → ℂ)) (j : Option τ) => j.elim x.1 x.2) ⁻¹' Set.univ.pi s =
      s none ×ˢ Set.univ.pi fun j => s (some j) := by
    ext x
    simp [Option.forall]
  rw [e, Measure.volume_eq_prod, Measure.prod_prod, volume_pi_pi, Fintype.prod_option]

theorem measurePreserving_pt {ι : Type} [Fintype ι] {r : ι → ℕ} {d : ℕ}
    (e : Fin (d + 1) ≃ Option (Σ a, Low (r a))) :
    MeasurePreserving (fun x : V 1 × (∀ a, Low (r a) → ℂ) => pt e x.1 x.2) volume volume := by
  have h1 : MeasurePreserving (fun z : V 1 => z 0) volume volume :=
    (volume_preserving_funUnique (Fin 1) ℂ).comp (volume_preserving_ofLp_complex (Fin 1))
  have h2 := h1.prod (measurePreserving_uncurry (κ := fun a => Low (r a)))
  have h3 := (measurePreserving_elim (τ := Σ a, Low (r a))).comp h2
  have h4 := (volume_preserving_arrowCongr' e.symm (MeasurableEquiv.refl ℂ) (MeasurePreserving.id volume)).comp h3
  have h5 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℂ)) volume volume :=
    MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℂ)).symm
      (volume_preserving_ofLp_complex (Fin (d + 1)))
  have h6 := h5.comp h4
  exact h6

theorem continuous_base {ι : Type} {r : ι → ℕ} {d : ℕ} (e : Fin (d + 1) ≃ Option (Σ a, Low (r a))) :
    Continuous (base e) := by
  unfold base
  refine (PiLp.continuous_toLp 2 _).comp ?_
  exact (continuous_single (A := fun _ : Fin 1 => ℂ) 0).comp (by fun_prop)

theorem setIntegral_base {ι : Type} [Fintype ι] {r : ι → ℕ} {d : ℕ}
    (e : Fin (d + 1) ≃ Option (Σ a, Low (r a))) {F : V (d + 1) → ℝ} {G : V 1 → ℝ} {K : Set (V 1)}
    (hK : MeasurableSet K) (hF : IntegrableOn F (base e ⁻¹' K))
    (hG : ∀ z ∈ K, ∫ n : ∀ a, Low (r a) → ℂ, F (pt e z n) = G z) :
    ∫ v in base e ⁻¹' K, F v = ∫ z in K, G z := by
  have hm := (measurePreserving_pt e).restrict_preimage ((continuous_base e).measurable hK)
  have hs : (fun x : V 1 × (∀ a, Low (r a) → ℂ) => pt e x.1 x.2) ⁻¹' (base e ⁻¹' K) = K ×ˢ Set.univ := by
    ext x
    simp [base_pt]
  rw [hs] at hm
  have hi := hm.integrable_comp_of_integrable hF
  rw [← hm.map_eq, integral_map hm.measurable.aemeasurable (by rw [hm.map_eq]; exact hF.aestronglyMeasurable)]
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [setIntegral_prod (fun x : V 1 × (∀ a, Low (r a) → ℂ) => F (pt e x.1 x.2)) hi]
  refine setIntegral_congr_fun hK fun z hz => ?_
  simp only [Measure.restrict_univ]
  exact hG z hz

theorem integrable_of_parts {α : Type} [MeasurableSpace α] {μ : Measure α} {F : α → ℝ}
    (hF : AEStronglyMeasurable F μ) (h₁ : ∫⁻ v, ENNReal.ofReal (F v) ∂μ ≠ ⊤)
    (h₂ : ∫⁻ v, ENNReal.ofReal (-F v) ∂μ ≠ ⊤) : Integrable F μ := by
  refine ⟨hF, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc ∫⁻ v, ENNReal.ofReal ‖F v‖ ∂μ ≤ ∫⁻ v, (ENNReal.ofReal (F v) + ENNReal.ofReal (-F v)) ∂μ := by
        refine lintegral_mono fun v => ?_
        rcases abs_choice (F v) with h | h <;> rw [Real.norm_eq_abs, h]
        · exact le_self_add
        · exact le_add_self
    _ = ∫⁻ v, ENNReal.ofReal (F v) ∂μ + ∫⁻ v, ENNReal.ofReal (-F v) ∂μ :=
        lintegral_add_left' hF.aemeasurable.ennreal_ofReal _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨h₁.lt_top, h₂.lt_top⟩

section Cell

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {π : Y ⟶ B} {w : π ≫ q = p}
  {ι : Type} [Fintype ι] {r : ι → ℕ} {d : ℕ} {e : Fin (d + 1) ≃ Option (Σ a, Low (r a))} {σ : k →+* ℂ}
  {c : AlgChart q σ 1} {c' : AlgChart p σ (d + 1)}

omit [Fintype ι] in

theorem IsCell.image_eq (h : IsCell e π w c c') {A : Set (CxPts q σ)} (hA : A ⊆ c.e.source) :
    c'.e '' (PtsOver.map π w (spMap σ) ⁻¹' A ∩ c'.e.source) = base e ⁻¹' (c.e '' A) := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  ext v
  constructor
  · rintro ⟨y, ⟨hy, hy'⟩, rfl⟩
    exact ⟨_, hy, (h₃ y hy').symm⟩
  · rintro ⟨a, ha, hv⟩
    have hvt : v ∈ c'.e.target := by
      rw [h₂]
      change base e v ∈ c.e.target
      rw [← hv]
      exact c.e.map_source (hA ha)
    have hy := c'.e.map_target hvt
    refine ⟨c'.e.symm v, ⟨?_, hy⟩, c'.e.right_inv hvt⟩
    have h₄ := h₃ _ hy
    rw [c'.e.right_inv hvt, ← hv] at h₄
    have h₅ : PtsOver.map π w (spMap σ) (c'.e.symm v) ∈ c.e.source := (h₁ ▸ hy).1
    have := c.e.injOn (hA ha) h₅ h₄
    change PtsOver.map π w (spMap σ) (c'.e.symm v) ∈ A
    rw [← this]
    exact ha

omit [Fintype ι] in

theorem IsCell.part_preimage [IsIntegral Y] [SecondCountableTopology (CxPts p σ)] (h : IsCell e π w c c')
    (hp : IsArithVar p (d + 1)) {ρ : AlgChart p σ (d + 1) → CxPts p σ → ℝ} (hρ : IsDens ρ)
    {A : Set (CxPts q σ)} (hAm : MeasurableSet A) (hA : A ⊆ c.e.source) :
    part ρ (PtsOver.map π w (spMap σ) ⁻¹' A) =
      ∫⁻ v in base e ⁻¹' (c.e '' A), ENNReal.ofReal (ρ c' (c'.e.symm v)) := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  have hne : c'.e.source.Nonempty := by
    refine ⟨c'.e.symm (pt e (c.e a) 0), c'.e.map_target ?_⟩
    rw [h.2.1]
    change base e _ ∈ c.e.target
    rw [base_pt]
    exact c.e.map_source (hA ha)
  have hm : MeasurableSet (PtsOver.map π w (spMap σ) ⁻¹' A) :=
    (PtsOver.continuous_map π w (spMap σ)).measurable hAm
  rw [← h.image_eq hA, ← hρ.part_apply c' (hm.inter c'.e.open_source.measurableSet) Set.inter_subset_right,
    ← measure_inter_add_sdiff _ c'.e.open_source.measurableSet]
  have h0 : part ρ (PtsOver.map π w (spMap σ) ⁻¹' A \ c'.e.source) = 0 := by
    refine measure_mono_null (fun y hy => ?_) (part_compl_ptsIn hp ρ c' hne)
    intro hU
    refine hy.2 ?_
    rw [h.1]
    exact ⟨hA hy.1, hU⟩
  rw [h0, add_zero]

theorem IsCell.part_add_part [IsIntegral Y] [SecondCountableTopology (CxPts q σ)] [SecondCountableTopology (CxPts p σ)]
    (h : IsCell e π w c c') (hp : IsArithVar p (d + 1)) {ρ : AlgChart p σ (d + 1) → CxPts p σ → ℝ}
    {g : AlgChart q σ 1 → CxPts q σ → ℝ} (hρ : IsDens ρ) (hg : IsDens g) (f₁ : part ρ Set.univ ≠ ⊤)
    (f₂ : part (fun c y => -ρ c y) Set.univ ≠ ⊤) (f₃ : part g Set.univ ≠ ⊤)
    (f₄ : part (fun c y => -g c y) Set.univ ≠ ⊤)
    (hfib : ∀ z ∈ c.e.target, ∫ n : ∀ a, Low (r a) → ℂ, ρ c' (c'.e.symm (pt e z n)) = g c (c.e.symm z))
    {A : Set (CxPts q σ)} (hAm : MeasurableSet A) (hA : A ⊆ c.e.source) :
    part ρ (PtsOver.map π w (spMap σ) ⁻¹' A) + part (fun c y => -g c y) A =
      part (fun c y => -ρ c y) (PtsOver.map π w (spMap σ) ⁻¹' A) + part g A := by
  have hρ' : IsDens fun c y => -ρ c y := (isDens_zero.sub hρ).congr fun c y _ => by simp
  have hg' : IsDens fun c y => -g c y := (isDens_zero.sub hg).congr fun c y _ => by simp
  have g₁ := ne_top_of_le_ne_top f₁ (measure_mono (Set.subset_univ (PtsOver.map π w (spMap σ) ⁻¹' A)))
  have g₂ := ne_top_of_le_ne_top f₂ (measure_mono (Set.subset_univ (PtsOver.map π w (spMap σ) ⁻¹' A)))
  have g₃ := ne_top_of_le_ne_top f₃ (measure_mono (Set.subset_univ A))
  have g₄ := ne_top_of_le_ne_top f₄ (measure_mono (Set.subset_univ A))
  rw [h.part_preimage hp hρ hAm hA] at g₁ ⊢
  rw [h.part_preimage hp hρ' hAm hA] at g₂ ⊢
  rw [hg.part_apply c hAm hA] at g₃ ⊢
  rw [hg'.part_apply c hAm hA] at g₄ ⊢
  have hK : MeasurableSet (c.e '' A) := ChartGlue.measurableSet_image c.e hAm hA
  have hKt : c.e '' A ⊆ c.e.target := by
    rintro _ ⟨a, ha, rfl⟩
    exact c.e.map_source (hA ha)
  have hT : base e ⁻¹' (c.e '' A) ⊆ c'.e.target := by
    rw [h.2.1]
    exact fun v hv => hKt hv
  have i₁ := integrable_of_parts
    (((hρ.2 c').mono hT).aestronglyMeasurable ((continuous_base e).measurable hK)) g₁ g₂
  have i₂ := integrable_of_parts (((hg.2 c).mono hKt).aestronglyMeasurable hK) g₃ g₄
  have key := setIntegral_base e hK i₁ fun z hz => hfib z (hKt hz)
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part i₁,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part i₂] at key
  rw [← ENNReal.toReal_eq_toReal_iff' (ENNReal.add_ne_top.2 ⟨g₁, g₄⟩) (ENNReal.add_ne_top.2 ⟨g₂, g₃⟩),
    ENNReal.toReal_add g₁ g₄, ENNReal.toReal_add g₂ g₃]
  linarith

end Cell

theorem total_eq_of_cells : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (r : ι → ℕ) (d : ℕ) (e : Fin (d + 1) ≃ Option (Σ a, Low (r a))) (σ : k →+* ℂ) [IsIntegral Y], IsArithVar q 1 → IsArithVar p (d + 1) → Nonempty (AnRead q σ 1) → Nonempty (AnRead p σ (d + 1)) → ∀ (ρ : AlgChart p σ (d + 1) → CxPts p σ → ℝ) (g : AlgChart q σ 1 → CxPts q σ → ℝ), IsDens ρ → IsDens g → (∀ y : CxPts q σ, ∃ (c : AlgChart q σ 1) (c' : AlgChart p σ (d + 1)), y ∈ c.e.source ∧ IsCell e π w c c' ∧ ∀ z ∈ c.e.target, ∫ n : ∀ a, Low (r a) → ℂ, ρ c' (c'.e.symm (pt e z n)) = g c (c.e.symm z)) → total ρ = total g := by
  intro k _ B Y q p π w ι _ r d e σ _ hq hp aq ap ρ g hρ hg hcov
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hq.isProjOver
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hp.isProjOver
  have hρ' : IsDens fun c y => -ρ c y := (isDens_zero.sub hρ).congr fun c y _ => by simp
  have hg' : IsDens fun c y => -g c y := (isDens_zero.sub hg).congr fun c y _ => by simp
  have f1 := part_univ_ne_top hp.isProjOver ap hρ
  have f2 := part_univ_ne_top hp.isProjOver ap hρ'
  have f3 := part_univ_ne_top hq.isProjOver aq hg
  have f4 := part_univ_ne_top hq.isProjOver aq hg'
  set Φ := PtsOver.map π w (spMap σ) with hΦ
  have hΦm : Measurable Φ := (PtsOver.continuous_map π w (spMap σ)).measurable
  have key : (part ρ).map Φ + part (fun c y => -g c y) = (part (fun c y => -ρ c y)).map Φ + part g := by
    refine ChartGlue.ext_of_cover (fun y => (hcov y).choose.e.source) (fun y => (hcov y).choose.e.open_source)
      (fun y => ⟨y, (hcov y).choose_spec.choose_spec.1⟩) fun y A hA hAy => ?_
    obtain ⟨c', -, hcell, hfib⟩ := (hcov y).choose_spec
    rw [Measure.add_apply, Measure.add_apply, Measure.map_apply hΦm hA, Measure.map_apply hΦm hA]
    exact hcell.part_add_part hp hρ hg f1 f2 f3 f4 hfib hA hAy
  have hu := congrArg (fun μ => μ Set.univ) key
  simp only [Measure.add_apply, Measure.map_apply hΦm MeasurableSet.univ, Set.preimage_univ] at hu
  have := congrArg ENNReal.toReal hu
  rw [ENNReal.toReal_add f1 f4, ENNReal.toReal_add f2 f3] at this
  simp only [total]
  linarith

end GlobalTheory.MixDens
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open GlobalTheory.Points
open scoped Classical ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FibLoc

open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.FibTriv (prodPt basePt)
open scoped ENNReal ComplexConjugate

theorem pull_prod {n m : ℕ} (L : V n →L[ℂ] V m) {ι : Type} (s : Finset ι) (f : ι → Ev m) (g : ι → Ev n)
    (h : ∀ a, pull L (f a : Alt m) = g a) : pull L ((∏ a ∈ s, f a : Ev m) : Alt m) = (∏ a ∈ s, g a : Ev n) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Subalgebra.coe_mul, Subalgebra.coe_mul, map_mul, h, ih]

theorem sym_mul_sym {n : ℕ} {a b c : Fin n} (h : a = c ∨ b = c) : (sym (a, b) * sym (c, c) : Ev n) = 0 := by
  refine Subtype.ext ?_
  rcases h with rfl | rfl
  · have := Subalgebra.mem_center_iff.1 (sym (a, b)).2 (dz a)
    change (sym (a, b) : Alt n) * (dz a * dzb a) = 0
    rw [← mul_assoc, ← this]
    change dz a * (dz a * dzb b) * dzb a = 0
    rw [← mul_assoc, dz, ExteriorAlgebra.ι_sq_zero, zero_mul, zero_mul]
  · have := Subalgebra.mem_center_iff.1 (sym (b, b)).2 (dzb b)
    change dz a * dzb b * (sym (b, b) : Alt n) = 0
    rw [mul_assoc, this]
    change dz a * (dz b * dzb b * dzb b) = 0
    rw [mul_assoc, dzb, ExteriorAlgebra.ι_sq_zero, mul_zero, mul_zero]

variable {d : ℕ} (L : V (d + 1) →L[ℂ] V d) (hL : ∀ v a, L v a = v a.castSucc)

include hL in

theorem pull_vol : pull L (vol d : Alt d) =
    (∏ a : Fin d, (Complex.I / 2) • sym (a.castSucc, a.castSucc) : Ev (d + 1)) := by
  refine pull_prod L _ _ _ fun a => ?_
  have e (b : Fin (d + 1)) : L (coordVec b) a = if b = a.castSucc then 1 else 0 := by
    rw [hL]; simp [coordVec, EuclideanSpace.single_apply, eq_comm]
  rw [Subalgebra.coe_smul, Subalgebra.coe_smul, map_smul]
  congr 1
  change pull L (dz a * dzb a) = dz _ * dzb _
  rw [map_mul, (pull_dz L a).1, (pull_dz L a).2]
  simp [e, apply_ite]

theorem dens_sym_mul_pull (x : Fin (d + 1) × Fin (d + 1)) (β : Alt d) :
    dens ((sym x : Alt (d + 1)) * pull L β) = dens ((sym x : Alt (d + 1)) * pull L (vol d : Alt d)) * dens β := by
  obtain ⟨c, hc, e⟩ := vol_eq d
  have hv : (bas d).repr (vol d : Alt d) Finset.univ = c := by simp [e]
  conv_lhs => rw [← (bas d).sum_repr β]
  rw [map_sum, Finset.mul_sum, dens, map_sum, Finsupp.finset_sum_apply, Finset.sum_eq_single Finset.univ _ (by simp)]
  · simp only [dens, hv, e, map_smul, mul_smul_comm, Finsupp.smul_apply, smul_eq_mul, Module.Basis.repr_self,
      Finsupp.single_eq_same]
    field_simp
  · intro S _ hS
    have hc : S.card < d + d := by simpa using Finset.card_lt_card (Finset.ssubset_univ_iff.2 hS)
    have hm : pull L (bas d S) ∈ ⋀[ℂ]^S.card (Fin (d + 1) ⊕ Fin (d + 1) → ℂ) := by
      rw [bas, ExteriorAlgebra.basis_apply, pull, ExteriorAlgebra.map_apply_ιMulti, ← exteriorPower.ιMulti_apply_coe]
      exact Subtype.prop _
    have hm' : (sym x : Alt (d + 1)) * pull L (bas d S) ∈ ⋀[ℂ]^(S.card + 1 + 1) (Fin (d + 1) ⊕ Fin (d + 1) → ℂ) := by
      change dz _ * dzb _ * _ ∈ LinearMap.range _ ^ _
      rw [pow_succ', pow_succ', mul_assoc]
      exact Submodule.mul_mem_mul ⟨_, rfl⟩ (Submodule.mul_mem_mul ⟨_, rfl⟩ hm)
    have h0 : (bas (d + 1)).repr ((sym x : Alt (d + 1)) * pull L (bas d S)) Finset.univ = 0 :=
      exterior_repr_univ_of_mem _ (by omega) hm'
    rw [map_smul, mul_smul_comm, map_smul, Finsupp.smul_apply, h0, smul_zero]

include hL in

theorem dens_ofValues_mul_pull (α : V (d + 1) → V (d + 1) → ℂ) (β : Alt d) :
    dens ((ofValues α : Alt (d + 1)) * pull L β) =
      2 / Complex.I * α (coordVec (Fin.last d)) (coordVec (Fin.last d)) * dens β := by
  have key (a b : Fin (d + 1)) : dens ((sym (a, b) : Alt (d + 1)) * pull L (vol d : Alt d)) =
      if a = Fin.last d ∧ b = Fin.last d then 2 / Complex.I else 0 := by
    rw [pull_vol L hL, ← Subalgebra.coe_mul]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      have : (sym (Fin.last d, Fin.last d) * ∏ a : Fin d, (Complex.I / 2) • sym (a.castSucc, a.castSucc) : Ev (d + 1)) =
          (2 / Complex.I) • vol (d + 1) := by
        rw [vol, Fin.prod_univ_castSucc, mul_smul_comm, smul_smul, mul_comm (sym _)]
        field_simp
        simp
      rw [this, Subalgebra.coe_smul]
      have := dens_vol (d + 1)
      simp only [dens, map_smul, Finsupp.smul_apply, smul_eq_mul] at this ⊢
      rw [mul_div_assoc, this, mul_one]
    · obtain ⟨c, hc⟩ : ∃ c : Fin d, a = c.castSucc ∨ b = c.castSucc := by
        by_cases ha : a = Fin.last d
        · obtain ⟨c, rfl⟩ := Fin.exists_castSucc_eq.2 fun hb : b = Fin.last d => h ⟨ha, hb⟩
          exact ⟨c, .inr rfl⟩
        · obtain ⟨c, rfl⟩ := Fin.exists_castSucc_eq.2 ha
          exact ⟨c, .inl rfl⟩
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c), ← mul_assoc, mul_smul_comm, sym_mul_sym hc]
      simp [dens]
  have hs (a b : Fin (d + 1)) (t : ℂ) : dens (t • ((sym (a, b) : Alt (d + 1)) * pull L β)) =
      t * ((if a = Fin.last d ∧ b = Fin.last d then 2 / Complex.I else 0) * dens β) := by
    rw [← key, ← dens_sym_mul_pull]
    simp only [dens, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_div_assoc]
  have hsum {ι : Type} (s : Finset ι) (f : ι → Alt (d + 1)) : dens (∑ i ∈ s, f i) = ∑ i ∈ s, dens (f i) := by
    simp only [dens, map_sum, Finsupp.finset_sum_apply, Finset.sum_div]
  simp only [ofValues, AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul, Finset.sum_mul, smul_mul_assoc, hsum, hs,
    ite_and]
  simp
  ring

theorem nrm_eq {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) (x : ℂ) :
    FibCos.nrm G x = (‖x + G 0 1 / G 1 1‖ ^ 2 + G.det.re / (G 1 1).re ^ 2) * (G 1 1).re := by
  have h1 := Complex.pos_iff.1 (hG.diag_pos (i := 1))
  have h0 := Complex.pos_iff.1 (hG.diag_pos (i := 0))
  have h10 : G 1 0 = conj (G 0 1) := (hG.1.apply 1 0).symm
  have e1 : G 1 1 = ((G 1 1).re : ℂ) := Complex.ext (by simp) (by simp [← h1.2])
  have e0 : G 0 0 = ((G 0 0).re : ℂ) := Complex.ext (by simp) (by simp [← h0.2])
  have hne : (G 1 1).re ≠ 0 := h1.1.ne'
  rw [FibCos.nrm, Matrix.det_fin_two, h10, e1, e0]
  generalize (G 1 1).re = s at *
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.sub_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  field_simp
  ring

theorem nrm_pos {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) (x : ℂ) : 0 < FibCos.nrm G x := by
  have h1 : 0 < (G 1 1).re := (Complex.pos_iff.1 (hG.diag_pos (i := 1))).1
  have hd : 0 < G.det.re := (Complex.pos_iff.1 hG.det_pos).1
  rw [nrm_eq hG]
  positivity

theorem leviForm_log_nrm {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) (x : ℂ) :
    leviForm (fun x => Real.log (FibCos.nrm G x)) x 1 1 = ((G.det.re / FibCos.nrm G x ^ 2 : ℝ) : ℂ) := by
  have h1 : 0 < (G 1 1).re := (Complex.pos_iff.1 (hG.diag_pos (i := 1))).1
  have hd : 0 < G.det.re := (Complex.pos_iff.1 hG.det_pos).1
  have hp (x : ℂ) : 0 < ‖x + G 0 1 / G 1 1‖ ^ 2 + G.det.re / (G 1 1).re ^ 2 := by positivity
  have hφ : ContDiffAt ℂ 2 (fun x : ℂ => x + G 0 1 / G 1 1) x := by fun_prop
  have e : (fun x => Real.log (FibCos.nrm G x)) = fun x =>
      Real.log (‖x + G 0 1 / G 1 1‖ ^ 2 + G.det.re / (G 1 1).re ^ 2) + Real.log (G 1 1).re :=
    funext fun x => by rw [nrm_eq hG, Real.log_mul (hp x).ne' h1.ne']
  have hf : fderiv ℂ (fun x : ℂ => x + G 0 1 / G 1 1) x 1 = 1 := by simp
  rw [e, leviForm_add_const _ (contDiffAt_log_normSq_add_comp hφ (hp x).ne'),
    leviForm_log_normSq_add_comp hφ (hp x).ne', hf, nrm_eq hG]
  have := (hp x).ne'
  generalize x + G 0 1 / G 1 1 = z at *
  have h' : ((‖z‖ ^ 2 + G.det.re / (G 1 1).re ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast this
  simp only [inner, Complex.star_def, map_one, one_mul, mul_one, Complex.conj_mul']
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_div, ← Complex.ofReal_div,
    ← Complex.ofReal_sub]
  congr 1
  field_simp
  ring

theorem measurePreserving_prodPt (d : ℕ) :
    MeasurePreserving (fun z : V d × ℂ => prodPt z.1 z.2) volume volume := by
  have h1 : MeasurePreserving (fun z : V d × ℂ => (z.2, z.1.ofLp)) volume volume :=
    (Measure.measurePreserving_swap (μ := (volume : Measure (Fin d → ℂ))) (ν := (volume : Measure ℂ))).comp
      ((volume_preserving_ofLp_complex (Fin d)).prod (MeasurePreserving.id volume))
  have h2 := (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℂ) (Fin.last d)).symm
  have h5 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℂ)) volume volume :=
    MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin (d + 1) → ℂ)).symm
      (volume_preserving_ofLp_complex (Fin (d + 1)))
  convert h5.comp (h2.comp h1) using 1
  funext z
  simp [prodPt, MeasurableEquiv.piFinSuccAbove, Fin.insertNth_last', Fin.snocEquiv]

theorem chartMeas_prod {X Y : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {d : ℕ} (e : OpenPartialHomeomorph X (V d))
    (e' : OpenPartialHomeomorph Y (V (d + 1))) (f : Y → X) (hs : ∀ y ∈ e'.source, f y ∈ e.source)
    (ht : e'.target = basePt ⁻¹' e.target) (hb : ∀ y ∈ e'.source, basePt (e' y) = e (f y))
    (ρ : X → ℝ≥0∞) (hρ : AEMeasurable (ρ ∘ e.symm) (volume.restrict e.target)) (ρ' : Y → ℝ≥0∞)
    (K : X → ℂ → ℝ≥0∞) (hK : Measurable (Function.uncurry K)) {T : Set Y}
    (h : ∀ y ∈ e'.source, T.indicator ρ' y = K (f y) (e' y (Fin.last d)) * ρ (f y))
    {S : Set X} (hS : MeasurableSet S) (hSe : S ⊆ e.source) (hT : MeasurableSet (f ⁻¹' S ∩ T))
    (hT' : MeasurableSet (e'.source ∩ T)) :
    ChartGlue.chartMeas e' ρ' (f ⁻¹' S ∩ T) = ∫⁻ b in S, (∫⁻ x, K b x) ∂ChartGlue.chartMeas e ρ := by
  have hK' : Measurable fun b => ∫⁻ x, K b x := hK.lintegral_prod_right
  have hIm := ChartGlue.measurableSet_image e hS hSe
  have hIt : e '' S ⊆ e.target := by rintro _ ⟨b, hb, rfl⟩; exact e.map_source (hSe hb)
  have hsy : AEMeasurable e.symm (volume.restrict e.target) :=
    e.continuousOn_symm.aemeasurable e.open_target.measurableSet
  have hbc : Continuous (basePt (d := d)) := FibTriv.differentiable_basePt.continuous
  have hR : ∫⁻ b in S, (∫⁻ x, K b x) ∂ChartGlue.chartMeas e ρ =
      ∫⁻ z in e '' S, (∫⁻ x, K (e.symm z) x) * ρ (e.symm z) := by
    rw [← lintegral_indicator hS, ChartGlue.chartMeas, lintegral_map' (hK'.indicator hS).aemeasurable
      (hsy.mono_ac (withDensity_absolutelyContinuous _ _)),
      lintegral_withDensity_eq_lintegral_mul₀ (g := fun z => S.indicator (fun b => ∫⁻ x, K b x) (e.symm z)) hρ
        ((hK'.indicator hS).comp_aemeasurable hsy),
      ← inter_eq_left.2 hIt, ← Measure.restrict_restrict hIm, ← lintegral_indicator hIm]
    refine setLIntegral_congr_fun e.open_target.measurableSet fun z hz => ?_
    by_cases hz' : z ∈ e '' S
    · have : e.symm z ∈ S := by
        obtain ⟨b, hb, rfl⟩ := hz'
        rwa [e.left_inv (hSe hb)]
      simp [hz', this, mul_comm]
    · have : e.symm z ∉ S := fun h => hz' ⟨_, h, e.right_inv hz⟩
      simp [hz', this]
  have hA : e' '' (e'.source ∩ (f ⁻¹' S ∩ T)) = e' '' (e'.source ∩ T) ∩ basePt ⁻¹' (e '' S) := by
    ext v
    constructor
    · rintro ⟨y, ⟨hy, h₁, h₂⟩, rfl⟩
      exact ⟨⟨y, ⟨hy, h₂⟩, rfl⟩, _, h₁, (hb y hy).symm⟩
    · rintro ⟨⟨y, ⟨hy, h₂⟩, rfl⟩, b, h₁, h₃⟩
      refine ⟨y, ⟨hy, ?_, h₂⟩, rfl⟩
      rw [hb y hy] at h₃
      rwa [mem_preimage, ← e.injOn (hSe h₁) (hs y hy) h₃]
  have hm := (measurePreserving_prodPt d).restrict_preimage (hbc.measurable hIm)
  have hp : (fun z : V d × ℂ => prodPt z.1 z.2) ⁻¹' (basePt ⁻¹' (e '' S)) = (e '' S) ×ˢ univ := by
    ext z; simp
  have hemb : MeasurableEmbedding fun z : V d × ℂ => prodPt z.1 z.2 :=
    (Homeomorph.measurableEmbedding ⟨⟨fun z => prodPt z.1 z.2, fun v => (basePt v, v (Fin.last d)), fun z => by simp,
      fun v => by simp⟩, FibTriv.differentiable_prodPt.continuous, hbc.prodMk (by fun_prop)⟩ :)
  have hTm := ChartGlue.measurableSet_image e' hT' inter_subset_left
  have h₁ : AEMeasurable e.symm (volume.restrict (e '' S)) := hsy.mono_measure (Measure.restrict_mono hIt le_rfl)
  have h₂ : AEMeasurable (ρ ∘ e.symm) (volume.restrict (e '' S)) := hρ.mono_measure (Measure.restrict_mono hIt le_rfl)
  rw [hR, ChartGlue.chartMeas_apply _ _ hT, hA, ← Measure.restrict_restrict hTm, ← lintegral_indicator hTm,
    setLIntegral_congr_fun (hbc.measurable hIm)
      (g := fun v => K (e.symm (basePt v)) (v (Fin.last d)) * ρ (e.symm (basePt v))) (fun v hv => ?_),
    ← hm.lintegral_comp_emb hemb, hp, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  · simp only [FibTriv.basePt_prodPt, FibTriv.prodPt_last]
    rw [lintegral_prod (fun a : V d × ℂ => K (e.symm a.1) a.2 * ρ (e.symm a.1))
      ((hK.comp_aemeasurable (h₁.comp_fst.prodMk measurable_snd.aemeasurable)).mul h₂.comp_fst)]
    refine lintegral_congr fun z => ?_
    dsimp only
    exact lintegral_mul_const (f := K (e.symm z)) _ (hK.comp measurable_prodMk_left)
  · have hv' : v ∈ e'.target := ht ▸ hIt hv
    have hy := e'.map_target hv'
    have := h _ hy
    rw [← e.left_inv (hs _ hy), ← hb _ hy, e'.right_inv hv'] at this
    beta_reduce
    rw [← this]
    by_cases hT : e'.symm v ∈ T
    · rw [indicator_of_mem hT, indicator_of_mem (show v ∈ e' '' (e'.source ∩ T) from ⟨_, ⟨hy, hT⟩, e'.right_inv hv'⟩)]
    · rw [indicator_of_notMem hT, indicator_of_notMem]
      rintro ⟨y, ⟨h₁, h₂⟩, rfl⟩
      exact hT (by rwa [e'.left_inv h₁])

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

theorem etale_snoc {k A R N : Type} [CommRing k] [CommRing A] [CommRing R] [Unique N] (α : k →+* A) {d : ℕ}
    (t : Fin d → A) (f : A →+* R) (n : N → R) (hg : (eval₂Hom α t).Etale) (hΦ : Function.Bijective (eval₂Hom f n)) :
    (eval₂Hom (f.comp α) (Fin.snoc (α := fun _ => R) (fun j => f (t j)) (n default))).Etale := by
  let ι : MvPolynomial (Fin (d + 1)) k →+* MvPolynomial N (MvPolynomial (Fin d) k) :=
    eval₂Hom (C.comp C) (Fin.snoc (α := fun _ => MvPolynomial N (MvPolynomial (Fin d) k)) (fun j => C (X j)) (X default))
  let κ : MvPolynomial N (MvPolynomial (Fin d) k) →+* MvPolynomial (Fin (d + 1)) k :=
    eval₂Hom (eval₂Hom C fun j => X j.castSucc) fun _ => X (Fin.last d)
  have h1 : κ.comp ι = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [ι, κ]
    · intro j
      induction j using Fin.lastCases <;> simp [ι, κ]
  have h2 : ι.comp κ = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro r; simp [ι, κ]
      · intro j; simp [ι, κ]
    · intro j
      obtain rfl : j = default := Subsingleton.elim _ _
      simp [ι, κ]
  have hι : Function.Bijective ι :=
    Function.bijective_iff_has_inverse.2 ⟨κ, fun x => DFunLike.congr_fun h1 x, fun x => DFunLike.congr_fun h2 x⟩
  have key : eval₂Hom (f.comp α) (Fin.snoc (α := fun _ => R) (fun j => f (t j)) (n default)) =
      (eval₂Hom f n).comp ((MvPolynomial.map (eval₂Hom α t)).comp ι) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [ι]
    · intro j
      induction j using Fin.lastCases <;> simp [ι]
  rw [key]
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective hι) (etale_mvPolynomial_map_of_etale _ hg))
    (RingHom.Etale.of_bijective hΦ)

theorem exists_chart_le {k : Type} [CommRing k] {B : Scheme.{0}} {q : B ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}
    (c₀ : AlgChart q σ d) {y : CxPts q σ} (hy : y ∈ c₀.e.source) {U : B.Opens} (hU : y ∈ ptsIn q σ U) :
    ∃ c : AlgChart q σ d, y ∈ c.e.source ∧ c.U ≤ U := by
  have hy0 : y ∈ ptsIn q σ c₀.U := c₀.source_subset hy
  obtain ⟨f, hfV, hf⟩ := c₀.affine.exists_basicOpen_le (V := U) ⟨_, mem_ptsIn.1 hU⟩ (mem_ptsIn.1 hy0)
  have hle : B.basicOpen f ≤ c₀.U := B.basicOpen_le f
  have hE : (eval₂Hom (algX q (B.basicOpen f)) (fun a => resG B hle (c₀.x a))).Etale := by
    have e : eval₂Hom (algX q (B.basicOpen f)) (fun a => resG B hle (c₀.x a)) =
        (resG B hle).comp (eval₂Hom (algX q c₀.U) c₀.x) := by
      rw [MvPolynomial.comp_eval₂Hom, GlobalTheory.TopForm.resG_comp_algX]
    rw [e]
    have hR : (resG B hle).Etale := by
      letI : Algebra Γ(B, c₀.U) Γ(B, B.basicOpen f) := (resG B hle).toAlgebra
      haveI : IsLocalization.Away f Γ(B, B.basicOpen f) := c₀.affine.isLocalization_basicOpen f
      exact RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway f)
    exact RingHom.Etale.stableUnderComposition _ _ c₀.etale hR
  obtain ⟨c, hc, hU, -⟩ := AlgChart.exists_of_etale (c₀.affine.basicOpen f) _ hE (mem_ptsIn.2 hf)
  exact ⟨c, hc, hU ▸ hfV⟩

open GlobalTheory.CellChart in

theorem exists_prod_chart {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B)
    (w : π ≫ q = p) {σ : k →+* ℂ} {d : ℕ} (c : AlgChart q σ d) {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ c.U)
    (hWa : IsAffineOpen W) {N : Type} [Unique N] (n : N → Γ(Y, W))
    (hΦ : Function.Bijective (eval₂Hom (π.appLE c.U W hW).hom n)) {b₀ : CxPts q σ} (hb₀ : b₀ ∈ c.e.source) :
    ∃ c' : AlgChart p σ (d + 1), c'.U = W ∧ c'.e.source = PtsOver.map π w (spMap σ) ⁻¹' c.e.source ∩ ptsIn p σ W ∧
      c'.e.target = basePt ⁻¹' c.e.target ∧
      ∀ y, c'.e y = prodPt (c.e (PtsOver.map π w (spMap σ) y)) (ev p σ W (n default) y) := by
  let s : V (d + 1) → CxPts p σ := fun v => if h : basePt v ∈ c.e.target then
    cellPt π w hW hWa n hΦ (c.source_subset (c.e.map_target h)) (fun _ => v (Fin.last d))
    else cellPt π w hW hWa n hΦ (c.source_subset hb₀) 0
  have s_eq {v} (h : basePt v ∈ c.e.target) :
      s v = cellPt π w hW hWa n hΦ (c.source_subset (c.e.map_target h)) (fun _ => v (Fin.last d)) := dif_pos h
  have s_mem {v} (h : basePt v ∈ c.e.target) : s v ∈ ptsIn p σ W := by rw [s_eq h]; exact cellPt_mem ..
  have s_map {v} (h : basePt v ∈ c.e.target) : PtsOver.map π w (spMap σ) (s v) = c.e.symm (basePt v) := by
    rw [s_eq h]; exact map_cellPt _ _ _ _ _ _ c.affine _ _
  have s_n {v} (h : basePt v ∈ c.e.target) (a : N) : ev p σ W (n a) (s v) = v (Fin.last d) := by
    rw [s_eq h]; exact ev_n_cellPt ..
  have hT : IsOpen (basePt ⁻¹' c.e.target) := c.e.open_target.preimage FibTriv.differentiable_basePt.continuous
  have holo (g : Γ(Y, W)) : DifferentiableOn ℂ (ev p σ W g ∘ s) (basePt ⁻¹' c.e.target) := by
    change DifferentiableOn ℂ (fun v => ev p σ W g (s v)) _
    obtain ⟨P, rfl⟩ := hΦ.2 g
    induction P using MvPolynomial.induction_on with
    | C a =>
      refine ((c.holo c.U a).comp FibTriv.differentiable_basePt.differentiableOn fun v hv =>
        ⟨hv, c.source_subset (c.e.map_target hv)⟩).congr fun v hv => ?_
      rw [eval₂Hom_C, ev_appLE π w hW (s_mem hv), s_map hv]
      rfl
    | add P Q hP hQ =>
      simp only [map_add, ev_add]
      exact hP.add hQ
    | mul_X P a hP =>
      have hd : DifferentiableOn ℂ (fun v : V (d + 1) => v (Fin.last d)) (basePt ⁻¹' c.e.target) := by fun_prop
      simp only [map_mul, ev_mul, eval₂Hom_X']
      exact hP.mul (hd.congr fun v hv => s_n hv a)
  have H := holo_of_affine hWa hT (fun v hv => s_mem hv) holo
  let e : OpenPartialHomeomorph (CxPts p σ) (V (d + 1)) :=
    { toFun y := prodPt (c.e (PtsOver.map π w (spMap σ) y)) (ev p σ W (n default) y)
      invFun := s
      source := PtsOver.map π w (spMap σ) ⁻¹' c.e.source ∩ ptsIn p σ W
      target := basePt ⁻¹' c.e.target
      map_source' y hy := by
        rw [mem_preimage, FibTriv.basePt_prodPt]
        exact c.e.map_source hy.1
      map_target' v hv := ⟨by rw [mem_preimage, s_map hv]; exact c.e.map_target hv, s_mem hv⟩
      left_inv' y hy := by
        rw [s_eq (by rw [FibTriv.basePt_prodPt]; exact c.e.map_source hy.1)]
        refine (cellPt_congr π w hW hWa n hΦ _ (map_mem π w hW hy.2) ?_ ?_).trans (cellPt_self π w hW hWa n hΦ hy.2)
        · rw [FibTriv.basePt_prodPt, c.e.left_inv hy.1]
        · funext a
          rw [FibTriv.prodPt_last, Subsingleton.elim a default]
      right_inv' v hv := by rw [s_map hv, c.e.right_inv hv, s_n hv, FibTriv.prodPt_basePt]
      open_source := ((PtsOver.continuous_map π w _).isOpen_preimage _ c.e.open_source).inter (isOpen_ptsIn W)
      open_target := hT
      continuousOn_toFun := FibTriv.differentiable_prodPt.continuous.comp_continuousOn
        ((c.e.continuousOn.comp (PtsOver.continuous_map π w _).continuousOn fun y hy => hy.1).prodMk
          ((continuousOn_ev (n default)).mono inter_subset_right))
      continuousOn_invFun := H.1 }
  refine ⟨⟨e, W, hWa, Fin.snoc (α := fun _ => Γ(Y, W)) (fun j => (π.appLE c.U W hW).hom (c.x j)) (n default), ?_,
    inter_subset_right, fun y hy j => ?_, H.2⟩, rfl, rfl, rfl, fun _ => rfl⟩
  · rw [← algX_eq π w hW]
    exact etale_snoc _ _ _ _ c.etale hΦ
  · change prodPt _ _ j = _
    induction j using Fin.lastCases
    · simp
    · rw [FibTriv.prodPt_castSucc, Fin.snoc_castSucc, c.apply_eq _ hy.1, ev_appLE π w hW hy.2]

theorem part_eq_chartMeas {M : Type} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    {n : ℕ} (A : HolAtlas M n) {α : A.Fld} (hα : A.IsForm α) (ε : ℤˣ) (i : A.ι) {T : Set M} (hT : MeasurableSet T)
    (h : T ⊆ (A.e i).source) : A.part α ε T =
      ChartGlue.chartMeas (A.e i) (fun y => ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α i (A.e i y))).re)) T := by
  refine ChartGlue.glueMeas_apply A.e _ A.holo (fun i j y hi hj => ?_) i hT h
  have e := hα.compat ⟨(i, y), hi⟩ ⟨(j, y), hj⟩ rfl
  rw [← A.loc_crd α ⟨(i, y), hi⟩, ← A.loc_crd α ⟨(j, y), hj⟩] at e
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  refine congrArg ENNReal.ofReal ((congrArg (fun β => ((ε : ℤ) : ℝ) * (dens β).re) e).trans ?_)
  beta_reduce
  rw [dens_pull, Complex.re_ofReal_mul, mul_left_comm]
  rfl

theorem c1F_eq_matForm_hessL {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsRegVar p D) (σ : k →+* ℂ)
    (L : HermLB p) (a : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ a.e.source) (c : L.B.ι) (hc : y ∈ ptsIn p σ (L.B.U c)) :
    c1F hX σ L ⟨(a, y), hy⟩ = ofValues (HermFrame.ddc (fun v => (L.φ σ).φ c (a.e.symm v)) (a.e y)) := by
  set b := pick (L.φ σ).isLB y
  have hb : y ∈ ptsIn p σ (L.B.U b) := mem_pick _ y
  have ho := ChartGlue.isOpen_over a.e (isOpen_ptsIn (p := p) (σ := σ) (L.B.U c ⊓ L.B.U b))
  have hm := ChartGlue.mem_over a.e hy (mem_ptsIn_inf.2 ⟨hc, hb⟩)
  have hf : ContDiffAt ℂ 2 (gv p σ L.B c b ∘ a.e.symm) (a.e y) :=
    (SCV.analyticAt_of_differentiableOn (a.holo _ (L.B.g c b).val) (ho.mem_nhds hm)).contDiffAt
  have h0 : (gv p σ L.B c b ∘ a.e.symm) (a.e y) ≠ 0 := ev_ne_zero hm.2 (L.B.g c b).isUnit
  have hC := (L.cInf σ).contDiffAt a hy hc
  have hlog : ContDiffAt ℝ 2 (fun v => Real.log (‖(gv p σ L.B c b ∘ a.e.symm) v‖ ^ 2)) (a.e y) :=
    ((hf.restrict_scalars ℝ).norm_sq ℂ).log (by simpa using h0)
  have key : leviForm (fun v => (L.φ σ).φ b (a.e.symm v)) (a.e y) =
      leviForm (fun v => (L.φ σ).φ c (a.e.symm v)) (a.e y) := by
    rw [leviForm_congr (u' := fun v => (L.φ σ).φ c (a.e.symm v) +
        -Real.log (‖(gv p σ L.B c b ∘ a.e.symm) v‖ ^ 2)), leviForm_add hC hlog.neg,
      leviForm_neg, leviForm_log_normSq_eq_zero hf h0, neg_zero, add_zero]
    filter_upwards [ho.mem_nhds hm] with v hv
    rw [(L.φ σ).trans c b _ (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2, sub_eq_add_neg]
    rfl
  change ofValues (HermFrame.ddc (fun v => (L.φ σ).φ b (a.e.symm v)) (a.e y)) = _
  unfold HermFrame.ddc
  rw [key]

section Cell

open GlobalTheory.FlagCell GlobalTheory.HermFrame
open GlobalTheory.FlagFibre (Low)
open GlobalTheory.QCoh (pullbackSections)

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B) (w : π ≫ q = p)
  {σ : k →+* ℂ} {E : B.Modules} (cE : Chart E 2) {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ cE.U) (n : Low 2 → Γ(Y, W))

theorem form_vals (h : Met q σ E 2) {y : CxPts p σ} (hy : y ∈ ptsIn p σ W) :
    ((h.pull π w).form (pullCol π cE.e hW (uniR n) 0) (pullCol π cE.e hW (uniR n) 0) y).re =
      FibCos.nrm (h.G cE (PtsOver.map π w (spMap σ) y)) (ev p σ W (n ⟨(1, 0), by decide⟩) y) ∧
    (h.pull π w).form (pullCol π cE.e hW (uniR n) 0) (pullbackSections π E hW (cE.e 0)) y =
      h.G cE (PtsOver.map π w (spMap σ) y) 0 0 +
        ev p σ W (n ⟨(1, 0), by decide⟩) y * h.G cE (PtsOver.map π w (spMap σ) y) 1 0 ∧
    (h.pull π w).form (pullbackSections π E hW (cE.e 0)) (pullbackSections π E hW (cE.e 0)) y =
      h.G cE (PtsOver.map π w (spMap σ) y) 0 0 := by
  have hc : y ∈ ptsIn p σ (π ⁻¹ᵁ cE.U) := mem_ptsIn.2 (hW (mem_ptsIn.1 hy))
  have hc' : PtsOver.map π w (spMap σ) y ∈ ptsIn q σ cE.U := hc
  have k₀ : (cE.pull h.isVB π).crd p σ (pullbackSections π E hW (cE.e 0)) y = ![1, 0] := by
    rw [cE.crd_pull h.isVB π w _ hW hy hc, cE.crd_frame hc']
    funext a
    fin_cases a <;> simp
  have k₁ : (cE.pull h.isVB π).crd p σ (pullCol π cE.e hW (uniR n) 0) y = ![1, ev p σ W (n ⟨(1, 0), by decide⟩) y] := by
    funext a
    simp only [pullCol, Chart.crd_sum, Chart.crd_smul, cE.crd_pull h.isVB π w _ hW hy hc, cE.crd_frame hc',
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    fin_cases a
    · exact (ev_eq hy _).trans (map_one _)
    · rfl
  simp only [(h.pull π w).form_eq (cE.pull h.isVB π) hc _ _ hy, h.pull_G π w cE hc', k₀, k₁]
  refine ⟨congrArg Complex.re ?_, ?_, ?_⟩ <;>
    simp [HermFrame.form, dotProduct, Matrix.mulVec, Fin.sum_univ_two, ← Complex.mul_conj']
  ring

variable {h : VMetric q E 2} (H : h.IsCInf) {fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2}
  (hs : Spans fl W (pullCol π cE.e hW (uniR n)))

include hs in

theorem exists_weight : ∃ c : (VMetric.grLB fl 0 (H.pull π w)).B.ι, (VMetric.grLB fl 0 (H.pull π w)).B.U c = W ∧
    ∀ y ∈ ptsIn p σ W, ((VMetric.grLB fl 0 (H.pull π w)).φ σ).φ c y =
      -Real.log (FibCos.nrm ((h.met σ).G cE (PtsOver.map π w (spMap σ) y)) (ev p σ W (n ⟨(1, 0), by decide⟩) y)) := by
  obtain ⟨s, t, h₁, h₂, h₃⟩ := hs.exists_adaptedChart 0
  let a : VBExt.AdaptedChart (VMetric.stepSeq fl 0) (0 : Fin 2) 1 := ⟨W, s, t, h₁, h₂⟩
  refine ⟨a.quot, rfl, fun y hy => ?_⟩
  have e := Met.quot_G (((h.pull π w).stepMet fl 0).met σ) (VMetric.stepSeq_shortExact fl 0)
    (fl.isVB (Fin.castSucc 0)) (fl.isVB_gr 0) a hy
  rw [← (form_vals π w cE hW n (h.met σ) hy).1]
  refine congrArg (fun z : ℂ => -Real.log z.re) ((congrArg Matrix.det e).trans ((Matrix.det_fin_one _).trans ?_))
  have key (H : Matrix (Fin 0 ⊕ Fin 1) (Fin 0 ⊕ Fin 1) ℂ) : quotGram H 0 0 = H (.inr 0) (.inr 0) := by
    simp [quotGram, Matrix.toBlocks₂₂]
  refine (key _).trans ((Met.form_restrict _ (fl.isSubbundle (Fin.succ 0)) (fl.isVB (Fin.succ 0)) _ _ hy).trans ?_)
  exact congrArg₂ (fun s t => ((h.met σ).pull π w).form s t y) (h₃ (.inr 0)) (h₃ (.inr 0))

include hs in

theorem cosSq_eq {M : B.Modules} (l : M ⟶ E) (m : Γ(M, cE.U)) (hm : l.app cE.U m = cE.e 0) {v : CxPts p σ → ℝ}
    (hv : CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map l) v)
    {y : CxPts p σ} (hy : y ∈ ptsIn p σ W) :
    v y = FibCos.cos ((h.met σ).G cE (PtsOver.map π w (spMap σ) y)) (ev p σ W (n ⟨(1, 0), by decide⟩) y) := by
  obtain ⟨s, -, e⟩ := hs 1
  have hG := (h.met σ).posDef cE (PtsOver.map π w (spMap σ) y) (mem_ptsIn.2 (hW (mem_ptsIn.1 hy)))
  obtain ⟨h₁, h₂, h₃⟩ := form_vals π w cE hW n (h.met σ) hy
  have := hv W (s ⟨0, by decide⟩) (pullbackSections π M hW m) y hy
  rw [QCoh.pullback_map_app_pullbackSections, hm, e, ← Met.conj_form, Complex.norm_conj] at this
  erw [h₁, h₂, h₃] at this
  have h0 : 0 < ((h.met σ).G cE (PtsOver.map π w (spMap σ) y) 0 0).re := (Complex.pos_iff.1 (hG.diag_pos (i := 0))).1
  rw [FibCos.cos, this, eq_div_iff (mul_pos h0 (nrm_pos hG _)).ne']
  ring

end Cell

theorem dens_fibre {d : ℕ} {u : V (d + 1) → ℝ} {v : V (d + 1)} (hu : ContDiffAt ℝ 2 u v)
    {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) (hG' : ∀ x, u (prodPt (basePt v) x) = -Real.log (FibCos.nrm G x))
    (γ β : Alt d) : dens (((ofValues (HermFrame.ddc u v) : Alt (d + 1)) - pull (fderiv ℂ basePt v) γ) *
      pull (fderiv ℂ basePt v) β) = (-FibCos.fs G (v (Fin.last d)) : ℝ) * dens β := by
  let L : V (d + 1) →L[ℂ] V d := LinearMap.toContinuousLinearMap
    { toFun := basePt, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hL : fderiv ℂ basePt v = L := L.fderiv
  let ψ : ℂ → V (d + 1) := fun t => prodPt (basePt v) 0 + t • coordVec (Fin.last d)
  have hψ (t : ℂ) : ψ t = prodPt (basePt v) t := by
    ext a
    induction a using Fin.lastCases <;> simp [ψ, coordVec, EuclideanSpace.single_apply, Fin.castSucc_ne_last]
  have hv : ψ (v (Fin.last d)) = v := by rw [hψ, FibTriv.prodPt_basePt]
  have hd : fderiv ℂ ψ (v (Fin.last d)) 1 = coordVec (Fin.last d) := by
    have : HasFDerivAt ψ _ _ := ((hasFDerivAt_id (𝕜 := ℂ) (v (Fin.last d))).smul_const (coordVec (Fin.last d))).const_add _
    rw [this.fderiv]
    simp
  have hl := leviForm_comp_holo (u := u) (φ := ψ) (z := v (Fin.last d)) (by rwa [hv]) (by fun_prop) 1 1
  simp only [hψ, hG'] at hl
  rw [leviForm_neg, ← hψ, hv, hd, ContinuousLinearMap.neg_apply, ContinuousLinearMap.neg_apply, leviForm_log_nrm hG] at hl
  have h0 : dens (pull L (γ * β)) = 0 := by rw [dens, PullTop.repr_pull_univ, zero_div]
  have hsub (a b : Alt (d + 1)) : dens (a - b) = dens a - dens b := by simp [dens, sub_div]
  rw [hL, sub_mul, ← map_mul, hsub, h0, sub_zero, dens_ofValues_mul_pull L fun _ _ => rfl, HermFrame.ddc, ← hl,
    HermFrame.kappa, FibCos.fs]
  congr 1
  have := (nrm_pos hG (v (Fin.last d))).ne'
  push_cast
  field_simp

theorem measurable_kernel {X : Type} [MeasurableSpace X] {G : X → Matrix (Fin 2) (Fin 2) ℂ}
    (hG : ∀ i j, Measurable fun b => G b i j) {J : Set ℝ} (hJ : MeasurableSet J) :
    Measurable (Function.uncurry fun b x => J.indicator (fun _ => (1 : ℝ≥0∞)) (FibCos.cos (G b) x) *
      ENNReal.ofReal (FibCos.fs (G b) x)) := by
  have h (i j) : Measurable fun z : X × ℂ => G z.1 i j := (hG i j).comp measurable_fst
  have hc : Measurable fun z : X × ℂ => conj z.2 := Complex.continuous_conj.measurable.comp measurable_snd
  have hn : Measurable fun z : X × ℂ => FibCos.nrm (G z.1) z.2 :=
    Complex.measurable_re.comp ((((h 0 0).add (measurable_snd.mul (h 1 0))).add (hc.mul (h 0 1))).add
      ((Complex.measurable_ofReal.comp (measurable_snd.norm.pow_const 2)).mul (h 1 1)))
  have hd : Measurable fun z : X × ℂ => (G z.1).det.re := by
    simp only [Matrix.det_fin_two]
    exact Complex.measurable_re.comp (((h 0 0).mul (h 1 1)).sub ((h 0 1).mul (h 1 0)))
  exact ((measurable_const.indicator hJ).comp ((((h 0 0).add (measurable_snd.mul (h 1 0))).norm.pow_const 2).div
    ((Complex.measurable_re.comp (h 0 0)).mul hn))).mul (hd.div ((hn.pow_const 2).const_mul _)).ennreal_ofReal

theorem local_product : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ φ : (hB.atlas σ).Fld, (hB.atlas σ).IsForm φ → ∀ ε : ℤˣ, ∀ b₀ : CxPts q σ,
      ∃ U : Set (CxPts q σ), IsOpen U ∧ b₀ ∈ U ∧ ∃ G : CxPts q σ → Matrix (Fin 2) (Fin 2) ℂ, (∀ b ∈ U, (G b).PosDef) ∧
        ∀ S : Set (CxPts q σ), MeasurableSet S → S ⊆ U → ∀ J : Set ℝ, MeasurableSet J →
          (hY.atlas σ).part (evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (X 0 - X 3) * pullF hB hY σ π w φ) ε
              (PtsOver.map π w (spMap σ) ⁻¹' S ∩ v ⁻¹' J) =
            ∫⁻ b in S, (∫⁻ x : ℂ, J.indicator (fun _ => (1 : ENNReal)) (GlobalTheory.FibCos.cos (G b) x) *
              ENNReal.ofReal (GlobalTheory.FibCos.fs (G b) x)) ∂((hB.atlas σ).part φ (-ε)) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ v hv φ hφ ε b₀
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hB.isProjOver
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  obtain ⟨c₀, hc₀⟩ := (hB.atlas σ).cover b₀
  obtain ⟨c, hc, hle⟩ := exists_chart_le c₀ hc₀ (mem_frameAt flB b₀)
  let a := (frameAt flB b₀).mid (lineSC_shortExact flB)
  let cE : Chart E 2 := ⟨c.U, fun l => Twist.resM E hle (a.e l), a.isFrame.res hle⟩
  obtain ⟨W, hW, hWa, n, hΦ, hs⟩ := GlobalTheory.T.flag_bundle_affine_polynomial_coords B Y π Unit (fun _ => 2) (fun _ => E) (fun _ => fl) hfl
    (fun _ => h.isVB) c.U c.affine (fun _ => cE.e) fun _ => cE.isFrame
  letI : Unique (Σ _ : Unit, FlagFibre.Low 2) := ⟨⟨⟨(), ⟨(1, 0), by decide⟩⟩⟩, by
    rintro ⟨⟨⟩, ⟨⟨i, j⟩, hij⟩⟩
    fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)⟩
  obtain ⟨c', hU, hsrc, htgt, hc'⟩ := exists_prod_chart π w c hW hWa n hΦ hc
  set f := PtsOver.map π w (spMap σ)
  set G := (h.met σ).G cE
  have hG (b) (hb : b ∈ c.e.source) : (G b).PosDef := (h.met σ).posDef cE b (c.source_subset hb)
  have hGm (i j) : Measurable fun b => G b i j := by
    have h₁ : ContinuousOn (fun b => G b i j) (ptsIn q σ cE.U) := fun b hb =>
      (H σ cE b hb i j).continuousAt.continuousWithinAt
    have h₂ : ContinuousOn (fun b => G b i j) (ptsIn q σ cE.U)ᶜ :=
      (continuousOn_const (c := 0)).congr fun b hb => by simp only [G, (h.met σ).G_of_notMem cE hb]; rfl
    simpa using h₁.measurable_piecewise h₂ (isOpen_ptsIn _).measurableSet
  refine ⟨c.e.source, c.e.open_source, hc, G, hG, fun S hS hSc J hJ => ?_⟩
  have hfm : Measurable f := (PtsOver.continuous_map π w _).measurable
  have hT : MeasurableSet (v ⁻¹' J) :=
    CosSqMeas.measurable_cosSq k B Y q p d hB hY π w E h H flB fl hfl A σ v hv hJ
  have hf := GlobalTheory.T.points_map_holomorphic k B q d hB σ Y p (d + 1) hY π w
  have hpull := GlobalTheory.T.first_chern_form_pullback k B q d hB σ Y p (d + 1) hY π w
  have hc₁ (L : HermLB p) := (GlobalTheory.T.firstChern_real_closed k Y p (d + 1) hY σ L).1.1
  set α := evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (X 0 - X 3) * pullF hB hY σ π w φ
  have hαe : α = (fld _ (c1F hY σ (VMetric.grLB fl 0 (H.pull π w))) +
      (-1 : ℂ) • fld _ (c1F hY σ ((VMetric.grLB flB 0 H).pull π w))) * pullF hB hY σ π w φ := by
    refine congrArg (· * pullF hB hY σ π w φ) (funext fun x => ?_)
    simp only [evalF, fld, map_sub, map_X, aeval_X, Pi.add_apply, Pi.smul_apply, neg_one_smul, ← sub_eq_add_neg,
      AddSubgroupClass.coe_sub]
    exact sub_eq_add_neg _ _
  have hαx (x : (hY.atlas σ).Pt) : α x = ((c1F hY σ (VMetric.grLB fl 0 (H.pull π w)) x : Alt (d + 1)) -
      pullF hB hY σ π w (fld _ (c1F hB σ (VMetric.grLB flB 0 H))) x) * pullF hB hY σ π w φ x := by
    rw [hαe, hpull, Pi.mul_apply, Pi.add_apply, Pi.smul_apply, neg_one_smul, ← sub_eq_add_neg, fld]
  have halg := (GlobalTheory.T.isForm_one_add_mul_smul _ _ (hY.atlas σ)).2
  have hα : (hY.atlas σ).IsForm α := by
    rw [hαe]
    exact (halg 1 _ _ (halg 1 _ _ (hc₁ _) (halg (-1) _ _ (hc₁ _) (hc₁ (A.pull π w))).2.2).1
      (GlobalTheory.T.holAtlas_isForm_pullback_holomorphic _ _ _ _ _ _ _ _ hf hφ)).2.1
  have hbase (y) : basePt (c'.e y) = c.e (f y) := by rw [hc', FibTriv.basePt_prodPt]
  have hlast (y) : c'.e y (Fin.last d) = ev p σ W (n default) y := by rw [hc', FibTriv.prodPt_last]
  have hA : MeasurableSet (f ⁻¹' S ∩ v ⁻¹' J) := (hfm hS).inter hT
  have hnull : (hY.atlas σ).part α ε ((f ⁻¹' S ∩ v ⁻¹' J) \ c'.e.source) = 0 := by
    refine measure_mono_null (t := (ptsIn p σ c'.U)ᶜ) (fun y hy hy' => hy.2 ?_) (MixDens.part_compl_ptsIn hY.toIsArithVar
      (fun c y => (ε : ℤ) * (dens ((hY.atlas σ).loc α c (c.e y))).re) c'
      ⟨_, c'.e.map_target (x := prodPt (c.e b₀) 0) (by
        rw [htgt, mem_preimage, FibTriv.basePt_prodPt]; exact c.e.map_source hc)⟩)
    rw [hsrc]
    exact ⟨hSc hy.1.1, hU ▸ hy'⟩
  rw [← measure_inter_add_sdiff _ c'.e.open_source.measurableSet, hnull, add_zero,
    part_eq_chartMeas _ hα ε c' (hA.inter c'.e.open_source.measurableSet) inter_subset_right,
    (Measure.restrict_congr_meas hS).2 fun T hTS hT => part_eq_chartMeas _ hφ (-ε) c hT (hTS.trans hSc)]
  refine (ChartGlue.chartMeas_apply_of_subset c'.e _ (hA.inter c'.e.open_source.measurableSet) inter_subset_right).trans ?_
  rw [inter_comm _ c'.e.source]
  refine (ChartGlue.chartMeas_apply c'.e
    (fun y => ENNReal.ofReal ((ε : ℤ) * (dens ((hY.atlas σ).loc α c' (c'.e y))).re)) hA).symm.trans
    (chartMeas_prod c.e c'.e f (fun y hy => (hsrc ▸ hy).1) htgt
    (fun y _ => hbase y) _ ?_ _ _ (measurable_kernel hGm hJ) (fun y hy => ?_) hS hSc hA
    (c'.e.open_source.measurableSet.inter hT))
  · have h₁ : ContinuousOn (fun z => ENNReal.ofReal (((-ε : ℤˣ) : ℤ) * (dens ((hB.atlas σ).loc φ c z)).re)) c.e.target :=
      ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
        ((hφ.smooth c Finset.univ).continuousOn.div_const _)))
    refine (h₁.congr fun z hz => ?_).aemeasurable c.e.open_target.measurableSet
    exact congrArg (fun z => ENNReal.ofReal (((-ε : ℤˣ) : ℤ) * (dens ((hB.atlas σ).loc φ c z)).re)) (c.e.right_inv hz)
  have hy' := hsrc ▸ hy
  obtain ⟨i, hi, hwt⟩ := exists_weight (σ := σ) π w cE hW (fun s => n ⟨(), s⟩) H (hs ())
  have hvy := cosSq_eq π w cE hW (fun s => n ⟨(), s⟩) (hs ()) (flB.ι 1) (Twist.resM _ hle ((frameAt flB b₀).e 0))
    (Twist.app_resM _ _ _) hv hy'.2
  have hder : fderiv ℂ (c.e ∘ f ∘ c'.e.symm) (c'.e y) = fderiv ℂ basePt (c'.e y) := by
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [c'.e.open_target.mem_nhds (c'.e.map_source hy)] with z hz
    rw [Function.comp_apply, Function.comp_apply, ← hbase, c'.e.right_inv hz]
  have hp (β) (hβ : (hB.atlas σ).IsForm β) : pullF hB hY σ π w β ⟨(c', y), hy⟩ =
      pull (fderiv ℂ basePt (c'.e y)) (β ⟨(c, f y), hy'.1⟩) := by
    rw [← hder]
    exact pullback_eq_chart _ _ _ _ _ _ _ _ hf hβ ⟨(c', y), hy⟩ c hy'.1
  have hden : dens ((hY.atlas σ).loc α c' (c'.e y)) =
      (-FibCos.fs (G (f y)) (c'.e y (Fin.last d)) : ℝ) * dens ((hB.atlas σ).loc φ c (c.e (f y))) := by
    refine (congrArg dens ((hY.atlas σ).loc_crd α ⟨(c', y), hy⟩)).trans ?_
    rw [show (hB.atlas σ).loc φ c (c.e (f y)) = _ from (hB.atlas σ).loc_crd φ ⟨(c, f y), hy'.1⟩, hαx ⟨(c', y), hy⟩,
      hp _ hφ, hp _ (GlobalTheory.T.firstChern_real_closed k B q d hB σ _).1.1, c1F_eq_matForm_hessL hY σ _ c' hy i (hi ▸ hy'.2)]
    refine dens_fibre ((HermLB.cInf _ σ).contDiffAt c' hy (hi ▸ hy'.2)) (hG _ hy'.1) (fun x => ?_) _ _
    have hx : prodPt (basePt (c'.e y)) x ∈ c'.e.target := by
      rw [htgt, mem_preimage, FibTriv.basePt_prodPt, ← mem_preimage, ← htgt]
      exact c'.e.map_source hy
    have hz := hsrc ▸ c'.e.map_target hx
    have e₁ := hbase (c'.e.symm (prodPt (basePt (c'.e y)) x))
    have e₂ := hlast (c'.e.symm (prodPt (basePt (c'.e y)) x))
    rw [c'.e.right_inv hx] at e₁ e₂
    rw [FibTriv.basePt_prodPt, hbase] at e₁
    rw [FibTriv.prodPt_last] at e₂
    rw [hwt _ hz.2, c.e.injOn hy'.1 hz.1 (e₁.trans (by rw [hbase]))]
    exact congrArg (fun x => -Real.log (FibCos.nrm _ x)) e₂.symm
  have hfs : 0 ≤ FibCos.fs (G (f y)) (c'.e y (Fin.last d)) :=
    div_nonneg (Complex.pos_iff.1 (hG _ hy'.1).det_pos).1.le (by positivity)
  change _ = J.indicator _ (FibCos.cos (G (f y)) (c'.e y (Fin.last d))) * _ *
    ENNReal.ofReal (((-ε : ℤˣ) : ℤ) * (dens ((hB.atlas σ).loc φ c (c.e (f y)))).re)
  rw [hlast y, show FibCos.cos (G (f y)) (ev p σ W (n default) y) = v y from hvy.symm, ← hlast y]
  by_cases hJy : v y ∈ J
  · rw [indicator_of_mem hJy, indicator_of_mem (show y ∈ v ⁻¹' J from hJy), one_mul, hden, Complex.re_ofReal_mul,
      ← ENNReal.ofReal_mul hfs]
    congr 1
    push_cast
    ring
  · rw [indicator_of_notMem hJy, indicator_of_notMem (show y ∉ v ⁻¹' J from hJy), zero_mul, zero_mul]

end GlobalTheory.FibLoc
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open GlobalTheory.Points
open scoped Classical ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_line_bundle_chern_relation : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ φ : (hB.atlas σ).Fld, (hB.atlas σ).IsForm φ → ∀ ε : ℤˣ, ∀ b₀ : CxPts q σ,
      ∃ U : Set (CxPts q σ), IsOpen U ∧ b₀ ∈ U ∧ ∃ G : CxPts q σ → Matrix (Fin 2) (Fin 2) ℂ, (∀ b ∈ U, (G b).PosDef) ∧
        ∀ S : Set (CxPts q σ), MeasurableSet S → S ⊆ U → ∀ J : Set ℝ, MeasurableSet J →
          (hY.atlas σ).part (evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (X 0 - X 3) * pullF hB hY σ π w φ) ε
              (PtsOver.map π w (spMap σ) ⁻¹' S ∩ v ⁻¹' J) =
            ∫⁻ b in S, (∫⁻ x : ℂ, J.indicator (fun _ => (1 : ENNReal)) (GlobalTheory.FibCos.cos (G b) x) *
              ENNReal.ofReal (GlobalTheory.FibCos.fs (G b) x)) ∂((hB.atlas σ).part φ (-ε)) := by
  atlas_forward_decl GlobalTheory.FibLoc.local_product
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open GlobalTheory.Points
open scoped Classical ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FibCos

theorem map_eq_of_local {Z T : Type} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T] [OpensMeasurableSpace T]
    [MeasurableSpace Z] (μ : Measure Z) (ν : Measure T) (f : Z → T) (hf : Measurable f) (v : Z → ℝ) (hv : Measurable v)
    (hloc : ∀ b₀ : T, ∃ U : Set T, IsOpen U ∧ b₀ ∈ U ∧ ∀ S : Set T, MeasurableSet S → S ⊆ U → ∀ J : Set ℝ,
      MeasurableSet J → μ (f ⁻¹' S ∩ v ⁻¹' J) = ν S * volume (J ∩ Set.Icc (0 : ℝ) 1)) :
    Measure.map v μ = ν Set.univ • volume.restrict (Set.Icc (0 : ℝ) 1) := by
  choose U hUo hU hUS using hloc
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover U fun b _ => (hUo b).mem_nhds (hU b)
  ext J hJ
  have key : Measure.map f (μ.restrict (v ⁻¹' J)) = volume (J ∩ Set.Icc (0 : ℝ) 1) • ν := by
    refine Measure.ext_of_biUnion_eq_univ (S := (t : Set T)) t.countable_toSet
      (Set.eq_univ_of_univ_subset (by simpa using ht)) fun b _ => ?_
    ext A hA
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA, Measure.map_apply hf (hA.inter (hUo b).measurableSet),
      Measure.restrict_apply (hf (hA.inter (hUo b).measurableSet)),
      hUS b _ (hA.inter (hUo b).measurableSet) Set.inter_subset_right J hJ, Measure.smul_apply, smul_eq_mul, mul_comm]
  have e := congrArg (fun m : Measure T => m Set.univ) key
  simp only [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Measure.smul_apply, smul_eq_mul] at e
  rw [Measure.map_apply hv hJ, e, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hJ, mul_comm]

end GlobalTheory.FibCos

theorem GlobalTheory.FibCos.map_part : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ φ : (hB.atlas σ).Fld, (hB.atlas σ).IsForm φ → ∀ ε : ℤˣ,
      Measure.map v ((hY.atlas σ).part (evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (X 0 - X 3) * pullF hB hY σ π w φ) ε) =
        (hB.atlas σ).part φ (-ε) Set.univ • volume.restrict (Set.Icc (0 : ℝ) 1) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ v hv φ hφ ε
  haveI : CompactSpace (CxPts q σ) := hB.compactSpace σ
  refine GlobalTheory.FibCos.map_eq_of_local _ _ _ (PtsOver.continuous_map π w (spMap σ)).measurable v
    (GlobalTheory.CosSqMeas.measurable_cosSq k B Y q p d hB hY π w E h H flB fl hfl A σ v hv) fun b₀ => ?_
  obtain ⟨U, hUo, hb, G, hG, hS⟩ := GlobalTheory.T.flag_bundle_line_bundle_chern_relation k B Y q p d hB hY π w E h H flB fl hfl A σ v hv φ hφ ε b₀
  refine ⟨U, hUo, hb, fun S hSm hSU J hJ => ?_⟩
  rw [hS S hSm hSU J hJ, setLIntegral_congr_fun hSm (fun b hb => GlobalTheory.T.fibre_cosine_pushforward_uniform (G b) (hG b (hSU hb)) J hJ),
    setLIntegral_const, mul_comm]
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_hermitian_line_integral_formula : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ φ : (hB.atlas σ).Fld, (hB.atlas σ).IsForm φ → ∀ ε : ℤˣ,
      Measure.map v ((hY.atlas σ).part (evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (X 0 - X 3) * pullF hB hY σ π w φ) ε) =
        (hB.atlas σ).part φ (-ε) Set.univ • volume.restrict (Set.Icc (0 : ℝ) 1) := by
  atlas_forward_decl GlobalTheory.FibCos.map_part
end

section
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineCos

theorem map_cosSq_part_le : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ α : (hY.atlas σ).Fld, (hY.atlas σ).IsForm α → ∀ ε : ℤˣ,
      ∃ C : ENNReal, C ≠ ⊤ ∧ Measure.map v ((hY.atlas σ).part α ε) ≤ C • volume.restrict (Set.Icc (0 : ℝ) 1) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ v hv α hα ε
  haveI : CompactSpace (CxPts p σ) := CxPts.compactSpace σ hY.isProjOver
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  have loc : ∀ y : CxPts p σ, ∃ W : Set (CxPts p σ), IsOpen W ∧ y ∈ W ∧ ContinuousOn v W ∧ ∃ C : ENNReal, C ≠ ⊤ ∧
      Measure.map v (((hY.atlas σ).part α ε).restrict W) ≤ C • volume.restrict (Set.Icc (0 : ℝ) 1) := by
    intro y
    obtain ⟨c, G, s, O, hy, hO, hcy, hOt, hG, hGp⟩ := GlobalTheory.T.flag_bundle_curvature_at_point k B Y q p d hB hY π w E h H flB fl hfl σ v hv y
    have hρ : ContinuousOn (fun z => ((ε : ℤ) : ℝ) * (hY.atlas σ).reDens α c z) O :=
      (continuousOn_const.mul ((hY.atlas σ).continuousOn_reDens hα c)).mono hOt
    obtain ⟨N, hN, hzN, hNO, C, hC, hle⟩ :=
      GlobalTheory.T.local_density_bound_near_point d O (fun z => ((ε : ℤ) : ℝ) * (hY.atlas σ).reDens α c z) G s (c.e y) hO hcy hρ hG fun z hz => (hGp z hz).1
    have hWo : IsOpen (c.e.source ∩ c.e ⁻¹' N) := c.e.isOpen_inter_preimage hN
    have hWc : ContinuousOn v (c.e.source ∩ c.e ⁻¹' N) := by
      have hF := GlobalTheory.LineCos.continuousOn_cosSq s hG fun z hz => (hGp z hz).1
      have : ContinuousOn (fun y => GlobalTheory.LineCos.cosSq s (G (GlobalTheory.LineCos.base (c.e y))) (GlobalTheory.LineCos.fib (c.e y)))
          (c.e.source ∩ c.e ⁻¹' N) :=
        hF.comp (c.e.continuousOn.mono Set.inter_subset_left) fun y hy => hNO hy.2
      refine this.congr fun y' hy' => ?_
      have := (hGp (c.e y') (hNO hy'.2)).2
      rwa [c.e.left_inv hy'.1] at this
    refine ⟨_, hWo, ⟨hy, hzN⟩, hWc, C, hC, ?_⟩
    set W := c.e.source ∩ c.e ⁻¹' N with hWdef
    have hWm : MeasurableSet W := hWo.measurableSet
    have hNt : N ⊆ c.e.target := hNO.trans hOt
    set ν := (volume.restrict N).withDensity fun z => ENNReal.ofReal (((ε : ℤ) : ℝ) * (hY.atlas σ).reDens α c z) with hνdef
    have haem : AEMeasurable c.e.symm ν :=
      ((c.e.continuousOn_symm.mono hNt).aemeasurable hN.measurableSet).mono_ac (withDensity_absolutelyContinuous _ _)
    have hcompat : ∀ (i j : (hY.atlas σ).ι) (y : CxPts p σ), y ∈ ((hY.atlas σ).e i).source → y ∈ ((hY.atlas σ).e j).source →
        ENNReal.ofReal (((ε : ℤ) : ℝ) * (hY.atlas σ).reDens α i ((hY.atlas σ).e i y)) =
          ENNReal.ofReal (‖ChartGlue.transDet ((hY.atlas σ).e i) ((hY.atlas σ).e j) y‖ ^ 2) *
            ENNReal.ofReal (((ε : ℤ) : ℝ) * (hY.atlas σ).reDens α j ((hY.atlas σ).e j y)) :=
      (hY.atlas σ).ofReal_compat (fun i v => ((ε : ℤ) : ℝ) * (hY.atlas σ).reDens α i v)
        (fun i j y hi hj => by rw [(hY.atlas σ).reDens_compat hα i j y hi hj]; ring)
    have hrest : ((hY.atlas σ).part α ε).restrict W = Measure.map c.e.symm ν := by
      ext A hA
      have hAW : MeasurableSet (A ∩ W) := hA.inter hWm
      have hsub : A ∩ W ⊆ c.e.source := fun y hy => hy.2.1
      have hp : (hY.atlas σ).part α ε = ChartGlue.glueMeas (hY.atlas σ).e
          (fun i y => ENNReal.ofReal (((ε : ℤ) : ℝ) * (hY.atlas σ).reDens α i ((hY.atlas σ).e i y))) := rfl
      rw [Measure.restrict_apply hA, Measure.map_apply_of_aemeasurable haem hA, hp,
        ChartGlue.glueMeas_apply _ _ (hY.atlas σ).holo hcompat c hAW hsub,
        ChartGlue.chartMeas_apply_of_subset ((hY.atlas σ).e c) _ hAW hsub, hνdef, withDensity_apply' _ _,
        Measure.restrict_restrict' hN.measurableSet]
      have himg : (c.e '' (A ∩ W)) = c.e.symm ⁻¹' A ∩ N := by
        ext z
        constructor
        · rintro ⟨y', ⟨hyA, hys, hyN⟩, rfl⟩
          exact ⟨by simpa [c.e.left_inv hys] using hyA, hyN⟩
        · rintro ⟨hzA, hzN'⟩
          exact ⟨c.e.symm z, ⟨hzA, c.e.map_target (hNt hzN'), by simpa [c.e.right_inv (hNt hzN')] using hzN'⟩,
            c.e.right_inv (hNt hzN')⟩
      change ∫⁻ v in c.e '' (A ∩ W), ENNReal.ofReal (((ε : ℤ) : ℝ) *
          (hY.atlas σ).reDens α c (c.e (c.e.symm v))) = _
      rw [himg]
      refine setLIntegral_congr_fun (himg ▸ ChartGlue.measurableSet_image _ hAW hsub) fun z hz => ?_
      rw [c.e.right_inv (hNt hz.2)]
    have hvae : AEMeasurable v (Measure.map c.e.symm ν) := by
      rw [← hrest]
      exact hWc.aemeasurable hWm
    rw [hrest, AEMeasurable.map_map_of_aemeasurable hvae haem]
    refine le_of_eq_of_le (Measure.map_congr ?_) hle
    refine (withDensity_absolutelyContinuous _ _).ae_le ((ae_restrict_iff' hN.measurableSet).2
      (Filter.Eventually.of_forall fun z hz => (hGp z (hNO hz)).2))

  choose W hWo hyW hWc C hC hle using loc
  have hvc : Continuous v :=
    continuous_iff_continuousAt.2 fun y => (hWc y).continuousAt ((hWo y).mem_nhds (hyW y))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWo fun y _ => Set.mem_iUnion.2 ⟨y, hyW y⟩
  refine ⟨∑ y ∈ t, C y, ENNReal.sum_ne_top.2 fun y _ => hC y, Measure.le_iff.2 fun S hS => ?_⟩
  have hsub : v ⁻¹' S ⊆ ⋃ y ∈ t, (v ⁻¹' S ∩ W y) := fun x hx => by
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact Set.mem_iUnion₂.2 ⟨y, hy, hx, hxy⟩
  calc Measure.map v ((hY.atlas σ).part α ε) S = (hY.atlas σ).part α ε (v ⁻¹' S) :=
        Measure.map_apply hvc.measurable hS
    _ ≤ ∑ y ∈ t, (hY.atlas σ).part α ε (v ⁻¹' S ∩ W y) :=
        (measure_mono hsub).trans (measure_biUnion_finset_le t _)
    _ = ∑ y ∈ t, Measure.map v (((hY.atlas σ).part α ε).restrict (W y)) S := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Measure.map_apply hvc.measurable hS, Measure.restrict_apply (hvc.measurable hS)]
    _ ≤ ∑ y ∈ t, C y * volume.restrict (Set.Icc (0 : ℝ) 1) S :=
        Finset.sum_le_sum fun y _ => Measure.le_iff.1 (hle y) S hS
    _ = ((∑ y ∈ t, C y) • volume.restrict (Set.Icc (0 : ℝ) 1)) S := by
        rw [Measure.smul_apply, smul_eq_mul, Finset.sum_mul]

end GlobalTheory.LineCos
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_hermitian_line_degree_identity : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ α : (hY.atlas σ).Fld, (hY.atlas σ).IsForm α → ∀ ε : ℤˣ,
      ∃ C : ENNReal, C ≠ ⊤ ∧ Measure.map v ((hY.atlas σ).part α ε) ≤ C • volume.restrict (Set.Icc (0 : ℝ) 1) := by
  atlas_forward_decl GlobalTheory.LineCos.map_cosSq_part_le
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.FibLog

theorem integrableOn_log_one_sub : IntegrableOn (fun t : ℝ => Real.log (1 - t) / 2) (Set.Icc 0 1) := by
  have h1 : IntervalIntegrable (fun t : ℝ => Real.log (1 - t)) volume 0 1 := by
    have := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1)).comp_sub_left 1
    simpa using this.symm
  exact ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).1 h1).div_const 2

theorem integral_log_one_sub : ∫ t in Set.Icc (0 : ℝ) 1, Real.log (1 - t) / 2 = -1 / 2 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_div]
  have : ∫ t in (0 : ℝ)..1, Real.log (1 - t) = ∫ t in (0 : ℝ)..1, Real.log t := by
    rw [intervalIntegral.integral_comp_sub_left (fun t => Real.log t) 1]; simp
  rw [this, integral_log]; norm_num

theorem wInt_log_one_sub : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    (∀ α : (hY.atlas σ).Fld, (hY.atlas σ).IsForm α → ∀ ε : ℤˣ, Integrable (fun y => Real.log (1 - v y) / 2) ((hY.atlas σ).part α ε)) ∧
      ∀ φ : (hB.atlas σ).Fld, (hB.atlas σ).IsForm φ →
        wInt (hY.atlas σ) (fun y => Real.log (1 - v y) / 2) (evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (X 0 - X 3) * pullF hB hY σ π w φ) = 1 / 2 * (hB.atlas σ).integral φ := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ v hv
  have hm : Measurable v := GlobalTheory.T.flag_bundle_hermitian_line_pullback_form k B Y q p d hB hY π w E h H flB fl hfl A σ v hv
  have hG : Measurable (fun t : ℝ => Real.log (1 - t) / 2) :=
    ((Real.measurable_log.comp (measurable_const.sub measurable_id))).div_const 2
  have key : ∀ (μ : Measure (CxPts p σ)) (C : ENNReal), Measure.map v μ = C • volume.restrict (Set.Icc (0 : ℝ) 1) →
      ∫ y, Real.log (1 - v y) / 2 ∂μ = C.toReal * (-1 / 2) := by
    intro μ C hμ
    have := integral_map (μ := μ) hm.aemeasurable (f := fun t : ℝ => Real.log (1 - t) / 2) hG.aestronglyMeasurable
    rw [← this, hμ, integral_smul_measure, GlobalTheory.FibLog.integral_log_one_sub, smul_eq_mul]
  refine ⟨fun α hα ε => ?_, fun φ hφ => ?_⟩
  · obtain ⟨C, hC, hle⟩ := GlobalTheory.T.flag_bundle_hermitian_line_degree_identity k B Y q p d hB hY π w E h H flB fl hfl A σ v hv α hα ε
    have hi : Integrable (fun t : ℝ => Real.log (1 - t) / 2) (Measure.map v ((hY.atlas σ).part α ε)) :=
      (GlobalTheory.FibLog.integrableOn_log_one_sub.smul_measure hC).mono_measure hle
    exact (integrable_map_measure hG.aestronglyMeasurable hm.aemeasurable).1 hi
  · have h1 := key _ _ (GlobalTheory.T.flag_bundle_hermitian_line_integral_formula k B Y q p d hB hY π w E h H flB fl hfl A σ v hv φ hφ 1)
    have h2 := key _ _ (GlobalTheory.T.flag_bundle_hermitian_line_integral_formula k B Y q p d hB hY π w E h H flB fl hfl A σ v hv φ hφ (-1))
    rw [wInt, h1, h2, HolAtlas.integral, neg_neg, Measure.real, Measure.real]
    ring

end GlobalTheory.FibLog
end
end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_chern_integral_pull_fourth : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    (∀ α : (hY.atlas σ).Fld, (hY.atlas σ).IsForm α → ∀ ε : ℤˣ, Integrable (fun y => Real.log (1 - v y) / 2) ((hY.atlas σ).part α ε)) ∧
      ∀ φ : (hB.atlas σ).Fld, (hB.atlas σ).IsForm φ →
        wInt (hY.atlas σ) (fun y => Real.log (1 - v y) / 2) (evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (X 0 - X 3) * pullF hB hY σ π w φ) = 1 / 2 * (hB.atlas σ).integral φ := by
  atlas_forward_decl GlobalTheory.FibLog.wInt_log_one_sub
end
