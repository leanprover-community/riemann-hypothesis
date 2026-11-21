import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.SegreChartProjObjects
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSemiPosMassFinite
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MemChartComponents
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SetFibreFiniteOfGoodProj
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AemeasurableCxPosDensity
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegralDensityIndependentProjection
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjChartSetEqSetChartSet
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SetSegreConeSmul
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsWeightedHomogeneousOfIsMultiHomog
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartDensityIntegrable
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChartA
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsGoodProjFirstCoordinate
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffGradient
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DomCellLogNormMeasurableInvariant
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsPosDensIntegrable

section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setFibre_finite_of_goodProj : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → ∀ y, (setFibre (conePts Q) Ψ y).Finite := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite | exact GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxFib.setFibre_finite <;> assumption)
end

section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aemeasurable_cxPosDensity : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → (∀ j, IsSmoothHerm (L j)) → Measurable g →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) →
    AEMeasurable (cxPosDens (conePts Q) Ψ (pot L) g) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable | exact GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxPosMeas.cxPosDens_aemeasurable <;> assumption)
end

section
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart.PolyLog

open Set GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open scoped ENNReal

variable {n : ℕ}

def graphHom (f : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin (n + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  aeval (Fin.snoc (α := fun _ => MvPolynomial (Fin n) ℂ) (fun i => X i) f)

theorem graphHom_castSucc (f : MvPolynomial (Fin n) ℂ) (i : Fin n) :
    graphHom f (X i.castSucc) = X i := by
  simp [graphHom]

theorem graphHom_last (f : MvPolynomial (Fin n) ℂ) : graphHom f (X (Fin.last n)) = f := by
  simp [graphHom]

theorem graphHom_surjective (f : MvPolynomial (Fin n) ℂ) : Function.Surjective (graphHom f) := by
  intro q
  induction q using MvPolynomial.induction_on with
  | C a => exact ⟨C a, by simp [graphHom]⟩
  | add p q hp hq =>
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    exact ⟨a + b, map_add _ _ _⟩
  | mul_X p i hp =>
    obtain ⟨a, rfl⟩ := hp
    exact ⟨a * X i.castSucc, by rw [map_mul, graphHom_castSucc]⟩

theorem eval_graphHom (f : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ)
    (q : MvPolynomial (Fin (n + 1)) ℂ) :
    eval x (graphHom f q) =
      eval (Fin.snoc (α := fun _ => ℂ) x (eval x f)) q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [graphHom]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp]
    congr 1
    induction i using Fin.lastCases with
    | last => simp [graphHom_last]
    | cast i => simp [graphHom_castSucc]

def graphIdeal (J : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin n) ℂ) :
    Ideal (MvPolynomial (Fin (n + 1)) ℂ) :=
  RingHom.ker ((Ideal.Quotient.mk J).comp (graphHom f).toRingHom)

theorem graphIdeal_surjective (J : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin n) ℂ) :
    Function.Surjective ((Ideal.Quotient.mk J).comp (graphHom f).toRingHom) :=
  (Ideal.Quotient.mk_surjective).comp (graphHom_surjective f)

theorem graphIdeal_isPrime {J : Ideal (MvPolynomial (Fin n) ℂ)} (f : MvPolynomial (Fin n) ℂ)
    (hJ : J.IsPrime) : (graphIdeal J f).IsPrime := by
  haveI := hJ
  exact RingHom.ker_isPrime _

theorem graphIdeal_dim (J : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin n) ℂ) :
    ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ graphIdeal J f) =
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
  ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective (graphIdeal_surjective J f))

theorem linForm_last : linForm (Pi.single (Fin.last n) (1 : ℂ)) =
    (X (Fin.last n) : MvPolynomial (Fin (n + 1)) ℂ) := by
  unfold linForm
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

theorem linForm_last_not_mem {J : Ideal (MvPolynomial (Fin n) ℂ)} {f : MvPolynomial (Fin n) ℂ}
    (hf : f ∉ J) : linForm (Pi.single (Fin.last n) (1 : ℂ)) ∉ graphIdeal J f := by
  rw [linForm_last]
  intro h
  apply hf
  have : (Ideal.Quotient.mk J) (graphHom f (X (Fin.last n))) = 0 := h
  rw [graphHom_last] at this
  exact Ideal.Quotient.eq_zero_iff_mem.mp this

def dropLast (w : EuclideanSpace ℂ (Fin (n + 1))) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 fun i => w i.castSucc

def addLast (z : EuclideanSpace ℂ (Fin n)) (t : ℂ) : EuclideanSpace ℂ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ => ℂ) (fun i => z i) t)

theorem dropLast_addLast (z : EuclideanSpace ℂ (Fin n)) (t : ℂ) : dropLast (addLast z t) = z := by
  ext i
  simp [dropLast, addLast]

theorem norm_sq_addLast (z : EuclideanSpace ℂ (Fin n)) (t : ℂ) :
    ‖addLast z t‖ ^ 2 = ‖z‖ ^ 2 + ‖t‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
  simp [addLast]

theorem lipschitz_dropLast : LipschitzWith 1 (dropLast (n := n)) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq, NNReal.coe_one, one_mul]
  refine Real.sqrt_le_sqrt ?_
  rw [Fin.sum_univ_castSucc]
  have : 0 ≤ dist (a (Fin.last n)) (b (Fin.last n)) ^ 2 := by positivity
  simpa [dropLast] using this

theorem slab_bound (d : ℕ) {J : Ideal (MvPolynomial (Fin n) ℂ)} (f : MvPolynomial (Fin n) ℂ) (R : ℝ)
    (hJ : J.IsPrime) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (hf : f ∉ J) :
    ∃ C α : ℝ, 0 < α ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ {z | ‖z‖ ≤ R} ∩
        {z | ‖eval (fun i => z i) f‖ ≤ ε}) ≤ ENNReal.ofReal (C * ε ^ α) := by
  obtain ⟨C, α, hα, hC⟩ := VarSlabMeasure.full (n + 1) d (graphIdeal J f)
    (Pi.single (Fin.last n) (1 : ℂ)) (R + 1) (graphIdeal_isPrime f hJ)
    ((graphIdeal_dim J f).trans hdim) (linForm_last_not_mem hf)
  refine ⟨C, α, hα, fun ε hε hε1 => ?_⟩
  refine le_trans ?_ (hC ε hε hε1)
  have hsub : zeroSetEuc J ∩ {z | ‖z‖ ≤ R} ∩ {z | ‖eval (fun i => z i) f‖ ≤ ε} ⊆
      dropLast '' (zeroSetEuc (graphIdeal J f) ∩ {w | ‖w‖ ≤ R + 1} ∩
        {w | ‖∑ j, (Pi.single (Fin.last n) (1 : ℂ) : Fin (n + 1) → ℂ) j * w j‖ ≤ ε}) := by
    rintro z ⟨⟨hzJ, hzR⟩, hzf⟩
    have hzR' : ‖z‖ ≤ R := hzR
    have hzf' : ‖eval (fun i => z i) f‖ ≤ ε := hzf
    refine ⟨addLast z (eval (fun i => z i) f), ⟨⟨?_, ?_⟩, ?_⟩, dropLast_addLast _ _⟩
    · intro q hq
      have h1 : graphHom f q ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hq
      have h2 := eval_graphHom f (fun i => z i) q
      rw [hzJ _ h1] at h2
      exact h2.symm
    · have h0 : 0 ≤ R := (norm_nonneg z).trans hzR'
      have h1 := norm_sq_addLast z (eval (fun i => z i) f)
      have h2 : ‖z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzR' 2
      have h3 : ‖eval (fun i => z i) f‖ ^ 2 ≤ 1 :=
        pow_le_one₀ (norm_nonneg _) (hzf'.trans hε1)
      show ‖addLast z (eval (fun i => z i) f)‖ ≤ R + 1
      refine abs_le_of_sq_le_sq' ?_ (by linarith) |>.2
      nlinarith
    · show ‖∑ j, (Pi.single (Fin.last n) (1 : ℂ) : Fin (n + 1) → ℂ) j * _‖ ≤ ε
      rw [Finset.sum_eq_single (Fin.last n)]
      · simpa [addLast] using hzf'
      · intro b _ hb; simp [Pi.single_apply, hb]
      · simp
  refine (measure_mono hsub).trans ?_
  have := lipschitz_dropLast.hausdorffMeasure_image_le (d := ((2 * d : ℕ) : ℝ)) (by positivity)
    (zeroSetEuc (graphIdeal J f) ∩ {w | ‖w‖ ≤ R + 1} ∩
        {w | ‖∑ j, (Pi.single (Fin.last n) (1 : ℂ) : Fin (n + 1) → ℂ) j * w j‖ ≤ ε})
  simpa using this

theorem bounded_part_finite (d : ℕ) {J : Ideal (MvPolynomial (Fin n) ℂ)} (R : ℝ) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) :
    μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ {z | ‖z‖ ≤ R}) < ⊤ := by
  have hsub : zeroSetEuc J ∩ {z : EuclideanSpace ℂ (Fin n) | ‖z‖ ≤ R} ⊆
      zeroSetEuc J ∩ Metric.ball 0 (R + 1) := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    rw [mem_ball_zero_iff]
    linarith [(show ‖z‖ ≤ R from hz.2)]
  exact (measure_mono hsub).trans_lt (HilbertSamuel.Closed.MassFinite n d J hJ hdim (R + 1))

theorem lintegral_lt_top (d : ℕ) {J : Ideal (MvPolynomial (Fin n) ℂ)} (f : MvPolynomial (Fin n) ℂ)
    (R : ℝ) (hJ : J.IsPrime) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (hf : f ∉ J) :
    ∫⁻ z in zeroSetEuc J ∩ {z | ‖z‖ ≤ R}, ‖Real.log ‖eval (fun i => z i) f‖‖ₑ
      ∂(μH[((2 * d : ℕ) : ℝ)]) < ⊤ := by
  obtain ⟨C, α, hα, hC⟩ := slab_bound d f R hJ hdim hf
  set S := zeroSetEuc J ∩ {z : EuclideanSpace ℂ (Fin n) | ‖z‖ ≤ R} with hSdef
  set μ := (μH[((2 * d : ℕ) : ℝ)]).restrict S
  have hSfin : μH[((2 * d : ℕ) : ℝ)] S < ⊤ := bounded_part_finite d R hJ hdim
  have hcont : Continuous fun z : EuclideanSpace ℂ (Fin n) => eval (fun i => z i) f :=
    (MvPolynomial.continuous_eval f).comp (PiLp.continuous_ofLp 2 _)
  set F : EuclideanSpace ℂ (Fin n) → ℝ := fun z => Real.log ‖eval (fun i => z i) f‖
  have hFm : Measurable F := Real.measurable_log.comp hcont.norm.measurable
  set G : EuclideanSpace ℂ (Fin n) → ℝ := fun z => max (-F z) 0
  have hGm : Measurable G := hFm.neg.max measurable_const
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : EuclideanSpace ℂ (Fin n)) R).exists_bound_of_continuousOn
    hcont.continuousOn
  set M : ℝ := max B 0

  have hFle : ∀ z ∈ S, F z ≤ M := by
    intro z hz
    refine (Real.log_le_self (norm_nonneg _)).trans ((hB z ?_).trans (le_max_left _ _))
    rw [mem_closedBall_zero_iff]
    exact hz.2

  have hG : ∫⁻ z, ENNReal.ofReal (G z) ∂μ < ⊤ := by
    rw [lintegral_eq_lintegral_meas_le (f := G) μ (Eventually.of_forall fun z => le_max_right _ _)
      hGm.aemeasurable]
    have hint : IntegrableOn (fun t => C * Real.exp (-α * t)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hα).const_mul C
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hint.lintegral_lt_top
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t (ht : 0 < t) => ?_)
    rw [Measure.restrict_apply (measurableSet_le measurable_const hGm)]
    refine (measure_mono ?_).trans ((hC (Real.exp (-t)) (Real.exp_pos _)
      (Real.exp_le_one_iff.mpr (by linarith))).trans_eq ?_)
    · rintro z ⟨hz, hzS⟩
      refine ⟨hzS, ?_⟩
      have htF : F z ≤ -t := by
        rcases le_max_iff.mp (show t ≤ G z from hz) with h1 | h1
        · linarith
        · linarith
      change ‖eval (fun i => z i) f‖ ≤ Real.exp (-t)
      rcases (norm_nonneg (eval (fun i => z i) f)).eq_or_lt with h0 | h0
      · rw [← h0]; positivity
      · exact (Real.log_le_iff_le_exp h0).mp htF
    · rw [← Real.exp_mul]; ring_nf
  have hle : ∀ z ∈ S, ‖F z‖ₑ ≤ ENNReal.ofReal M + ENNReal.ofReal (G z) := by
    intro z hz
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hFle z hz
    rcases le_or_gt 0 (F z) with h2 | h2
    · rw [abs_of_nonneg h2]; have := le_max_right (-F z) 0; linarith
    · rw [abs_of_neg h2]; have := le_max_left (-F z) 0; have := le_max_right B 0
      linarith
  refine lt_of_le_of_lt (setLIntegral_mono (g := fun z => ENNReal.ofReal M + ENNReal.ofReal (G z))
    (measurable_const.add hGm.ennreal_ofReal) hle) ?_
  rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSfin, hG⟩

theorem integrable_chartAbsDens_log :
    ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : MvPolynomial (Fin n) ℂ) (φ : Fin d → (Fin n → ℂ) → ℝ) (R C : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A → f ∉ J →
    (∀ i, GroundTheory.Heights₂.Heights.SmoothNear (GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J) (φ i)) →
    Integrable (chartAbsDens J A
      ((Metric.closedBall 0 R).indicator fun x => |Real.log ‖MvPolynomial.eval x f‖| + C) φ) := by
  intro n d J A f φ R C hJ hdim hA hf hφ
  have hcont : Continuous fun x : Fin n → ℂ => eval x f := MvPolynomial.continuous_eval f
  have hgm : Measurable fun x : Fin n → ℂ => |Real.log ‖eval x f‖| + C :=
    ((Real.measurable_log.comp hcont.norm.measurable).abs).add_const C
  refine ⟨(SheetSumMeasurable.proof n d J A _ φ hJ hdim hA
    (hgm.indicator measurableSet_closedBall) hφ).2.aestronglyMeasurable, ?_⟩
  obtain ⟨K, hK, hDK⟩ := HilbertSamuel.Closed.ChartMassCompare n d J A φ R hJ hdim hA hφ

  obtain ⟨L, hL0, hL⟩ : ∃ L : ℝ, 0 ≤ L ∧
      ∀ z : EuclideanSpace ℂ (Fin n), ‖z‖ ≤ L * ‖WithLp.ofLp z‖ :=
    ⟨(n : ℝ) ^ (2⁻¹ : ℝ), by positivity, fun z => by
      simpa [dist_zero_right] using
        (PiLp.lipschitzWith_toLp 2 (fun _ : Fin n => ℂ)).dist_le_mul (WithLp.ofLp z) 0⟩
  unfold HasFiniteIntegral
  refine (hDK _ hgm).trans_lt (ENNReal.mul_lt_top hK ?_)
  set S := zeroSetEuc J ∩ {z : EuclideanSpace ℂ (Fin n) | ‖z‖ ≤ L * R} with hSdef
  have hsub : zeroSetEuc J ∩ {z : EuclideanSpace ℂ (Fin n) |
      WithLp.ofLp z ∈ Metric.closedBall (0 : Fin n → ℂ) R} ⊆ S := by
    rintro z ⟨hz, hzB⟩
    refine ⟨hz, ?_⟩
    have : ‖WithLp.ofLp z‖ ≤ R := mem_closedBall_zero_iff.mp hzB
    exact (hL z).trans (mul_le_mul_of_nonneg_left this hL0)
  refine lt_of_le_of_lt (lintegral_mono_set hsub) ?_
  have hSfin : μH[((2 * d : ℕ) : ℝ)] S < ⊤ := bounded_part_finite d (L * R) hJ hdim
  have hlog := lintegral_lt_top d f (L * R) hJ hdim hf
  have hcontE : Continuous fun z : EuclideanSpace ℂ (Fin n) => eval (fun i => z i) f :=
    (MvPolynomial.continuous_eval f).comp (PiLp.continuous_ofLp 2 _)
  have hFm : Measurable fun z : EuclideanSpace ℂ (Fin n) => Real.log ‖eval (fun i => z i) f‖ :=
    Real.measurable_log.comp hcontE.norm.measurable
  have hle : ∀ z : EuclideanSpace ℂ (Fin n),
      ‖|Real.log ‖eval (WithLp.ofLp z) f‖| + C‖ₑ ≤
        ‖Real.log ‖eval (fun i => z i) f‖‖ₑ + ‖C‖ₑ := by
    intro z
    refine (enorm_add_le _ _).trans ?_
    have : ‖|Real.log ‖eval (WithLp.ofLp z) f‖|‖ₑ = ‖Real.log ‖eval (fun i => z i) f‖‖ₑ := by
      rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_abs]
    rw [this]
  refine lt_of_le_of_lt (lintegral_mono fun z => hle z) ?_
  rw [lintegral_add_right _ measurable_const, lintegral_const, Measure.restrict_apply_univ]
  exact ENNReal.add_lt_top.mpr ⟨hlog, ENNReal.mul_lt_top enorm_lt_top hSfin⟩

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart.PolyLog

end
end

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_chartAbsDensity : ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : MvPolynomial (Fin n) ℂ) (φ : Fin d → (Fin n → ℂ) → ℝ) (R C : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A → f ∉ J →
    (∀ i, GroundTheory.Heights₂.Heights.SmoothNear (GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J) (φ i)) →
    Integrable (chartAbsDens J A
      ((Metric.closedBall 0 R).indicator fun x => |Real.log ‖MvPolynomial.eval x f‖| + C) φ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Pub.CxChart.PolyLog.integrable_chartAbsDens_log
end

section
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

theorem zeroSet_chartIdeal_conePts : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsMultiHomogIdeal Q →
    GroundTheory.Heights₂.Heights.ComplexSets.zeroSet (GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal (conePts Q) σ i) =
      chartSet (conePts Q) σ i := by
  intro K _ _ ι _ Q m σ i hQ
  exact segChart_zeroSet (isMultiHomogIdeal_toR hQ) σ i

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeroSet_chartIdeal_eq_chartSet : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsMultiHomogIdeal Q →
    GroundTheory.Heights₂.Heights.ComplexSets.zeroSet (GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal (conePts Q) σ i) =
      chartSet (conePts Q) σ i := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Pub.CxChart.zeroSet_chartIdeal_conePts
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt
open ReciprocityTheory.AnForm.R (conePts)

theorem chartComponents_dim : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsCxVar Q e → ∀ J ∈ chartComponents (conePts Q) σ i,
      ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ) := by
  intro K _ _ ι _ Q e m σ i hQ J hJ
  have hmin : J ∈ (setSegChartIdeal (conePts Q) σ i).minimalPrimes :=
    mem_chartComponents.mp hJ
  have hhom : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q := hQ.2.1.2.1
  exact segChart_dim hQ.2.1.1 hhom hQ.2.2 σ i hmin

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringKrullDim_chartComponents : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k),
    IsCxVar Q e → ∀ J ∈ chartComponents (conePts Q) σ i,
      ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartComponents_dim
end

section
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FinProj

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

open GroundTheory.Heights₂.Heights.ComplexSets

theorem setChartIdeal_le_chartIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {S : Set ((Σ k, ι k) → ℂ)} {e m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (hΨ0 : ∀ w, Ψ w 0 = w i) :
    GlobalTheory.CompanionTheory.Ar.Pub.CxChart.setChartIdeal S σ Ψ ≤ GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal S σ i := by
  have hset : GlobalTheory.CompanionTheory.Ar.Pub.CxChart.setChartSet S σ Ψ = GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartSet S σ i := by
    ext x
    simp only [GlobalTheory.CompanionTheory.Ar.Pub.CxChart.setChartSet, GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartSet, hΨ0]
  rw [GlobalTheory.CompanionTheory.Ar.Pub.CxChart.setChartIdeal, GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal, hset]

theorem chartProj_finite : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → (∀ w, Ψ w 0 = w i) →
    (∀ J ∈ chartComponents (conePts Q) σ i, ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ)) →
    ∀ J ∈ chartComponents (conePts Q) σ i,
      GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J (chartProjMatrix σ Ψ) := by
  intro K _ _ ι _ Q e m σ i Ψ hQ hΨ hΨ0 hdim J hJ
  have hJm := GlobalTheory.CompanionTheory.Ar.Pub.CxChart.mem_chartComponents.1 hJ
  have hR : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q := hQ.2.1.2.1
  have hfin : (projHom J (chartProjMatrix σ Ψ)).toRingHom.Finite := by
    have hrad : originIdeal m ≤ (leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ)).radical := by
      refine Ideal.span_le.2 (Set.range_subset_iff.2 fun a => ?_)
      obtain ⟨r, hr⟩ := GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cone_pow_mem hR hΨ
        ((setChartIdeal_le_chartIdeal hΨ0).trans hJm.1.2) a
      exact ⟨r, hr⟩
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg_radical hrad (IsNoetherian.noetherian _)
    exact ConeAvoidsFinite.proof m e N J _ hN
  exact ⟨FiniteProjHomInjective.proof m e J _ hJm.1.1 (hdim J hJ) hfin, hfin⟩

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FinProj
end
end

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartComponents_finite_projection : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → (∀ w, Ψ w 0 = w i) →
    (∀ J ∈ chartComponents (conePts Q) σ i, ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ)) →
    ∀ J ∈ chartComponents (conePts Q) σ i,
      GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J (chartProjMatrix σ Ψ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FinProj.chartProj_finite
end

section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_density_integrable : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → (∀ j, IsSmoothHerm (L j)) →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) →
    (∀ w, Ψ w 0 = w i) → (∀ y, (setFibre (conePts Q) Ψ y).Finite) →
    GroundTheory.Heights₂.Heights.ComplexSets.zeroSet (GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal (conePts Q) σ i) =
      chartSet (conePts Q) σ i →
    (∀ J ∈ chartComponents (conePts Q) σ i, ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ)) →
    (∀ J ∈ chartComponents (conePts Q) σ i,
      GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J (chartProjMatrix σ Ψ)) →
    ∀ᵐ y, ∑ᶠ w ∈ setFibre (conePts Q) Ψ y, setSheetDensity (conePts Q) Ψ (pot L) g y w =
      ∑ J ∈ chartComponents (conePts Q) σ i,
        chartDens J (chartProjMatrix σ Ψ) (chartWeight σ i g) (chartPot σ i L) y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FibSum.fibreSum | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FibSum.fibreSum | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.FibSum.fibreSum <;> assumption)
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt
open ReciprocityTheory.AnForm.R (conePts)
open GroundTheory.Heights₂.Heights (chartLift chartLift_segre_apply)

namespace SecNotIn

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def chartMono (i : (k : K) → ι k) : MRingOver ℂ ι := ∏ k, X ⟨k, i k⟩

theorem eval_chartMono (i : (k : K) → ι k) (x : (Σ k, ι k) → ℂ) : eval x (chartMono i) = segre x i := by
  simp [chartMono, segre]

theorem eval_scale_eq_zero {Q : Ideal (MRingOver ℂ ι)} (hQ : IsMultiHomogIdeal Q)
    (c : K → ℂ) {x : (Σ k, ι k) → ℂ} (hx : ∀ f ∈ Q, eval x f = 0) :
    ∀ f ∈ Q, eval (fun q => c q.1 * x q) f = 0 := by
  obtain ⟨S, hS, rfl⟩ := hQ
  have hle : Ideal.span S ≤ RingHom.ker (eval (fun q : Σ k, ι k => c q.1 * x q)) := by
    rw [Ideal.span_le]
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    have h := ReciprocityTheory.AnForm.R.aeval_smul_of_isMultiHomog ha c x
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have h' : eval (fun q : Σ k, ι k => c q.1 * x q) f = (∏ k, c k ^ a k) * eval x f := h
    rw [h', hx f (Ideal.subset_span hf), mul_zero]
  exact fun f hf => hle hf

theorem mem_of_eval_eq_zero {Q : Ideal (MRingOver ℂ ι)} (hQp : Q.IsPrime) {i : (k : K) → ι k}
    (hw : chartMono i ∉ Q) {g : MRingOver ℂ ι}
    (h : ∀ x : (Σ k, ι k) → ℂ, (∀ f ∈ Q, eval x f = 0) → segre x i ≠ 0 → eval x g = 0) : g ∈ Q := by
  have hrad : g * chartMono i ∈ Q.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ), mem_vanishingIdeal_iff]
    intro x hx
    have hae : ∀ p : MvPolynomial (Σ k, ι k) ℂ, aeval x p = eval x p := fun _ => rfl
    rw [hae, map_mul, eval_chartMono]
    by_cases h0 : segre x i = 0
    · rw [h0, mul_zero]
    · rw [h x (fun f hf => by have := hx f hf; rwa [hae] at this) h0, zero_mul]
  rw [hQp.radical] at hrad
  exact (hQp.mem_or_mem hrad).resolve_right hw

def normAt (i : (k : K) → ι k) (x : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun q => (x ⟨q.1, i q.1⟩)⁻¹ * x q

theorem entry_ne_zero {i : (k : K) → ι k} {x : (Σ k, ι k) → ℂ} (h : segre x i ≠ 0) (k : K) :
    x ⟨k, i k⟩ ≠ 0 := fun h0 => h (Finset.prod_eq_zero (Finset.mem_univ k) h0)

theorem segre_normAt (i i' : (k : K) → ι k) (x : (Σ k, ι k) → ℂ) :
    segre (normAt i x) i' = segre x i' / segre x i := by
  simp only [segre, normAt, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  rw [div_eq_mul_inv, mul_comm]

theorem normAt_mem {Q : Ideal (MRingOver ℂ ι)} (hQ : IsMultiHomogIdeal Q)
    {i : (k : K) → ι k} {x : (Σ k, ι k) → ℂ} (hx : ∀ f ∈ Q, eval x f = 0) (h : segre x i ≠ 0) :
    normAt i x ∈ conePts Q :=
  ⟨fun k => ⟨i k, mul_ne_zero (inv_ne_zero (entry_ne_zero h k)) (entry_ne_zero h k)⟩,
    eval_scale_eq_zero hQ (fun k => (x ⟨k, i k⟩)⁻¹) hx⟩

theorem normAt_mem_chartSet {Q : Ideal (MRingOver ℂ ι)} (hQ : IsMultiHomogIdeal Q)
    {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) {i : (k : K) → ι k} {x : (Σ k, ι k) → ℂ}
    (hx : ∀ f ∈ Q, eval x f = 0) (h : segre x i ≠ 0) :
    (fun a => segre x (σ a) / segre x i) ∈ chartSet (conePts Q) σ i :=
  ⟨normAt i x, normAt_mem hQ hx h, by rw [segre_normAt, div_self h],
    funext fun a => (segre_normAt i (σ a) x).symm⟩

theorem exists_homogenise {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (f : MvPolynomial (Fin m) ℂ) :
    ∃ (F : MRingOver ℂ ι) (D : ℕ), ∀ x : (Σ k, ι k) → ℂ, segre x i ≠ 0 →
      eval x F = segre x i ^ D * eval (fun a => segre x (σ a) / segre x i) f := by
  induction f using MvPolynomial.induction_on with
  | C c => exact ⟨C c, 0, fun x _ => by simp⟩
  | add f g hf hg =>
    obtain ⟨F, D, hF⟩ := hf
    obtain ⟨G, E, hG⟩ := hg
    refine ⟨F * chartMono i ^ E + G * chartMono i ^ D, D + E, fun x hx => ?_⟩
    simp only [map_add, map_mul, map_pow, eval_chartMono, hF x hx, hG x hx]
    ring
  | mul_X f a hf =>
    obtain ⟨F, D, hF⟩ := hf
    refine ⟨F * chartMono (σ a), D + 1, fun x hx => ?_⟩
    simp only [map_mul, eval_chartMono, hF x hx, eval_X]
    field_simp
    ring

theorem chartIdeal_isPrime {Q : Ideal (MRingOver ℂ ι)} (hQp : Q.IsPrime)
    (hQh : IsMultiHomogIdeal Q) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    {i : (k : K) → ι k} (hw : chartMono i ∉ Q) (hne : chartIdeal (conePts Q) σ i ≠ ⊤) :
    (chartIdeal (conePts Q) σ i).IsPrime := by
  have back : ∀ (f : MvPolynomial (Fin m) ℂ) (F : MRingOver ℂ ι) (D : ℕ),
      (∀ x : (Σ k, ι k) → ℂ, segre x i ≠ 0 →
        eval x F = segre x i ^ D * eval (fun a => segre x (σ a) / segre x i) f) →
      F ∈ Q → f ∈ chartIdeal (conePts Q) σ i := by
    intro f F D hF hFQ
    rw [chartIdeal, mem_vanishingIdeal_iff]
    rintro _ ⟨z, hz, hz1, rfl⟩
    have h0 : segre z i ≠ 0 := by rw [hz1]; exact one_ne_zero
    have h := hF z h0
    rw [hz.2 F hFQ, hz1] at h
    simpa using h.symm
  refine ⟨hne, fun {f g} hfg => ?_⟩
  obtain ⟨F, D, hF⟩ := exists_homogenise σ i f
  obtain ⟨G, E, hG⟩ := exists_homogenise σ i g
  have hFG : F * G ∈ Q := mem_of_eval_eq_zero hQp hw fun x hx h0 => by
    have h1 : eval (fun a => segre x (σ a) / segre x i) (f * g) = 0 :=
      (mem_vanishingIdeal_iff.1 hfg) _ (normAt_mem_chartSet hQh σ hx h0)
    rw [map_mul] at h1
    rw [map_mul, hF x h0, hG x h0]
    linear_combination (segre x i ^ D * segre x i ^ E) * h1
  rcases hQp.mem_or_mem hFG with h | h
  · exact Or.inl (back f F D hF h)
  · exact Or.inr (back g G E hG h)

theorem eval_chartSection [DecidableEq K] {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (x : Fin m → ℂ) (s : MRingOver ℂ ι) : eval x (chartSection σ i s) = eval (chartLift σ i x) s := by
  induction s using MvPolynomial.induction_on with
  | C c => simp [chartSection]
  | add f g hf hg =>
    simp only [chartSection, map_add] at hf hg ⊢
    rw [hf, hg]
  | mul_X f q hf =>
    simp only [chartSection, map_mul, aeval_X, eval_X] at hf ⊢
    rw [hf]
    rfl

end SecNotIn

open SecNotIn in

theorem chartSection_notMem_component : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (s : MRingOver ℂ ι) (a : K → ℕ),
    IsCxVar Q e → IsMultiHomog s a → s ∉ Q →
    ∀ J ∈ chartComponents (conePts Q) σ i, chartSection σ i s ∉ J := by
  intro K _ _ ι _ Q e m σ i s a hQ hs hsQ J hJ hmem
  obtain ⟨-, ⟨hQp, hQh, -⟩, -⟩ := hQ
  have hJmin := mem_chartComponents.1 hJ
  have hprimeJ : J.IsPrime := hJmin.1.1
  have hne : chartIdeal (conePts Q) σ i ≠ ⊤ := fun h =>
    hprimeJ.ne_top (top_le_iff.1 (h ▸ hJmin.1.2))
  have hw : chartMono i ∉ Q := by
    intro hwQ
    apply hne
    rw [Ideal.eq_top_iff_one, chartIdeal, mem_vanishingIdeal_iff]
    rintro _ ⟨z, hz, hz1, rfl⟩
    have h0 := hz.2 _ hwQ
    rw [eval_chartMono, hz1] at h0
    exact absurd h0 one_ne_zero
  have hprime := chartIdeal_isPrime hQp hQh σ hw hne
  have hJI : J ≤ chartIdeal (conePts Q) σ i := hJmin.2 ⟨hprime, le_rfl⟩ hJmin.1.2
  have hI := hJI hmem
  apply hsQ
  refine mem_of_eval_eq_zero hQp hw fun x hx h0 => ?_
  have hz1 : segre (normAt i x) i = 1 := by rw [segre_normAt, div_self h0]
  have hpt : (fun a => segre (normAt i x) (σ a)) ∈ chartSet (conePts Q) σ i :=
    ⟨normAt i x, normAt_mem hQh hx h0, hz1, rfl⟩
  have h1 : eval (fun a => segre (normAt i x) (σ a)) (chartSection σ i s) = 0 :=
    (mem_vanishingIdeal_iff.1 hI) _ hpt
  have hlift : chartLift σ i (fun a => segre (normAt i x) (σ a)) = normAt i x := by
    funext ⟨k, j⟩
    rw [chartLift_segre_apply σ i _ hz1]
    have : normAt i x ⟨k, i k⟩ = 1 := inv_mul_cancel₀ (entry_ne_zero h0 k)
    rw [this, inv_one, mul_one]
  rw [eval_chartSection, hlift] at h1
  have hsc : eval (normAt i x) s = (∏ k, ((x ⟨k, i k⟩)⁻¹) ^ a k) * eval x s :=
    ReciprocityTheory.AnForm.R.aeval_smul_of_isMultiHomog (fun d hd k => hs d hd k)
      (fun k => (x ⟨k, i k⟩)⁻¹) x
  rw [hsc] at h1
  refine (mul_eq_zero.1 h1).resolve_left ?_
  exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (inv_ne_zero (entry_ne_zero h0 k))

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartSection_not_mem_components : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (s : MRingOver ℂ ι) (a : K → ℕ),
    IsCxVar Q e → IsMultiHomog s a → s ∉ Q →
    ∀ J ∈ chartComponents (conePts Q) σ i, chartSection σ i s ∉ J := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartSection_notMem_component
end

section
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open GroundTheory.Heights₂.Heights (chartLift chartLiftDom contDiff_chartLift chartLift_blockNonzero segre_chartLift
  chartWeight_of_coord)

section

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {m : ℕ}

theorem eval_chartSection (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (s : MRingOver ℂ ι)
    (x : Fin m → ℂ) : MvPolynomial.eval x (chartSection σ i s) = MvPolynomial.eval (chartLift σ i x) s := by
  induction s using MvPolynomial.induction_on with
  | C c => simp [chartSection]
  | add p q hp hq =>
    have : chartSection σ i (p + q) = chartSection σ i p + chartSection σ i q := by
      simp [chartSection]
    rw [this, map_add, map_add, hp, hq]
  | mul_X p q hp =>
    have : chartSection σ i (p * X q) =
        chartSection σ i p * X (σ.symm (Function.update i q.1 q.2)) := by
      simp [chartSection]
    rw [this, map_mul, map_mul, hp]
    simp [chartLift]

theorem mem_closedBall_of_lift_mem_domCell {S : Set ((Σ k, ι k) → ℂ)} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {x : Fin m → ℂ} (hx : x ∈ chartSet S σ i) (hd : chartLift σ i x ∈ domCell i) :
    x ∈ Metric.closedBall (0 : Fin m → ℂ) 1 := by
  obtain ⟨z, -, hzi, rfl⟩ := hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro a
  have h := hd (σ a)
  rw [segre_chartLift σ i z hzi, hzi, norm_one] at h
  exact h

theorem abs_log_div_le {t h c : ℝ} (ht : 0 ≤ t) (hh : 0 < h) (hc : |Real.log h| ≤ c) (hc0 : 0 ≤ c) :
    |Real.log (t / h)| ≤ |Real.log t| + c := by
  rcases ht.eq_or_lt with rfl | ht
  · simpa using hc0
  · rw [Real.log_div ht.ne' hh.ne']
    exact (abs_sub _ _).trans (by gcongr)

end

theorem integrable_chartAbsDens_cellWeight : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (N : Fin e → HermLine ι)
    (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ)
    (J : Ideal (MvPolynomial (Fin m) ℂ)),
    IsSmoothHerm A → (∀ k, A.a k = a k) → IsMultiHomog s a →
    Measurable ((domCell i).indicator (absLogNorm A s)) →
    GroundTheory.Heights₂.Heights.ComplexSets.zeroSet (GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal (conePts Q) σ i) =
      chartSet (conePts Q) σ i →
    J ∈ chartComponents (conePts Q) σ i →
    GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J (chartProjMatrix σ Ψ) →
    (∀ R C : ℝ, Integrable (chartAbsDens J (chartProjMatrix σ Ψ)
      ((Metric.closedBall 0 R).indicator fun x => |Real.log ‖MvPolynomial.eval x (chartSection σ i s)‖| + C)
      (chartPot σ i N))) →
    Integrable (chartAbsDens J (chartProjMatrix σ Ψ)
      (chartWeight σ i ((domCell i).indicator (absLogNorm A s))) (chartPot σ i N)) := by
  intro K _ _ ι _ Q e m σ i Ψ N A s a J hA _ _ hmeas hzero hJ hproj hint
  classical
  set T : Set (Fin m → ℂ) := Metric.closedBall 0 1 ∩ {x | x (σ.symm i) = 1} with hT
  have hTc : IsCompact T :=
    (isCompact_closedBall (0 : Fin m → ℂ) 1).inter_right
      (isClosed_eq (continuous_apply _) continuous_const)
  have hcont : ContinuousOn (fun x => Real.log (A.h (chartLift σ i x))) T := by
    have h1 : ContinuousOn (fun x => A.h (chartLift σ i x)) T :=
      hA.continuousOn.comp (contDiff_chartLift σ i (n := 0)).continuous.continuousOn
        fun x hx => chartLift_blockNonzero σ i hx.2
    exact h1.log fun x hx => (A.pos _ (chartLift_blockNonzero σ i hx.2)).ne'
  obtain ⟨C, hC⟩ := hTc.exists_bound_of_continuousOn hcont
  have hchart : ∀ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J, x ∈ chartSet (conePts Q) σ i := by
    intro x hx
    rw [← hzero]
    intro q hq
    exact hx q ((mem_chartComponents.1 hJ).1.2 hq)
  have hcoord : ∀ x ∈ chartSet (conePts Q) σ i, x (σ.symm i) = 1 := by
    rintro _ ⟨z, -, hzi, rfl⟩
    simpa using hzi
  have hmeasW : Measurable (chartWeight σ i ((domCell i).indicator (absLogNorm A s))) := by
    unfold chartWeight
    exact (hmeas.comp (contDiff_chartLift σ i (n := 0)).continuous.measurable).piecewise
      (GroundTheory.Heights₂.Heights.isOpen_chartLiftDom σ i).measurableSet measurable_const
  have hmeasD : Measurable (chartAbsDens J (chartProjMatrix σ Ψ)
      (chartWeight σ i ((domCell i).indicator (absLogNorm A s))) (chartPot σ i N)) :=
    GroundTheory.Heights₂.Heights.SheetSumMeasurable.measurable_sheetSum hproj (fun a b => |a * b|)
      ((continuous_mul.comp continuous_id).abs.measurable) hmeasW _
  refine (hint 1 (max C 0)).mono' hmeasD.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (GroundTheory.Heights₂.Heights.chartAbsDens_nonneg _ _ _ _ _)]
  have key : ∀ x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J,
      |chartWeight σ i ((domCell i).indicator (absLogNorm A s)) x| ≤
        |(Metric.closedBall (0 : Fin m → ℂ) 1).indicator
          (fun x => |Real.log ‖MvPolynomial.eval x (chartSection σ i s)‖| + max C 0) x| := by
    intro x hx
    have hxc := hchart x hx
    have h1 := hcoord x hxc
    rw [chartWeight_of_coord _ h1]
    by_cases hd : chartLift σ i x ∈ domCell i
    · have hb := mem_closedBall_of_lift_mem_domCell hxc hd
      have hC' : |Real.log (A.h (chartLift σ i x))| ≤ max C 0 :=
        (hC x ⟨hb, h1⟩).trans (le_max_left _ _)
      have hnz := chartLift_blockNonzero σ i h1
      have habs : absLogNorm A s (chartLift σ i x) = |logNormC A s (chartLift σ i x)| := by
        simp only [absLogNorm]
        rw [if_pos hnz]
      rw [Set.indicator_of_mem hd, Set.indicator_of_mem hb, habs, abs_abs, logNormC,
        ← eval_chartSection]
      exact (abs_log_div_le (norm_nonneg _) (A.pos _ hnz) hC' (le_max_right _ _)).trans
        (le_abs_self _)
    · rw [Set.indicator_of_notMem hd, abs_zero]
      exact abs_nonneg _
  have h := GroundTheory.Heights₂.Heights.sheetSum_le_mul (J := J) (A := chartProjMatrix σ Ψ) (y := y)
    (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hproj y) 1
    (fun x t => |chartWeight σ i ((domCell i).indicator (absLogNorm A s)) x *
      ReciprocityTheory.AnForm.maDens (fun k => chartPot σ i N k ∘ t) y|)
    (fun x t => |(Metric.closedBall (0 : Fin m → ℂ) 1).indicator
      (fun x => |Real.log ‖MvPolynomial.eval x (chartSection σ i s)‖| + max C 0) x *
      ReciprocityTheory.AnForm.maDens (fun k => chartPot σ i N k ∘ t) y|)
    (fun x hx t _ => by
      rw [one_mul, abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (key x hx.1) (abs_nonneg _))
  exact h.trans_eq (one_mul _)

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_domCell_logNorm_chart : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (N : Fin e → HermLine ι)
    (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ)
    (J : Ideal (MvPolynomial (Fin m) ℂ)),
    IsSmoothHerm A → (∀ k, A.a k = a k) → IsMultiHomog s a →
    Measurable ((domCell i).indicator (absLogNorm A s)) →
    GroundTheory.Heights₂.Heights.ComplexSets.zeroSet (GlobalTheory.CompanionTheory.Ar.Pub.CxChart.chartIdeal (conePts Q) σ i) =
      chartSet (conePts Q) σ i →
    J ∈ chartComponents (conePts Q) σ i →
    GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J (chartProjMatrix σ Ψ) →
    (∀ R C : ℝ, Integrable (chartAbsDens J (chartProjMatrix σ Ψ)
      ((Metric.closedBall 0 R).indicator fun x => |Real.log ‖MvPolynomial.eval x (chartSection σ i s)‖| + C)
      (chartPot σ i N))) →
    Integrable (chartAbsDens J (chartProjMatrix σ Ψ)
      (chartWeight σ i ((domCell i).indicator (absLogNorm A s))) (chartPot σ i N)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Pub.CxChart.integrable_chartAbsDens_cellWeight
end

section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.domCell_logNorm_measurable_invariant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ) (i : (k : K) → ι k),
    IsSmoothHerm A → (∀ k, A.a k = a k) → IsMultiHomog s a →
    Measurable ((domCell i).indicator (absLogNorm A s)) ∧
    ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      (domCell i).indicator (absLogNorm A s) (fun p => c p.1 * z p) =
        (domCell i).indicator (absLogNorm A s) z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cutWeight_measurable_invariant | exact GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cutWeight_measurable_invariant | (intros; apply GlobalTheory.CompanionTheory.Ar.Pub.CxChart.cutWeight_measurable_invariant <;> assumption)
end

section
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxTwist

theorem isSheet_bot_of_isSetSheet {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    {S : Set ((Σ k, ι k) → ℂ)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hS : ∀ z ∈ S, ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0) {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ}
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} (hγ : IsSetSheet S Ψ y w γ) : IsSheet ⊥ Ψ y w γ := by
  refine ⟨hγ.1, hγ.2.mono fun y' hy' => ⟨hy'.1, ⟨hS _ hy'.2.1, fun f hf => ?_⟩, hy'.2.2⟩⟩
  rw [Ideal.mem_bot.1 hf]
  simp

theorem exists_dominating_twist : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (e : ℕ) (L : Fin e → HermLine ι),
    (∀ j, IsSmoothHerm (L j)) →
    ∃ N : Fin e → HermLine ι, (∀ j, IsSmoothHerm (N j)) ∧
      ∀ (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
        (∀ z ∈ S, ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0) →
        (∀ (g : ((Σ k, ι k) → ℂ) → ℝ) y w, (∀ z, 0 ≤ g z) → 0 ≤ setSheetDensity S Ψ (pot N) g y w) ∧
        ∀ (g g' : ((Σ k, ι k) → ℂ) → ℝ) y w, (∀ z ∈ S, |g z| ≤ g' z) →
          |setSheetDensity S Ψ (pot L) g y w| ≤ 3 ^ e * setSheetDensity S Ψ (pot N) g' y w := by
  intro K _ ι _ e L hL
  classical
  choose T hTs hTp hLTp using fun j =>
    GroundTheory.Heights₂.Heights.Inter.SemiPosTwist.proof GroundTheory.Heights₂.Heights.Inter.TorusInvLevi.proof K ι (L j) (hL j)
  have hLT : ∀ j, IsSmoothHerm ((L j).tensor (T j)) := fun j => isSmoothHerm_tensor (hL j) (hTs j)
  refine ⟨fun j => ((L j).tensor (T j)).tensor (T j), fun j => isSmoothHerm_tensor (hLT j) (hTs j), ?_⟩
  intro S Ψ hS
  have hab : ∀ {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ},
      IsSetSheet S Ψ y w γ → |maDensity (fun j y' => pot L j (γ y')) y| ≤
        3 ^ e * maDensity (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (γ y')) y :=
    fun hγ => GroundTheory.Heights₂.Heights.Inter.PointsAbsIntegrable.abs_maDensity_le hL hTs hTp hLTp
      (isSheet_bot_of_isSetSheet hS hγ)
  have hnn : ∀ {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ},
      IsSetSheet S Ψ y w γ →
        0 ≤ maDensity (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (γ y')) y :=
    fun hγ => nonneg_of_mul_nonneg_right ((abs_nonneg _).trans (hab hγ)) (by positivity)
  refine ⟨fun g y w hg => ?_, fun g g' y w hgg => ?_⟩
  · unfold setSheetDensity
    split_ifs with hγ
    · exact mul_nonneg (hg _) (hnn hγ.choose_spec)
    · exact le_rfl
  · unfold setSheetDensity
    by_cases hγ : ∃ γ, IsSetSheet S Ψ y w γ
    · rw [dif_pos hγ, dif_pos hγ]
      have hs := hγ.choose_spec
      have hmem : hγ.choose y ∈ S := hs.2.self_of_nhds.2.1
      have hg := hgg _ hmem
      rw [abs_mul]
      calc |g (hγ.choose y)| * |maDensity (fun j y' => pot L j (hγ.choose y')) y|
          ≤ g' (hγ.choose y) * (3 ^ e * maDensity
              (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (hγ.choose y')) y) :=
            mul_le_mul hg (hab hs) (abs_nonneg _) ((abs_nonneg _).trans hg)
        _ = 3 ^ e * (g' (hγ.choose y) * maDensity
              (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (hγ.choose y')) y) := by ring
    · rw [dif_neg hγ, dif_neg hγ]
      simp

end GlobalTheory.CompanionTheory.Ar.Pub.CxTwist
end
end

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_metrics_nonneg_density : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (e : ℕ) (L : Fin e → HermLine ι),
    (∀ j, IsSmoothHerm (L j)) →
    ∃ N : Fin e → HermLine ι, (∀ j, IsSmoothHerm (N j)) ∧
      ∀ (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
        (∀ z ∈ S, ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0) →
        (∀ (g : ((Σ k, ι k) → ℂ) → ℝ) y w, (∀ z, 0 ≤ g z) → 0 ≤ setSheetDensity S Ψ (pot N) g y w) ∧
        ∀ (g g' : ((Σ k, ι k) → ℂ) → ℝ) y w, (∀ z ∈ S, |g z| ≤ g' z) →
          |setSheetDensity S Ψ (pot L) g y w| ≤ 3 ^ e * setSheetDensity S Ψ (pot N) g' y w := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Pub.CxTwist.exists_dominating_twist
end

section
section
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)
open GlobalTheory.CompanionTheory.Ar.Pub.CxChart (chartSet chartComponents chartSection domCell absLogNorm)
open GroundTheory.Heights₂.Heights (chartProjMatrix chartWeight chartPot chartDens chartAbsDens)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

section Assembly

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem setSheetDensity_eq_zero {e : ℕ} {S : Set ((Σ k, ι k) → ℂ)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : ∀ z ∈ S, g z = 0) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) : setSheetDensity S Ψ φ g y w = 0 := by
  unfold setSheetDensity
  split_ifs with hγ
  · rw [hg _ hγ.choose_spec.2.self_of_nhds.2.1, zero_mul]
  · rfl

theorem setSheetDensity_sum {e : ℕ} {S : Set ((Σ k, ι k) → ℂ)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {τ : Type*} (t : Finset τ) (G : τ → ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) :
    setSheetDensity S Ψ φ (fun z => ∑ i ∈ t, G i z) y w = ∑ i ∈ t, setSheetDensity S Ψ φ (G i) y w := by
  unfold setSheetDensity
  split_ifs with hγ
  · rw [Finset.sum_mul]
  · simp

theorem exists_mem_domCell [DecidableEq K] {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0) :
    ∃ i, z ∈ domCell i := by
  choose i1 _ using hz
  have : Nonempty ((k : K) → ι k) := ⟨i1⟩
  obtain ⟨i, hi⟩ := Finite.exists_max fun i' : (k : K) → ι k => ‖segre z i'‖
  exact ⟨i, hi⟩

theorem segre_ne_zero_of_mem_domCell {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0)
    {i : (k : K) → ι k} (hi : z ∈ domCell i) : segre z i ≠ 0 := by
  choose i1 hi1 using hz
  have h1 : segre z i1 ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hi1 k
  intro h0
  have := hi i1
  rw [h0, norm_zero] at this
  exact h1 (norm_le_zero_iff.1 this)

end Assembly

theorem cell_mass_lt_top {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Q : Ideal (MRingOver ℂ ι)} {e : ℕ} {i : (k : K) → ι k}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {N : Fin e → HermLine ι}
    {A : HermLine ι} {s : MRingOver ℂ ι} {a : K → ℕ}
    (hQ : IsCxVar Q e) (hΨ : IsSetGoodProj (conePts Q) Ψ) (hΨ0 : ∀ w, Ψ w 0 = w i)
    (hN : ∀ j, IsSmoothHerm (N j)) (hA : IsSmoothHerm A) (hAa : ∀ k, A.a k = a k)
    (hs : IsMultiHomog s a) (hsQ : s ∉ Q)
    (hnn : ∀ y w, 0 ≤ setSheetDensity (conePts Q) Ψ (pot N) ((domCell i).indicator (absLogNorm A s)) y w) :
    ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot N) ((domCell i).indicator (absLogNorm A s)) y) < ⊤ := by
  classical
  set σ : Fin (Fintype.card ((k : K) → ι k)) ≃ ((k : K) → ι k) := (Fintype.equivFin _).symm with hσ
  set G := (domCell i).indicator (absLogNorm A s) with hG
  obtain ⟨hGm, hGi⟩ := GlobalTheory.T.domCell_logNorm_measurable_invariant K ι A s a i hA hAa hs
  have hzero := GlobalTheory.T.zeroSet_chartIdeal_eq_chartSet K ι Q _ σ i hQ.2.1.2.1
  have hdim := GlobalTheory.T.ringKrullDim_chartComponents K ι Q e _ σ i hQ
  have hfin := GlobalTheory.T.chartComponents_finite_projection K ι Q e _ σ i Ψ hQ hΨ hΨ0 hdim
  have hfs := GlobalTheory.T.chart_density_integrable K ι Q e _ σ i N G Ψ hQ hN hGi hΨ0 (GlobalTheory.T.setFibre_finite_of_goodProj K ι Q e Ψ hQ hΨ) hzero hdim hfin
  have hsm : ∀ j, ∀ J ∈ chartComponents (conePts Q) σ i, GroundTheory.Heights₂.Heights.SmoothNear
      (GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J) (chartPot σ i N j) := fun j J hJ =>
    GroundTheory.Heights₂.Heights.smoothNear_chartPot σ i hN (fun x hx => by
      have hx' : x ∈ chartSet (conePts Q) σ i := by
        rw [← hzero]
        exact fun q hq => hx q ((mem_chartComponents.1 hJ).1.2 hq)
      obtain ⟨z, -, hzi, rfl⟩ := hx'
      simpa using hzi) j
  have hint : Integrable (fun y => ∑ J ∈ chartComponents (conePts Q) σ i,
      chartAbsDens J (chartProjMatrix σ Ψ) (chartWeight σ i G) (chartPot σ i N) y) :=
    integrable_finset_sum _ fun J hJ =>
      GlobalTheory.T.integrable_domCell_logNorm_chart K ι Q e _ σ i Ψ N A s a J hA hAa hs hGm hzero hJ (hfin J hJ) fun R C =>
        GlobalTheory.T.integrable_chartAbsDensity _ e J _ _ _ R C (mem_chartComponents.1 hJ).1.1 (hdim J hJ) (hfin J hJ)
          (GlobalTheory.T.chartSection_not_mem_components K ι Q e _ σ i s a hQ hs hsQ J hJ) fun j => hsm j J hJ
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) hint.lintegral_lt_top
  filter_upwards [hfs] with y hy
  refine ENNReal.ofReal_le_ofReal ?_
  have hpos : cxPosDens (conePts Q) Ψ (pot N) G y =
      ∑ᶠ w ∈ setFibre (conePts Q) Ψ y, setSheetDensity (conePts Q) Ψ (pot N) G y w := by
    unfold cxPosDens
    exact finsum_congr fun w => finsum_congr fun _ => max_eq_left (hnn y w)
  rw [hpos, hy]
  exact Finset.sum_le_sum fun J _ =>
    GroundTheory.Heights₂.Heights.PtsSemiPosMassFinite.chartDens_le_chartAbsDens _ _ _ _ _

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open GlobalTheory.CompanionTheory.Ar.Pub.CxChart in

theorem GlobalTheory.CompanionTheory.Ar.Pub.CxChart.logNorm_mass_lt_top : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    (∀ k, A.a k = a k) → IsMultiHomog s a → s ∉ Q →
    ∫⁻ y, ENNReal.ofReal (∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|) < ⊤ := by
  intro K _ ι _ Q e Ψ L A s a hQ hΨ hL hA hAa hs hsQ
  classical
  obtain ⟨N, hN, hTw⟩ := GlobalTheory.T.exists_smooth_metrics_nonneg_density K ι e L hL
  obtain ⟨hnn, hbd⟩ := hTw (conePts Q) Ψ fun z hz => hz.1
  set G : ((k : K) → ι k) → ((Σ k, ι k) → ℂ) → ℝ := fun i => (domCell i).indicator (absLogNorm A s) with hG
  have hG0 : ∀ i z, 0 ≤ G i z := fun i z => Set.indicator_nonneg (fun z _ => by
    unfold absLogNorm
    split_ifs
    · exact abs_nonneg _
    · exact le_rfl) z
  have hWm := fun i => GlobalTheory.T.domCell_logNorm_measurable_invariant K ι A s a i hA hAa hs
  have hcell : ∀ i, ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot N) (G i) y) < ⊤ := by
    intro i
    by_cases hi : ∃ z ∈ conePts Q, segre z i ≠ 0
    · obtain ⟨Ψ', hΨ', hΨ0⟩ := GlobalTheory.T.exists_goodProj_first_coordinate K ι Q e i hQ hi
      rw [GlobalTheory.T.integral_density_independent_projection K ι Q e Ψ Ψ' N (G i) hQ hΨ hΨ' hN (hWm i).1 (hWm i).2]
      exact cell_mass_lt_top hQ hΨ' hΨ0 hN hA hAa hs hsQ fun y w => (hTw (conePts Q) Ψ' fun z hz => hz.1).1 _ y w (hG0 i)
    · have h0 : ∀ z ∈ conePts Q, G i z = 0 := fun z hz => Set.indicator_of_notMem (fun hzi =>
        hi ⟨z, hz, segre_ne_zero_of_mem_domCell hz.1 hzi⟩) _
      have : ∀ y, cxPosDens (conePts Q) Ψ (pot N) (G i) y = 0 := fun y => by
        unfold cxPosDens
        simp [setSheetDensity_eq_zero (pot N) h0]
      simp [this]
  have hfib := GlobalTheory.T.setFibre_finite_of_goodProj K ι Q e Ψ hQ hΨ
  have hcov : ∀ z ∈ conePts Q, |logNormC A s z| ≤ ∑ i, G i z := by
    intro z hz
    obtain ⟨i, hi⟩ := exists_mem_domCell hz.1
    have : |logNormC A s z| = G i z := by
      simp only [hG, Set.indicator_of_mem hi, absLogNorm, if_pos hz.1]
    rw [this]
    exact Finset.single_le_sum (f := fun i => G i z) (fun i _ => hG0 i z) (Finset.mem_univ i)
  have hpt : ∀ y, ENNReal.ofReal (∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|) ≤
      ENNReal.ofReal (3 ^ e) * ∑ i, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot N) (G i) y) := by
    intro y
    have hnnd : ∀ i, 0 ≤ cxPosDens (conePts Q) Ψ (pot N) (G i) y := fun i =>
      finsum_nonneg fun w => finsum_nonneg fun _ => le_max_right _ _
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hnnd i, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold cxPosDens
    simp only [finsum_mem_eq_finite_toFinset_sum _ (hfib y)]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun w _ => ?_
    refine (hbd _ (fun z => ∑ i, G i z) y w hcov).trans ?_
    rw [setSheetDensity_sum]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => le_max_left _ _) (by positivity)
  calc ∫⁻ y, ENNReal.ofReal (∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
        |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|)
      ≤ ∫⁻ y, ENNReal.ofReal (3 ^ e) * ∑ i, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot N) (G i) y) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (3 ^ e) * ∑ i, ∫⁻ y, ENNReal.ofReal (cxPosDens (conePts Q) Ψ (pot N) (G i) y) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_finset_sum' _ fun i _ =>
          (GlobalTheory.T.aemeasurable_cxPosDensity K ι Q e Ψ N (G i) hQ hΨ hN (hWm i).1 (hWm i).2).ennreal_ofReal]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.sum_lt_top.2 fun i _ => hcell i)
end
end

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt GlobalTheory.CompanionTheory.Ar.Pub.CxComp Filter Topology
open ReciprocityTheory.AnForm.R (conePts)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_fibre_logNorm_finite : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRingOver ℂ ι) (a : K → ℕ),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    (∀ k, A.a k = a k) → IsMultiHomog s a → s ∉ Q →
    ∫⁻ y, ENNReal.ofReal (∑ᶠ w ∈ setFibre (conePts Q) Ψ y,
      |setSheetDensity (conePts Q) Ψ (pot L) (logNormC A s) y w|) < ⊤ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Pub.CxChart.logNorm_mass_lt_top
end
