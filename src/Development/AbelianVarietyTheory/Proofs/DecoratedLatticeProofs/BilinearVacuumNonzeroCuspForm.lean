import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBiThetaIffJoin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactAverageSmoothFamilyClosedUnderDerivatives
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralFundamentalDomainRightTranslateInvariStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorIntegralCommOfBoundedFiniteMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegralCompactAutomorphicQuotientParaStatement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaHeisenbergDeriv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOneParamDerivOrthDecJoinedEqSum
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMultTOfEquivariant

section
section
open MeasureTheory
open scoped ContDiff

noncomputable section

namespace GlobalTheory.AvgSmooth

variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] {n : ℕ}

theorem integrable_cont (μ : Measure K) [IsFiniteMeasure μ] {f : K → ℂ} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun k => hC k (Set.mem_univ k))

def coordC (n : ℕ) (i : Fin n) : (Fin n → ℝ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).smulRight (1 : ℂ)

theorem clm_expand (L : (Fin n → ℝ) →L[ℝ] ℂ) : L = ∑ i, L (Pi.single i 1) • coordC n i := by
  ext1 u
  have e : L u = ∑ i, u i • L (Pi.single i 1) := by
    conv_lhs => rw [← Finset.univ_sum_single u]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_smul]
    congr 1
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [e]
  simp [coordC, ContinuousLinearMap.sum_apply, Complex.real_smul, mul_comm]

theorem hasFDerivAt_avg (μ : Measure K) [IsFiniteMeasure μ] {F : K → (Fin n → ℝ) → ℂ}
    {G : Fin n → K → (Fin n → ℝ) → ℂ} (hF : Continuous fun p : K × (Fin n → ℝ) => F p.1 p.2)
    (hG : ∀ i, Continuous fun p : K × (Fin n → ℝ) => G i p.1 p.2) (hd : ∀ k, Differentiable ℝ (F k))
    (he : ∀ i k t, fderiv ℝ (F k) t (Pi.single i 1) = G i k t) (t₀ : Fin n → ℝ) :
    HasFDerivAt (fun t => ∫ k, F k t ∂μ) (∑ i, (∫ k, G i k t₀ ∂μ) • coordC n i) t₀ := by
  have hFk : ∀ t, Continuous fun k => F k t := fun t => hF.comp (continuous_id.prodMk continuous_const)
  have hGk : ∀ i t, Continuous fun k => G i k t := fun i t => (hG i).comp (continuous_id.prodMk continuous_const)
  have hM : ∀ i, ∃ M : ℝ, ∀ p ∈ (Set.univ : Set K) ×ˢ Metric.closedBall t₀ 1, ‖G i p.1 p.2‖ ≤ M := fun i =>
    (isCompact_univ.prod (isCompact_closedBall t₀ 1)).exists_bound_of_continuousOn (hG i).continuousOn
  choose M hM using hM
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ)
    (F := fun t k => F k t) (F' := fun t k => ∑ i, G i k t • coordC n i)
    (bound := fun _ => ∑ i, M i * ‖coordC n i‖) (Metric.ball_mem_nhds t₀ one_pos)
    (Filter.Eventually.of_forall fun t => (hFk t).aestronglyMeasurable)
    (integrable_cont μ (hFk t₀))
    (Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hGk i t₀).aestronglyMeasurable.smul_const _)
    (Filter.Eventually.of_forall fun k t ht => by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_smul]
      gcongr
      exact hM i (k, t) ⟨Set.mem_univ _, Metric.ball_subset_closedBall ht⟩)
    (integrable_const _)
    (Filter.Eventually.of_forall fun k t _ => by
      have h := (hd k t).hasFDerivAt
      rw [clm_expand (fderiv ℝ (F k) t)] at h
      simpa only [he] using h)
  refine key.congr_fderiv ?_
  rw [integral_finset_sum _ fun i _ => (integrable_cont μ (hGk i t₀)).smul_const _]
  exact Finset.sum_congr rfl fun i _ => integral_smul_const _ _

end GlobalTheory.AvgSmooth

open GlobalTheory.AvgSmooth in

theorem GlobalTheory.AvgSmooth.main : ∀ (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (n : ℕ) (φ : Fin n → (Fin n → ℝ) → ℂ), (∀ i, ContDiff ℝ ∞ (φ i)) → ∀ 𝒢 : Set (K → (Fin n → ℝ) → ℂ), (∀ F ∈ 𝒢, Continuous fun p : K × (Fin n → ℝ) => F p.1 p.2) → (∀ F ∈ 𝒢, ∀ k, Differentiable ℝ (F k)) → (∀ F ∈ 𝒢, ∀ i, ∃ F' ∈ 𝒢, ∀ k t, fderiv ℝ (F k) t (Pi.single i 1) = F' k t + φ i t * F k t) → ∀ F ∈ 𝒢, ContDiff ℝ ∞ fun t => ∫ k, F k t ∂μ := by
  intro K _ _ _ _ μ _ n φ hφ 𝒢 hc hd hder
  have hk : ∀ F ∈ 𝒢, ∀ t, Integrable (fun k => F k t) μ := fun F hF t =>
    integrable_cont μ ((hc F hF).comp (continuous_id.prodMk continuous_const))
  have hD : ∀ F ∈ 𝒢, ∃ F' : Fin n → K → (Fin n → ℝ) → ℂ, (∀ i, F' i ∈ 𝒢) ∧ ∀ t₀,
      HasFDerivAt (fun t => ∫ k, F k t ∂μ)
        (∑ i, ((∫ k, F' i k t₀ ∂μ) + φ i t₀ * ∫ k, F k t₀ ∂μ) • coordC n i) t₀ := by
    intro F hF
    choose F' hF' he using hder F hF
    refine ⟨F', hF', fun t₀ => ?_⟩
    have h := hasFDerivAt_avg μ (G := fun i k t => F' i k t + φ i t * F k t) (hc F hF)
      (fun i => (hc _ (hF' i)).add (((hφ i).continuous.comp continuous_snd).mul (hc F hF))) (hd F hF) he t₀
    refine h.congr_fderiv (Finset.sum_congr rfl fun i _ => ?_)
    rw [integral_add (hk _ (hF' i) t₀) ((hk F hF t₀).const_mul _), integral_const_mul]
  have main : ∀ m : ℕ, ∀ F ∈ 𝒢, ContDiff ℝ m fun t => ∫ k, F k t ∂μ := by
    intro m
    induction m with
    | zero =>
      intro F hF
      obtain ⟨F', -, h⟩ := hD F hF
      exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun t => (h t).continuousAt)
    | succ m ih =>
      intro F hF
      obtain ⟨F', hF', h⟩ := hD F hF
      rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by norm_cast, contDiff_succ_iff_hasFDerivAt]
      refine ⟨_, ?_, h⟩
      refine ContDiff.sum fun i _ => ContDiff.smul_const ?_ _
      exact (ih _ (hF' i)).add ((contDiff_infty.1 (hφ i) m).mul (ih F hF))
  intro F hF
  exact contDiff_infty.2 fun m => main m F hF

end
end

open MeasureTheory
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_compactAverage_of_closed_partials : ∀ (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (n : ℕ) (φ : Fin n → (Fin n → ℝ) → ℂ), (∀ i, ContDiff ℝ ∞ (φ i)) → ∀ 𝒢 : Set (K → (Fin n → ℝ) → ℂ), (∀ F ∈ 𝒢, Continuous fun p : K × (Fin n → ℝ) => F p.1 p.2) → (∀ F ∈ 𝒢, ∀ k, Differentiable ℝ (F k)) → (∀ F ∈ 𝒢, ∀ i, ∃ F' ∈ 𝒢, ∀ k t, fderiv ℝ (F k) t (Pi.single i 1) = F' k t + φ i t * F k t) → ∀ F ∈ 𝒢, ContDiff ℝ ∞ fun t => ∫ k, F k t ∂μ := by
  atlas_forward_decl GlobalTheory.AvgSmooth.main
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaAvgSmooth

open GlobalTheory.WeilVacMove

theorem key {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {lam : AF D.host.F →+ ℂ} (hl : Continuous lam)
    (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a)) {n : ℕ} (L : (Fin n → ℝ) →+ WO S T)
    (hL : Continuous L) (hL0 : ∀ t, (L t).map (finPart D) = 0) (w : WO S T) (f : WO S T → ℂ)
    (hf : IsThetaFunO ψ S T f) (t : Fin n → ℝ) (i : Fin n) :
    fderiv ℝ (fun t => f (w + L t)) t (Pi.single i 1) =
      dLine ψ S T (L.comp (AddMonoidHom.single (fun _ : Fin n => ℝ) i)) f (w + L t) +
        -phase lam S T (L.comp (AddMonoidHom.single (fun _ : Fin n => ℝ) i) 1) (w + L t) * f (w + L t) := by
  set M := L.comp (AddMonoidHom.single (fun _ : Fin n => ℝ) i) with hMdef
  have hs : Continuous (AddMonoidHom.single (fun _ : Fin n => ℝ) i) := by
    refine continuous_pi fun j => ?_
    by_cases h : j = i
    · subst h; simp; exact continuous_id'
    · simpa [h] using continuous_const
  have hM : Continuous M := hL.comp hs
  have hM0 : ∀ s, (M s).map (finPart D) = 0 := fun s => hL0 _
  set x := w + L t with hx
  set c := phase lam S T (M 1) x with hc
  obtain ⟨hd, -⟩ := hasDerivAt_zero_and_isTheta hψ hM hM0 hf
  have hexp : HasDerivAt (fun s : ℝ => Complex.exp (-((s : ℂ) * c))) (-c) 0 := by
    have := ((HasDerivAt.ofReal_comp (hasDerivAt_id (0 : ℝ))).mul_const c).neg.cexp
    simpa using this
  have h1 := hexp.mul (hd x)
  have hsm : ∀ s : ℝ, s • (Pi.single i (1 : ℝ) : Fin n → ℝ) = Pi.single i s := by
    intro s
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  have e1 : ∀ s : ℝ, Complex.exp (-((s : ℂ) * c)) * heisO ψ S T (M s) f x =
      f (w + L (t + s • Pi.single i 1)) := by
    intro s
    rw [heisO, psi_sympl_line hl hlam hM hM0, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero,
      one_mul, hsm, map_add, hx, add_assoc]
    rfl
  have hg : DifferentiableAt ℝ (fun t => f (w + L t)) (t + (0 : ℝ) • Pi.single i 1) :=
    ((hf.smooth n L hL hL0 w).differentiable (by simp)).differentiableAt
  have hl' : HasDerivAt (fun s : ℝ => t + s • (Pi.single i (1 : ℝ) : Fin n → ℝ)) (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ) : Fin n → ℝ)).const_add t
  have h2 := hg.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl'
  rw [zero_smul, add_zero] at h2
  have h3 : HasDerivAt (fun s : ℝ => f (w + L (t + s • Pi.single i 1)))
      (-c * heisO ψ S T (M 0) f x + Complex.exp (-(((0 : ℝ) : ℂ) * c)) * dLine ψ S T M f x) 0 := by
    have e : (fun s : ℝ => f (w + L (t + s • Pi.single i 1))) =
        fun s : ℝ => Complex.exp (-((s : ℂ) * c)) * heisO ψ S T (M s) f x := funext fun s => (e1 s).symm
    rw [e]
    exact h1
  have := h2.unique h3
  rw [this, map_zero, GlobalTheory.WeilVacMove.heisO_zero]
  simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul]
  ring

theorem avg_smooth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (𝒢 : Set (K → WO S T → ℂ)), (∀ F ∈ 𝒢, Continuous fun p : K × WO S T => F p.1 p.2) → (∀ F ∈ 𝒢, ∀ k, IsThetaFunO ψ S T (F k)) → (∀ F ∈ 𝒢, ∀ M : ℝ →+ WO S T, Continuous M → (∀ s, (M s).map (finPart D) = 0) → (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (F k)) ∈ 𝒢) → ∀ F ∈ 𝒢, ∀ (n : ℕ) (L : (Fin n → ℝ) →+ WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ∞ fun t => ∫ k, F k (w + L t) ∂μ := by
  intro D ψ hψ S T K _ _ _ _ μ _ 𝒢 hc hth hcl F hF n L hL hL0 w
  obtain ⟨lam, hl, hlam⟩ := exists_log hψ
  have hs : ∀ i, Continuous (AddMonoidHom.single (fun _ : Fin n => ℝ) i) := by
    intro i
    refine continuous_pi fun j => ?_
    by_cases h : j = i
    · subst h; simp; exact continuous_id'
    · simpa [h] using continuous_const
  let M : Fin n → ℝ →+ WO S T := fun i => L.comp (AddMonoidHom.single (fun _ : Fin n => ℝ) i)
  have hM : ∀ i, Continuous (M i) := fun i => hL.comp (hs i)
  have hM0 : ∀ i s, (M i s).map (finPart D) = 0 := fun i s => hL0 _
  let φ : Fin n → (Fin n → ℝ) → ℂ := fun i t => -phase lam S T (M i 1) (w + L t)
  let 𝒢' : Set (K → (Fin n → ℝ) → ℂ) := {G | ∃ F ∈ 𝒢, G = fun k t => F k (w + L t)}
  have hφ : ∀ i, ContDiff ℝ ∞ (φ i) := by
    intro i
    have hc' : Continuous ((phase lam S T (M i 1)).comp L) :=
      hl.comp (continuous_symplOH S T hL continuous_const)
    have e : φ i = fun t => -(phase lam S T (M i 1) w + ((phase lam S T (M i 1)).comp L) t) := by
      funext t
      simp only [φ, map_add, AddMonoidHom.comp_apply]
    rw [e]
    exact (contDiff_const.add (contDiff_additive _ hc')).neg
  have hmem : (fun k t => F k (w + L t)) ∈ 𝒢' := ⟨F, hF, rfl⟩
  refine GlobalTheory.T.contDiff_compactAverage_of_closed_partials K μ n φ hφ 𝒢' ?_ ?_ ?_ _ hmem
  · rintro G ⟨F, hF, rfl⟩
    exact (hc F hF).comp (continuous_fst.prodMk (continuous_const.add (hL.comp continuous_snd)))
  · rintro G ⟨F, hF, rfl⟩ k
    exact ((hth F hF k).smooth n L hL hL0 w).differentiable (by simp)
  · rintro G ⟨F, hF, rfl⟩ i
    refine ⟨fun k t => GlobalTheory.WeilVacMove.dLine ψ S T (M i) (F k) (w + L t), ⟨_, hcl F hF (M i) (hM i) (hM0 i), rfl⟩,
      fun k t => ?_⟩
    exact GlobalTheory.ThetaAvgSmooth.key hψ hl hlam L hL hL0 w (F k) (hth F hF k) t i

end GlobalTheory.ThetaAvgSmooth
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactAverage_thetaFamily_smooth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (𝒢 : Set (K → WO S T → ℂ)), (∀ F ∈ 𝒢, Continuous fun p : K × WO S T => F p.1 p.2) → (∀ F ∈ 𝒢, ∀ k, IsThetaFunO ψ S T (F k)) → (∀ F ∈ 𝒢, ∀ M : ℝ →+ WO S T, Continuous M → (∀ s, (M s).map (finPart D) = 0) → (fun k => GlobalTheory.WeilVacMove.dLine ψ S T M (F k)) ∈ 𝒢) → ∀ F ∈ 𝒢, ∀ (n : ℕ) (L : (Fin n → ℝ) →+ WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ∞ fun t => ∫ k, F k (w + L t) ∂μ := by
  first | exact @GlobalTheory.ThetaAvgSmooth.avg_smooth | exact GlobalTheory.ThetaAvgSmooth.avg_smooth | (intros; apply GlobalTheory.ThetaAvgSmooth.avg_smooth <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOneParamDeriv_orthDecJoined_eq_sum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (W A S A' : HSp D) (d : OrthDec W A (GlobalTheory.ChiGrid.negSp A')) (G : WO A S → WO S A' → ℂ), IsBiTheta ψ A S A' G → ∀ M : ℝ →+ WO W S, Continuous M → (∀ s, (M s).map (finPart D) = 0) → (∀ s, (GlobalTheory.BiTransfer.fstH d S (M s)).map (finPart D) = 0) ∧ (∀ s, (GlobalTheory.BiTransfer.sndH d S (M s)).map (finPart D) = 0) ∧ GlobalTheory.WeilVacMove.dLine ψ W S M (GlobalTheory.BiTransfer.join d S G) = GlobalTheory.BiTransfer.join d S fun u v => GlobalTheory.WeilVacMove.dLine ψ A S ((GlobalTheory.BiTransfer.fstH d S).comp M) (fun u' => G u' v) u + GlobalTheory.WeilVacMove.dLine ψ S A' ((GlobalTheory.BiTransfer.sndH d S).comp M) (G u) v := by
  first | exact @GlobalTheory.BiJoinDeriv.dLine_join | exact GlobalTheory.BiJoinDeriv.dLine_join | (intros; apply GlobalTheory.BiJoinDeriv.dLine_join <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DerivComm

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem exists_biBound (hψ : IsStdChar D ψ (-1)) {A S A' : HSp D} {C : WO A S → WO S A' → ℂ}
    (h : IsBiTheta ψ A S A' C) : ∃ B : ℝ, ∀ u v, ‖C u v‖ ≤ B := by
  obtain ⟨B, hB⟩ := GlobalTheory.WeilVacMove.exists_bound hψ
    (GlobalTheory.BiTransfer.isThetaFunO_join (GlobalTheory.BiTransfer.sumDec A (GlobalTheory.ChiGrid.negSp A')) h)
  refine ⟨B, fun u v => ?_⟩
  have := hB (GlobalTheory.BiTransfer.inlH (GlobalTheory.BiTransfer.sumDec A (GlobalTheory.ChiGrid.negSp A')) S u +
    GlobalTheory.BiTransfer.inrH (GlobalTheory.BiTransfer.sumDec A (GlobalTheory.ChiGrid.negSp A')) S v)
  rwa [GlobalTheory.BiTransfer.join_inl_inr] at this

theorem om_dLine_right : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (χA χS χS' χA' : (AE D)ˣ →* Circle) (oma : Om A S) (omb : Om S A'), IsWeilDatumO ψ A S χA χS oma → IsWeilDatumO ψ S A' χS' χA' omb → BiAct D → ∀ G : WO A S → WO S A' → ℂ, IsBiTheta ψ A S A' G → ∀ M' : ℝ →+ WO S A', Continuous M' → (∀ s, (M' s).map (finPart D) = 0) → ∀ p u v, oma p (fun u' => GlobalTheory.WeilVacMove.dLine ψ S A' M' (G u') v) u = GlobalTheory.WeilVacMove.dLine ψ S A' M' (fun v' => oma p (fun u' => G u' v') u) v := by
  intro D ψ A S A' χA χS χS' χA' oma omb hA hB hBi G hG M' hM hM0 p u v
  have hψ : IsStdChar D ψ (-1) := hA.std
  set G' : WO A S → WO S A' → ℂ := fun u v => GlobalTheory.WeilVacMove.dLine ψ S A' M' (G u) v with hG'def
  have hG' : IsBiTheta ψ A S A' G' := (GlobalTheory.T.isJointlySmoothBiTheta_heisenbergDeriv D ψ hψ A S A' G hG).2 M' hM hM0
  set H : WO A S → WO S A' → ℂ := fun u v => oma p (fun u' => G u' v) u with hHdef
  have hH : IsBiTheta ψ A S A' H := (hBi ψ A S A' χA χS χS' χA' oma omb hA hB G hG).1 p
  set H' : WO A S → WO S A' → ℂ := fun u v => oma p (fun u' => G' u' v) u with hH'def
  have hH' : IsBiTheta ψ A S A' H' := (hBi ψ A S A' χA χS χS' χA' oma omb hA hB G' hG').1 p

  set c : ℝ → ℂ := fun s => ψ (symplOH S A' v (M' s)) with hcdef
  have hc : Continuous c := hψ.1.1.comp (GlobalTheory.WeilVacMove.continuous_symplOH S A' continuous_const hM)
  have hc1 : ∀ s, ‖c s‖ = 1 := fun s => hψ.1.2.1 _
  have hheis : ∀ (f : WO S A' → ℂ) s, heisO ψ S A' (M' s) f v = c s * f (v + M' s) := fun f s => rfl
  have hvm : Continuous fun s => v + M' s := continuous_const.add hM
  have hG'c : Continuous fun q : ℝ × WO A S => G' q.2 (v + M' q.1) :=
    hG'.cont.comp (f := fun q : ℝ × WO A S => (q.2, v + M' q.1)) (continuous_snd.prodMk (hvm.comp continuous_fst))
  have hH'c : Continuous fun q : ℝ × WO A S => H' q.2 (v + M' q.1) :=
    hH'.cont.comp (f := fun q : ℝ × WO A S => (q.2, v + M' q.1)) (continuous_snd.prodMk (hvm.comp continuous_fst))
  have hF0 : Continuous fun q : ℝ × WO A S => c q.1 * G' q.2 (v + M' q.1) := (hc.comp continuous_fst).mul hG'c
  have hoF0 : Continuous fun q : ℝ × WO A S => c q.1 * H' q.2 (v + M' q.1) := (hc.comp continuous_fst).mul hH'c

  set F : ℝ → WO A S → ℂ := fun s u' => c s * G' u' (v + M' s) with hFdef
  have hFth : ∀ s, IsThetaFunO ψ A S (F s) := fun s =>
    GlobalTheory.WeilVacMove.isTheta_smul (c s) (GlobalTheory.FrComb.slice_left hG' (v + M' s))
  have hFc : Continuous fun q : ℝ × WO A S => F q.1 q.2 := hF0
  obtain ⟨B1, hB1⟩ := exists_biBound hψ hG'
  have hFb : ∃ C : ℝ, ∀ a x, ‖F a x‖ ≤ C := ⟨B1, fun a x => by
    rw [hFdef, norm_mul, hc1, one_mul]; exact hB1 _ _⟩
  have hoF : ∀ s, oma p (F s) = fun u => c s * H' u (v + M' s) := by
    intro s
    have e : F s = c s • (fun u' => G' u' (v + M' s)) := rfl
    rw [e, map_smul]
    rfl
  have hoFc : Continuous fun q : ℝ × WO A S => oma p (F q.1) q.2 := by
    simp only [hoF]
    exact hoF0
  obtain ⟨B2, hB2⟩ := exists_biBound hψ hH'
  have hoFb : ∃ C : ℝ, ∀ a x, ‖oma p (F a) x‖ ≤ C := ⟨B2, fun a x => by
    rw [hoF, norm_mul, hc1, one_mul]; exact hB2 _ _⟩

  have hftc : ∀ u' t, ∫ s in (0 : ℝ)..t, F s u' = c t * G u' (v + M' t) - G u' v := by
    intro u' t
    have hd : ∀ s, HasDerivAt (fun t : ℝ => heisO ψ S A' (M' t) (G u') v)
        (heisO ψ S A' (M' s) (G' u') v) s := fun s =>
      GlobalTheory.WeilVacMove.hasDerivAt_line hψ hM hM0 (GlobalTheory.FrComb.slice_right hG u') v s
    have hcont : Continuous fun s => F s u' :=
      hF0.comp (f := fun s : ℝ => (s, u')) (continuous_id.prodMk continuous_const)
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t) (fun s _ => hd s)
      (hcont.intervalIntegrable _ _)
    change ∫ s in (0 : ℝ)..t, heisO ψ S A' (M' s) (G' u') v = _
    rw [this, hheis, hheis]
    simp only [hcdef, map_zero, add_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul]

  set φ : ℝ → ℂ := fun t => c t * H u (v + M' t) with hφdef
  set k : ℝ → ℂ := fun s => c s * H' u (v + M' s) with hkdef
  have hk : Continuous k := hoF0.comp (f := fun s : ℝ => (s, u)) (continuous_id.prodMk continuous_const)
  have hφint : ∀ t, 0 ≤ t → φ t = φ 0 + ∫ s in (0 : ℝ)..t, k s := by
    intro t ht
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) t)) :=
      isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
    have hth : IsThetaFunO ψ A S (fun x => ∫ a, F a x ∂(volume.restrict (Set.Ioc (0 : ℝ) t))) := by
      have e : (fun x => ∫ a, F a x ∂(volume.restrict (Set.Ioc (0 : ℝ) t))) =
          c t • (fun u' => G u' (v + M' t)) - (fun u' => G u' v) := by
        funext x
        rw [← intervalIntegral.integral_of_le ht, hftc]
        rfl
      rw [e]
      exact GlobalTheory.WeilVacMove.isTheta_sub (GlobalTheory.WeilVacMove.isTheta_smul _ (GlobalTheory.FrComb.slice_left hG _))
        (GlobalTheory.FrComb.slice_left hG v)
    have hcomm := GlobalTheory.T.weilOperator_integral_comm_of_bounded_finiteMeasure D ψ A S χA χS oma hA ℝ (volume.restrict (Set.Ioc (0 : ℝ) t)) F p hFth hFc hFb hoFc hoFb hth u
    have e1 : (fun y => ∫ a, F a y ∂(volume.restrict (Set.Ioc (0 : ℝ) t))) =
        c t • (fun u' => G u' (v + M' t)) - (fun u' => G u' v) := by
      funext x
      rw [← intervalIntegral.integral_of_le ht, hftc]
      rfl
    rw [e1, map_sub, map_smul] at hcomm
    have e2 : ∫ a, oma p (F a) u ∂(volume.restrict (Set.Ioc (0 : ℝ) t)) = ∫ s in (0 : ℝ)..t, k s := by
      rw [intervalIntegral.integral_of_le ht]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      show oma p (F s) u = k s
      rw [hoF]
    rw [e2] at hcomm
    have e3 : φ 0 = H u v := by
      rw [hφdef]; simp only [map_zero, add_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, hcdef, AddChar.map_zero_eq_one, one_mul]
    rw [e3, ← hcomm]
    simp only [hφdef, hHdef, LinearMap.sub_apply, Pi.sub_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    ring

  have h1 : HasDerivAt φ (GlobalTheory.WeilVacMove.dLine ψ S A' M' (H u) v) 0 :=
    (GlobalTheory.WeilVacMove.hasDerivAt_zero_and_isTheta hψ hM hM0 (GlobalTheory.FrComb.slice_right hH u)).1 v
  have h2 : HasDerivWithinAt φ (k 0) (Set.Ici 0) 0 := by
    have h3 : HasDerivAt (fun t => φ 0 + ∫ s in (0 : ℝ)..t, k s) (k 0) 0 :=
      ((hk.integral_hasStrictDerivAt 0 0).hasDerivAt).const_add _
    refine h3.hasDerivWithinAt.congr (fun t ht => hφint t ht) (hφint 0 le_rfl)
  have h4 := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ h1.hasDerivWithinAt h2
  have e4 : k 0 = H' u v := by
    simp only [hkdef, hcdef, map_zero, add_zero, GlobalTheory.WeilVacMove.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul]
  rw [e4] at h4
  exact h4.symm

end GlobalTheory.DerivComm
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_first_commutes_heisenbergDerivative_second : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (χA χS χS' χA' : (AE D)ˣ →* Circle) (oma : Om A S) (omb : Om S A'), IsWeilDatumO ψ A S χA χS oma → IsWeilDatumO ψ S A' χS' χA' omb → BiAct D → ∀ G : WO A S → WO S A' → ℂ, IsBiTheta ψ A S A' G → ∀ M' : ℝ →+ WO S A', Continuous M' → (∀ s, (M' s).map (finPart D) = 0) → ∀ p u v, oma p (fun u' => GlobalTheory.WeilVacMove.dLine ψ S A' M' (G u') v) u = GlobalTheory.WeilVacMove.dLine ψ S A' M' (fun v' => oma p (fun u' => G u' v') u) v := by
  atlas_forward_decl GlobalTheory.DerivComm.om_dLine_right
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeisLineComb

open GlobalTheory.WeilVacMove GlobalTheory.FockCompare

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem actO_actO_inv (g : GA D S) (h : GA D T) (x : WO S T) : actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  unfold actO
  rw [inv_inv]
  calc HMul.hMul (HMul.hMul (mt T h) (HMul.hMul (HMul.hMul (mt T h⁻¹) x) (mt S g))) (mt S g⁻¹)
      = HMul.hMul (HMul.hMul (HMul.hMul (mt T h) (mt T h⁻¹)) x) (HMul.hMul (mt S g) (mt S g⁻¹)) := by
        simp only [Matrix.mul_assoc]
    _ = x := by rw [← GlobalTheory.WeilVacMove.mt_mul, ← GlobalTheory.WeilVacMove.mt_mul, mul_inv_cancel, mul_inv_cancel, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.mt_one, Matrix.one_mul, Matrix.mul_one]

theorem dLine_apply {θ : GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition.InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ)
    {lam : AF D.host.F →+ ℂ} (hl : Continuous lam) (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a))
    {L : ℝ →+ WO S T} (hL : Continuous L) (hL0 : ∀ t, (L t).map (finPart D) = 0) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (w : WO S T) :
    dLine ψ S T L f w = phase lam S T (L 1) w * f w +
      fderiv ℝ (fun x => f (w + iotaW σ T S x)) 0 (piW θ T S (L 1)) := by
  have hline := (smooth_iff_sm_and_real_lines D θ σ h T S).2.1 L ⟨hL, hL0⟩
  have hfs := ((smooth_iff_sm_and_real_lines D θ σ h T S).1 f).1 hf.smooth
  have e : (fun t : ℝ => heisO ψ S T (L t) f w) = fun t : ℝ => Complex.exp (t * phase lam S T (L 1) w) *
      f (w + iotaW σ T S (t • piW θ T S (L 1))) := by
    funext t
    rw [heisO, psi_sympl_line hl hlam hL hL0, ← hline t]
  unfold dLine
  rw [e]
  exact (hasDerivAt_exp_mul _ _ f hfs _ w).deriv

theorem dLine_eq_sum (hψ : IsStdChar D ψ (-1)) {θ : GlobalTheory.IndefiniteRowSideFullHecke.FockOrthogonalDecomposition.InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D}
    (h : Chart θ σ) {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ (RW T S)) {L : ℝ →+ WO S T} (hL : Continuous L)
    (hL0 : ∀ t, (L t).map (finPart D) = 0) (N : ι → ℝ →+ WO S T) (hN : ∀ i, Continuous (N i))
    (hN0 : ∀ i t, (N i t).map (finPart D) = 0) (hN1 : ∀ i, piW θ T S (N i 1) = b i) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    dLine ψ S T L f = ∑ i, ((b.coord i (piW θ T S (L 1)) : ℝ) : ℂ) • dLine ψ S T (N i) f := by
  obtain ⟨lam, hl, hlam⟩ := exists_log hψ
  funext w
  let A : RW T S →+ ℂ := AddMonoidHom.mk' (fun v => lam (symplOH S T w (iotaW σ T S v))) fun u v => by
    rw [map_add, symplOH_add_right, map_add]
  have hA : Continuous A := hl.comp (continuous_symplOH S T continuous_const (h.continuous_iota T S))
  let A' : RW T S →L[ℝ] ℂ := A.toRealLinearMap hA
  let B : RW T S →L[ℝ] ℂ := fderiv ℝ (fun x => f (w + iotaW σ T S x)) 0
  let Φ : RW T S →ₗ[ℝ] ℂ := (LinearMap.mulRight ℝ (f w)).comp A'.toLinearMap + B.toLinearMap
  have key : ∀ (K : ℝ →+ WO S T), Continuous K → (∀ t, (K t).map (finPart D) = 0) →
      dLine ψ S T K f w = Φ (piW θ T S (K 1)) := by
    intro K hK hK0
    rw [dLine_apply h hl hlam hK hK0 hf]
    have e1 : K 1 = iotaW σ T S (piW θ T S (K 1)) := by
      have := (smooth_iff_sm_and_real_lines D θ σ h T S).2.1 K ⟨hK, hK0⟩ 1
      rwa [one_smul] at this
    have e2 : lam (symplOH S T w (K 1)) = A (piW θ T S (K 1)) := by
      show _ = lam (symplOH S T w (iotaW σ T S (piW θ T S (K 1))))
      rw [← e1]
    show lam (symplOH S T w (K 1)) * f w + _ = _
    rw [e2]
    rfl
  rw [Finset.sum_apply, key L hL hL0]
  simp only [Pi.smul_apply, smul_eq_mul]
  simp only [fun i => key (N i) (hN i) (hN0 i), hN1]
  conv_lhs => rw [← b.sum_repr (piW θ T S (L 1))]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Complex.real_smul, Module.Basis.coord_apply]

theorem dLine_om_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ M : ℝ →+ WO S T, Continuous M → (∀ s, (M s).map (finPart D) = 0) → ∃ (m : ℕ) (N : Fin m → ℝ →+ WO S T) (c : Fin m → GA D S × GA D T → ℂ), (∀ i, Continuous (N i)) ∧ (∀ i s, (N i s).map (finPart D) = 0) ∧ (∀ i, Continuous (c i)) ∧ ∀ p f, IsThetaFunO ψ S T f → GlobalTheory.WeilVacMove.dLine ψ S T M (om p f) = ∑ i, c i p • om p (GlobalTheory.WeilVacMove.dLine ψ S T (N i) f) := by
  intro D ψ S T χS χT om hW M hM hM0
  have hψ := hW.std
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  let b := Module.finBasis ℝ (RW T S)
  let N : Fin (Module.finrank ℝ (RW T S)) → ℝ →+ WO S T := fun i =>
    (iotaW σ T S).comp (ContinuousLinearMap.toSpanSingleton ℝ (b i)).toLinearMap.toAddMonoidHom
  have hN : ∀ i, Continuous (N i) := fun i =>
    (h.continuous_iota T S).comp (ContinuousLinearMap.toSpanSingleton ℝ (b i)).continuous
  have hN0 : ∀ i t, (N i t).map (finPart D) = 0 := fun i t => h.real_iota T S _
  have hN1 : ∀ i, piW θ T S (N i 1) = b i := fun i => by
    show piW θ T S (iotaW σ T S ((1 : ℝ) • b i)) = b i
    rw [h.pi_iota, one_smul]
  let Mp : GA D S × GA D T → ℝ →+ WO S T := fun p =>
    AddMonoidHom.mk' (fun s => actO S T p.1⁻¹ p.2⁻¹ (M s)) fun s t => by rw [map_add, actO_add]
  have hMp : ∀ p, Continuous (Mp p) := fun p =>
    (continuous_const.matrix_mul hM).matrix_mul continuous_const
  have hMp0 : ∀ p t, (Mp p t).map (finPart D) = 0 := fun p t => by
    show (actO S T p.1⁻¹ p.2⁻¹ (M t)).map (finPart D) = 0
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, hM0 t, Matrix.mul_zero, Matrix.zero_mul]
  refine ⟨_, N, fun i p => ((b.coord i (piW θ T S (Mp p 1)) : ℝ) : ℂ), hN, hN0, fun i => ?_, fun p f hf => ?_⟩
  · have hc : Continuous fun p : GA D S × GA D T => actO S T p.1⁻¹ p.2⁻¹ (M 1) := by
      unfold actO
      exact (((GlobalTheory.MixModel.continuous_mt T).comp (continuous_snd.inv)).matrix_mul continuous_const).matrix_mul
        ((GlobalTheory.MixModel.continuous_mt S).comp continuous_fst.inv.inv)
    exact Complex.continuous_ofReal.comp ((LinearMap.continuous_of_finiteDimensional (b.coord i)).comp
      ((continuous_pi' hθ T S).comp hc))
  · obtain ⟨g, k⟩ := p
    have e := om_dLine hW g k (hMp (g, k)) (hMp0 (g, k)) hM hM0 (fun t => (actO_actO_inv g k (M t)).symm) hf
    rw [← e, dLine_eq_sum hψ h b (hMp (g, k)) (hMp0 (g, k)) N hN hN0 hN1 hf, map_sum]
    simp only [map_smul]

end GlobalTheory.HeisLineComb

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDeriv_weilTranslate_continuous_combination : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ M : ℝ →+ WO S T, Continuous M → (∀ s, (M s).map (finPart D) = 0) → ∃ (m : ℕ) (N : Fin m → ℝ →+ WO S T) (c : Fin m → GA D S × GA D T → ℂ), (∀ i, Continuous (N i)) ∧ (∀ i s, (N i s).map (finPart D) = 0) ∧ (∀ i, Continuous (c i)) ∧ ∀ p f, IsThetaFunO ψ S T f → GlobalTheory.WeilVacMove.dLine ψ S T M (om p f) = ∑ i, c i p • om p (GlobalTheory.WeilVacMove.dLine ψ S T (N i) f) := by
  first | exact @GlobalTheory.HeisLineComb.dLine_om_comb | exact GlobalTheory.HeisLineComb.dLine_om_comb | (intros; apply GlobalTheory.HeisLineComb.dLine_om_comb <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

open scoped ComplexOrder

theorem sig_eq_of_definite {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef ∨ (-G).PosDef) {p q : ℕ}
    (h : Formalism.UG.HasSignature G p q) : (p, q) = (n, 0) ∨ (p, q) = (0, n) := by
  rcases hG with hG | hG
  · exact Or.inl (GlobalTheory.DefLiftMult.sig_of_posDef hG h)
  · right
    obtain ⟨hn, Q, hQ⟩ := Formalism.UG.P.sig_data G p q h
    have hp : p = 0 := by
      by_contra hp
      have i : Fin p := ⟨0, Nat.pos_of_ne_zero hp⟩
      have h1 := (hG.posSemidef.conjTranspose_mul_mul_same Q).diag_nonneg (i := Sum.inl i)
      rw [Matrix.mul_neg, Matrix.neg_mul, hQ] at h1
      simp [Formalism.UG.Jpq] at h1
      exact absurd h1 (by norm_num)
    subst hp
    simp at hn
    rw [hn]

theorem isDefinite_of_defSp {D : D7} {A : HSp D} (x : DefSp A) (hx : x.Is) : A.IsDefinite := by
  have hτ : ∀ τ, (gramAt D A τ).PosDef ∨ (-(gramAt D A τ)).PosDef := by
    intro τ
    have hp := (hx.cart τ).2.2
    rcases hx.pm τ with h | h
    · left
      rwa [h, Matrix.mul_one] at hp
    · right
      rwa [h, Matrix.mul_neg, Matrix.mul_one] at hp
  intro σ
  have hs := hx.sig σ
  have key : (A.sig σ).1 = A.rank ∧ (A.sig σ).2 = 0 ∨ (A.sig σ).1 = 0 ∧ (A.sig σ).2 = A.rank := by
    obtain ⟨τ, rfl | rfl⟩ := GlobalTheory.DefLiftMult.exists_tauE D σ
    · simpa [Prod.ext_iff] using sig_eq_of_definite (hτ τ) hs
    · have e : A.gram.map ((starRingEnd ℂ).comp (tauE D τ)) = (gramAt D A τ)ᴴᵀ := by
        ext i j
        rfl
      rw [e] at hs
      have hd : ((gramAt D A τ)ᴴᵀ).PosDef ∨ (-(gramAt D A τ)ᴴᵀ).PosDef := by
        rcases hτ τ with h | h
        · exact Or.inl h.conjTranspose.transpose
        · right
          have := h.conjTranspose.transpose
          rwa [Matrix.conjTranspose_neg, Matrix.transpose_neg] at this
      simpa [Prod.ext_iff] using sig_eq_of_definite hd hs
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (Prod.ext h1 h2)
  · exact Or.inr (Prod.ext h1 h2)

theorem isCompact_ginfC_of_defSp : ∀ (D : D7) (A : HSp D) (x : DefSp A), x.Is → IsCompact (GinfC A : Set (GA D A)) :=
  fun _ _ x hx => Formalism.IndefR.Eqv.isCompact_GinfC hx.sig (isDefinite_of_defSp x hx)

end GlobalTheory.SeeSaw

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_realPoints_of_definiteHermitianSpaceData : ∀ (D : D7) (A : HSp D) (x : DefSp A), x.Is → IsCompact (GinfC A : Set (GA D A)) := by
  atlas_forward_decl GlobalTheory.SeeSaw.isCompact_ginfC_of_defSp
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CenAvg

section Base

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

open GlobalTheory.WeilVacMove in
theorem dLine_smul {S T : HSp D} (M : ℝ →+ WO S T) (a : ℂ) (f : WO S T → ℂ) : dLine ψ S T M (a • f) = a • dLine ψ S T M f := by
  funext x
  simp only [dLine, heisO, Pi.smul_apply, smul_eq_mul]
  rw [← deriv_const_mul_field]
  congr 1
  funext t
  ring

open GlobalTheory.WeilVacMove in
theorem dLine_add (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {M : ℝ →+ WO S T} (hM : Continuous M)
    (hM0 : ∀ s, (M s).map (finPart D) = 0) {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    dLine ψ S T M (f + g) = dLine ψ S T M f + dLine ψ S T M g := by
  funext x
  have h := ((hasDerivAt_zero_and_isTheta hψ hM hM0 hf).1 x).add ((hasDerivAt_zero_and_isTheta hψ hM hM0 hg).1 x)
  refine Eq.trans ?_ h.deriv
  unfold dLine
  congr 1
  funext t
  simp only [heisO, Pi.add_apply, mul_add]

variable {A S A' : HSp D} {χA χS χS' χA' : (AE D)ˣ →* Circle} {oma : Om A S} {omb : Om S A'}

theorem continuous_act (ha : IsWeilDatumO ψ A S χA χS oma) (hb : IsWeilDatumO ψ S A' χS' χA' omb) (hB : BiAct D)
    {G : WO A S → WO S A' → ℂ} (hG : IsBiTheta ψ A S A' G) :
    Continuous fun x : (GA D A × GA D S) × WO A S × WO S A' => oma x.1 (fun u => G u x.2.2) x.2.1 := by
  have h := (hB ψ A S A' _ _ _ _ oma omb ha hb G hG).2.2.2.comp
    (show Continuous fun x : (GA D A × GA D S) × WO A S × WO S A' => (x.1, ((1 : GA D S × GA D A'), x.2)) from
      continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
  simpa only [Function.comp_def, map_one, Module.End.one_apply] using h

end Base

section Smooth

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {χA χS χS' χA' : (AE D)ˣ →* Circle} {oma : Om A S} {omb : Om S A'}

open GlobalTheory.WeilVacMove GlobalTheory.BiTransfer in

theorem isBiSmooth_avg (ha : IsWeilDatumO ψ A S χA χS oma) (hb : IsWeilDatumO ψ S A' χS' χA' omb) (hB : BiAct D)
    {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    {p : K → GA D A × GA D S} (hp : Continuous p) {c : K → ℂ} (hc : Continuous c) {G : WO A S → WO S A' → ℂ}
    (hG : IsBiTheta ψ A S A' G) : IsBiSmooth fun u v => ∫ k, c k * oma (p k) (fun u' => G u' v) u ∂μ := by
  have hψ := ha.std
  let d := sumDec A (GlobalTheory.ChiGrid.negSp A')
  let gen : Set (K → WO (GlobalTheory.Doubling.hsum A (GlobalTheory.ChiGrid.negSp A')) S → ℂ) :=
    {F | ∃ (c : K → ℂ) (G : WO A S → WO S A' → ℂ), Continuous c ∧ IsBiTheta ψ A S A' G ∧
      F = fun k => c k • join d S fun u v => oma (p k) (fun u' => G u' v) u}
  have h1 : ∀ F ∈ Submodule.span ℂ gen, Continuous fun q : K × WO (GlobalTheory.Doubling.hsum A (GlobalTheory.ChiGrid.negSp A')) S => F q.1 q.2 := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem F h =>
      obtain ⟨c, G, hc, hG, rfl⟩ := h
      exact (hc.comp continuous_fst).mul ((continuous_act ha hb hB hG).comp ((hp.comp continuous_fst).prodMk
        (((continuous_fstH d S).comp continuous_snd).prodMk ((continuous_sndH d S).comp continuous_snd))))
    | zero => exact continuous_const
    | add F F' _ _ h h' => exact h.add h'
    | smul a F _ h => exact h.const_smul a
  have h2 : ∀ F ∈ Submodule.span ℂ gen, ∀ k, IsThetaFunO ψ _ S (F k) := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem F h =>
      obtain ⟨c, G, hc, hG, rfl⟩ := h
      exact fun k => isTheta_smul _ (isThetaFunO_join d ((hB ψ A S A' _ _ _ _ oma omb ha hb G hG).1 (p k)))
    | zero => exact fun _ => isTheta_zero
    | add F F' _ _ h h' => exact fun k => isTheta_add (h k) (h' k)
    | smul a F _ h => exact fun k => isTheta_smul a (h k)
  have h3 : ∀ F ∈ Submodule.span ℂ gen, ∀ M : ℝ →+ WO _ S, Continuous M → (∀ s, (M s).map (finPart D) = 0) →
      (fun k => dLine ψ _ S M (F k)) ∈ Submodule.span ℂ gen := by
    intro F hF M hM hM0
    induction hF using Submodule.span_induction with
    | mem F h =>
      obtain ⟨c, G, hc, hG, rfl⟩ := h
      have hT := (hB ψ A S A' _ _ _ _ oma omb ha hb G hG).1
      obtain ⟨f1, f2, -⟩ := GlobalTheory.T.heisenbergOneParamDeriv_orthDecJoined_eq_sum D ψ hψ _ A S A' d G hG M hM hM0
      have c1 : Continuous ((fstH d S).comp M) := (continuous_fstH d S).comp hM
      have c2 : Continuous ((sndH d S).comp M) := (continuous_sndH d S).comp hM
      obtain ⟨m, N, e, hN, hN0, he, hexp⟩ := GlobalTheory.T.heisenbergDeriv_weilTranslate_continuous_combination D ψ A S χA χS oma ha _ c1 f1
      have key : (fun k => dLine ψ _ S M (c k • join d S fun u v => oma (p k) (fun u' => G u' v) u)) =
          (∑ i, fun k => (c k * e i (p k)) • join d S fun u v =>
            oma (p k) (fun u' => dLine ψ A S (N i) (fun u'' => G u'' v) u') u) +
          fun k => c k • join d S fun u v => oma (p k) (fun u' => dLine ψ S A' ((sndH d S).comp M) (G u') v) u := by
        funext k
        rw [dLine_smul, (GlobalTheory.T.heisenbergOneParamDeriv_orthDecJoined_eq_sum D ψ hψ _ A S A' d _ (hT (p k)) M hM hM0).2.2]
        funext x
        simp only [Pi.smul_apply, Pi.add_apply, Finset.sum_apply, join_apply, smul_eq_mul]
        rw [GlobalTheory.T.weilOperator_first_commutes_heisenbergDerivative_second D ψ A S A' _ _ _ _ oma omb ha hb hB G hG _ c2 f2, mul_add]
        congr 1
        have := congrFun (hexp (p k) _ (GlobalTheory.FrComb.slice_left hG (sndH d S x))) (fstH d S x)
        simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul] at this
        rw [show (fun u' => oma (p k) (fun u'' => G u'' (sndH d S x)) u') = oma (p k) (fun u'' => G u'' (sndH d S x)) from rfl,
          this, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
      rw [key]
      refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.subset_span ?_) (Submodule.subset_span ?_)
      · exact ⟨_, _, hc.mul ((he i).comp hp), (GlobalTheory.T.isJointlySmoothBiTheta_heisenbergDeriv D ψ hψ A S A' G hG).1 _ (hN i) (hN0 i), rfl⟩
      · exact ⟨_, _, hc, (GlobalTheory.T.isJointlySmoothBiTheta_heisenbergDeriv D ψ hψ A S A' G hG).2 _ c2 f2, rfl⟩
    | zero =>
      have : (fun k : K => dLine ψ _ S M ((0 : K → WO (GlobalTheory.Doubling.hsum A (GlobalTheory.ChiGrid.negSp A')) S → ℂ) k)) = 0 := by
        funext k x
        simp [dLine, heisO]
      rw [this]
      exact Submodule.zero_mem _
    | add F F' hF hF' h h' =>
      have : (fun k => dLine ψ _ S M ((F + F') k)) = (fun k => dLine ψ _ S M (F k)) + fun k => dLine ψ _ S M (F' k) :=
        funext fun k => dLine_add hψ hM hM0 (h2 F hF k) (h2 F' hF' k)
      rw [this]
      exact Submodule.add_mem _ h h'
    | smul a F _ h =>
      have : (fun k => dLine ψ _ S M ((a • F) k)) = a • fun k => dLine ψ _ S M (F k) :=
        funext fun k => dLine_smul M a (F k)
      rw [this]
      exact Submodule.smul_mem _ a h
  intro n L L' hL hL' h0 h0' u v
  have := GlobalTheory.T.compactAverage_thetaFamily_smooth D ψ hψ _ S K μ (Submodule.span ℂ gen : Set _) h1 h2 h3 _ (Submodule.subset_span (show _ ∈ gen from ⟨c, G, hc, hG, rfl⟩)) n
    ((inlH d S).comp L + (inrH d S).comp L') (((continuous_inlH d S).comp hL).add ((continuous_inrH d S).comp hL'))
    (fun t => by
      show (inlH d S (L t) + inrH d S (L' t)).map (finPart D) = 0
      rw [Matrix.map_add _ (RingHom.map_add _), map_inlH d S _ (h0 t), fin_inrH d S (h0' t), add_zero]) (inlH d S u + inrH d S v)
  convert this using 4 with t k
  simp only [Pi.smul_apply, join_apply, smul_eq_mul, AddMonoidHom.add_apply, AddMonoidHom.comp_apply, map_add, fst_inl, fst_inr,
    snd_inl, snd_inr, add_zero, zero_add]

end Smooth

section Compact

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {K : Type} [TopologicalSpace K] [CompactSpace K]

theorem exists_bound_fam (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {F : K → WO S T → ℂ} (hF : ∀ k, IsThetaFunO ψ S T (F k))
    (hc : Continuous fun q : K × WO S T => F q.1 q.2) : ∃ C : ℝ, ∀ k x, ‖F k x‖ ≤ C := by
  obtain ⟨-, -, -, -, -, Q, hQ, hQc⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  obtain ⟨C, hC⟩ := (isCompact_univ.prod hQ).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun k x => ?_⟩
  obtain ⟨γ, ⟨γ', rfl⟩, hx⟩ := hQc x
  have hq := (hF k).quasi γ' x
  have e : (((incA D).toAddMonoidHom.mapMatrix (m := Fin T.rank) (n := Fin S.rank)) γ') = ratW T S γ' := rfl
  rw [e] at hx
  have h1 := hψ.1.2.1 (-(symplOH S T (ratW T S γ') x))
  have := hC (k, _) ⟨Set.mem_univ _, hx⟩
  simp only at this
  rw [hq, norm_mul, h1, one_mul] at this
  exact this

variable [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K] (μ : Measure K)

theorem om_integral [IsFiniteMeasure μ] {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hom : IsWeilDatumO ψ S T χS χT om) {c : K → ℂ} (hc : Continuous c) {F : K → WO S T → ℂ} (p : GA D S × GA D T)
    (hF : ∀ k, IsThetaFunO ψ S T (F k)) (h1 : Continuous fun q : K × WO S T => F q.1 q.2)
    (h2 : Continuous fun q : K × WO S T => om p (F q.1) q.2) (hI : IsThetaFunO ψ S T fun x => ∫ k, c k * F k x ∂μ) (x : WO S T) :
    om p (fun y => ∫ k, c k * F k y ∂μ) x = ∫ k, c k * om p (F k) x ∂μ := by
  have hF' : ∀ k, IsThetaFunO ψ S T (c k • F k) := fun k => GlobalTheory.WeilVacMove.isTheta_smul _ (hF k)
  have h1' : Continuous fun q : K × WO S T => (c q.1 • F q.1) q.2 := (hc.comp continuous_fst).mul h1
  have h2' : Continuous fun q : K × WO S T => om p (c q.1 • F q.1) q.2 := by
    simp only [map_smul]
    exact (hc.comp continuous_fst).mul h2
  have := GlobalTheory.T.weilOperator_integral_comm_of_bounded_finiteMeasure D ψ S T χS χT om hom K μ (fun k => c k • F k) p hF' h1' (exists_bound_fam hom.std hF' h1') h2'
    (exists_bound_fam hom.std (fun k => hom.om_pres p _ (hF' k)) h2') hI x
  simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using this

omit [CompactSpace K] in

theorem integral_mean [IsProbabilityMeasure μ] {A : HSp D} (hA : CoCpt A) (vA : Vol A) {j : K → GA D A} (hj : Continuous j)
    {F : GA D A → ℂ} (hF : IsContAut A F) : ∫ h in vA.𝓕, ∫ k, F (h * j k) ∂μ ∂vA.μ = ∫ h in vA.𝓕, F h ∂vA.μ := by
  obtain ⟨i1, -, i3, -, i5, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D A
  have hfin := (GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D A hA vA Unit (fun _ _ => 1) continuous_const (fun _ _ _ _ => rfl)).1 ()
  haveI : IsFiniteMeasure (vA.μ.restrict vA.𝓕) := by
    rcases (integrable_const_iff (c := (1 : ℂ))).1 hfin with h | h
    · exact absurd h one_ne_zero
    · exact h
  obtain ⟨C, hC⟩ := (GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D A hA vA Unit (fun g _ => F g) (hF.2.comp continuous_fst)
    (fun γ hγ g _ => hF.1 γ hγ g)).2.2 ()
  have hC' := hC.self_of_nhds
  rw [integral_integral_swap]
  · simp_rw [GlobalTheory.T.setIntegral_fundamentalDomain_right_translate_invariant D A vA.μ vA.𝓕 vA.haar vA.fund F hF.1]
    simp
  · refine Integrable.mono' (integrable_const C) ?_ (ae_of_all _ fun q => hC' _)
    exact (hF.2.comp (continuous_fst.mul (hj.comp continuous_snd))).aestronglyMeasurable

end Compact

section Avg

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {χA χS χS' χA' : (AE D)ˣ →* Circle} {oma : Om A S} {omb : Om S A'}
  {K : Type} [MeasurableSpace K]

def avg (oma : Om A S) (μ : Measure K) (j : K → GA D A) (c : K → ℂ) (G : WO A S → WO S A' → ℂ) : WO A S → WO S A' → ℂ :=
  fun u v => ∫ k, c k * oma (j k, 1) (fun u' => G u' v) u ∂μ

variable (μ : Measure K) {j : K → GA D A} (c : K → ℂ) {G : WO A S → WO S A' → ℂ}

theorem avg_fix_left (ha : IsWeilDatumO ψ A S χA χS oma) (hj : ∀ k, j k ∈ GinfC A) {v : WO S A'}
    (hG : IsThetaFunO ψ A S fun u => G u v) {w : WO A S} (hw : w.map (infPart D) = 0)
    (h : heisO ψ A S w (fun u => G u v) = fun u => G u v) :
    heisO ψ A S w (fun u => avg oma μ j c G u v) = fun u => avg oma μ j c G u v := by
  funext u
  simp only [heisO, avg]
  rw [← integral_const_mul]
  congr 1
  funext k
  have := congrFun (ha.om_heis (j k) 1 w _ hG) u
  rw [h, GlobalTheory.FrComb.actO_real (hj k) (GinfC S).one_mem hw] at this
  rw [this, heisO]
  ring

theorem avg_fix_right {w : WO S A'} (h : ∀ u, heisO ψ S A' w (G u) = G u) (u : WO A S) :
    heisO ψ S A' w (avg oma μ j c G u) = avg oma μ j c G u := by
  funext v
  simp only [heisO, avg]
  rw [← integral_const_mul]
  congr 1
  funext k
  have e : (fun u' => G u' v) = ψ (symplOH S A' v w) • fun u' => G u' (v + w) := funext fun u' => (congrFun (h u') v).symm
  rw [e, map_smul, Pi.smul_apply, smul_eq_mul]
  ring

variable [TopologicalSpace K] [CompactSpace K] [BorelSpace K] [IsFiniteMeasure μ] {c}

omit [MeasurableSpace K] [CompactSpace K] [BorelSpace K] in
theorem continuous_fam (ha : IsWeilDatumO ψ A S χA χS oma) (hb : IsWeilDatumO ψ S A' χS' χA' omb) (hB : BiAct D)
    (hG : IsBiTheta ψ A S A' G) {p : K → GA D A × GA D S} (hp : Continuous p) :
    Continuous fun q : K × WO A S × WO S A' => oma (p q.1) (fun u => G u q.2.2) q.2.1 :=
  (continuous_act ha hb hB hG).comp ((hp.comp continuous_fst).prodMk continuous_snd)

theorem isBiTheta_avg (ha : IsWeilDatumO ψ A S χA χS oma) (hb : IsWeilDatumO ψ S A' χS' χA' omb) (hB : BiAct D)
    (hjc : Continuous j) (hj : ∀ k, j k ∈ GinfC A) (hc : Continuous c) (hG : IsBiTheta ψ A S A' G) :
    IsBiTheta ψ A S A' (avg oma μ j c G) := by
  have hp : Continuous fun k => (j k, (1 : GA D S)) := hjc.prodMk continuous_const
  have hT := (hB ψ A S A' _ _ _ _ oma omb ha hb G hG).1
  refine ⟨?_, isBiSmooth_avg ha hb hB μ hp hc hG, fun γ u v => ?_, fun γ u v => ?_, ?_, ?_⟩
  · exact GlobalTheory.AvgFam.continuous_avg μ (F := fun k (q : WO A S × WO S A') => c k * oma (j k, 1) (fun u' => G u' q.2) q.1)
      ((hc.comp continuous_fst).mul (continuous_fam ha hb hB hG hp))
  · simp only [avg]
    rw [← integral_const_mul]
    congr 1
    funext k
    rw [(hT (j k, 1)).quasiL]
    ring
  · simp only [avg]
    rw [← integral_const_mul]
    congr 1
    funext k
    rw [(hT (j k, 1)).quasiR]
    ring
  · obtain ⟨U, hU, h⟩ := hG.levL
    exact ⟨U, hU, fun a haU ha0 v => avg_fix_left μ c ha hj (GlobalTheory.FrComb.slice_left hG v) ha0 (h a haU ha0 v)⟩
  · obtain ⟨U, hU, h⟩ := hG.levR
    exact ⟨U, hU, fun a haU ha0 u => avg_fix_right μ c (h a haU ha0) u⟩

theorem isBiVac_avg (ha : IsWeilDatumO ψ A S χA χS oma) (hb : IsWeilDatumO ψ S A' χS' χA' omb) (hB : BiAct D)
    (hjc : Continuous j) (hj : ∀ k, j k ∈ GinfC A) (hc : Continuous c) (hG : IsBiTheta ψ A S A' G) {LA LS LA'}
    (hv : IsBiVac ψ A S A' LA LS LA' G) : IsBiVac ψ A S A' LA LS LA' (avg oma μ j c G) := by
  have h := isBiTheta_avg μ ha hb hB hjc hj hc hG
  refine ⟨h.cont, fun v => ⟨GlobalTheory.FrComb.slice_left h v, fun w hw => ?_, fun e he w hw hw' => ?_⟩,
    fun u => ⟨GlobalTheory.FrComb.slice_right h u, fun w hw => ?_, fun e he w hw hw' => ?_⟩⟩
  · exact avg_fix_left μ c ha hj (hv.left v).1 (GlobalTheory.FrComb.nsmul_fin (GlobalTheory.SplitScalar.latO_fin hw) 2) ((hv.left v).2.1 w hw)
  · exact avg_fix_left μ c ha hj (hv.left v).1 (GlobalTheory.SplitScalar.latO_fin hw) ((hv.left v).2.2 e he w hw hw')
  · exact avg_fix_right μ c (fun u' => (hv.right u').2.1 w hw) u
  · exact avg_fix_right μ c (fun u' => (hv.right u').2.2 e he w hw hw') u

theorem biComb_avg (ha : IsWeilDatumO ψ A S χA χS oma) (hb : IsWeilDatumO ψ S A' χS' χA' omb) (hB : BiAct D)
    (hjc : Continuous j) (hj : ∀ k, j k ∈ GinfC A) (hc : Continuous c) (hG : IsBiTheta ψ A S A' G)
    {e : WO A S →₀ ℂ} {e' : WO S A' →₀ ℂ} (he : IsFinComb e) (he' : IsFinComb e') :
    biComb ψ A S A' e e' (avg oma μ j c G) = avg oma μ j c (biComb ψ A S A' e e' G) := by
  have hp : Continuous fun k => (j k, (1 : GA D S)) := hjc.prodMk continuous_const
  have hK1 := GlobalTheory.FrComb.biTheta_combR ha.std hG he'
  have s1 : ∀ k u v, oma (j k, 1) (fun u' => biComb ψ A S A' e e' G u' v) u =
      biComb ψ A S A' e e' (fun u v => oma (j k, 1) (fun u' => G u' v) u) u v := by
    intro k u v
    show oma (j k, 1) (comb ψ A S e fun u'' => comb ψ S A' e' (G u'') v) u = _
    rw [GlobalTheory.FrComb.om_comb ha (hj k) (GinfC S).one_mem he (GlobalTheory.FrComb.slice_left hK1 v), GlobalTheory.FrComb.op_combR]
    rfl
  have hi : ∀ (a : ℂ) u v, Integrable (fun k => a * (c k * oma (j k, 1) (fun u' => G u' v) u)) μ := fun a u v =>
    GlobalTheory.AvgFam.integrable_of_continuous μ (continuous_const.mul (hc.mul ((continuous_fam ha hb hB hG hp).comp
      (continuous_id.prodMk (continuous_const (y := (u, v)))))))
  funext u v
  have e1 : biComb ψ A S A' e e' (avg oma μ j c G) u v = ∑ x ∈ e.support, ∑ y ∈ e'.support,
      ∫ k, (e x * ψ (symplOH A S u x) * (e' y * ψ (symplOH S A' v y))) *
        (c k * oma (j k, 1) (fun u' => G u' (v + y)) (u + x)) ∂μ := by
    simp only [biComb, GlobalTheory.FrComb.comb_apply, Finset.mul_sum, avg, integral_const_mul, mul_assoc]
  rw [e1]
  simp only [avg, s1]
  rw [← Finset.sum_congr rfl fun x _ => integral_finset_sum _ fun y _ => hi _ _ _,
    ← integral_finset_sum _ fun x _ => integrable_finset_sum _ fun y _ => hi _ _ _]
  congr 1
  funext k
  simp only [biComb, GlobalTheory.FrComb.comb_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

variable [SecondCountableTopology K]

theorem om_avg (ha : IsWeilDatumO ψ A S χA χS oma) (hb : IsWeilDatumO ψ S A' χS' χA' omb) (hB : BiAct D)
    (hjc : Continuous j) (hj : ∀ k, j k ∈ GinfC A) (hc : Continuous c) (hG : IsBiTheta ψ A S A' G) (g : GA D A) (h : GA D S)
    (u : WO A S) (v : WO S A') :
    oma (g, h) (fun u' => avg oma μ j c G u' v) u = ∫ k, c k * oma (g * j k, h) (fun u' => G u' v) u ∂μ := by
  haveI := (GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D A).1
  have hm : ∀ k f, oma (g, h) (oma (j k, 1) f) = oma (g * j k, h) f := fun k f => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have hv : Continuous fun q : K × WO A S => (q.1, q.2, v) := continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
  have := om_integral μ ha hc (F := fun k => oma (j k, 1) fun u' => G u' v) (g, h)
    (fun k => ha.om_pres _ _ (GlobalTheory.FrComb.slice_left hG v))
    ((continuous_fam ha hb hB hG (hjc.prodMk continuous_const)).comp hv)
    (by
      simp only [hm]
      exact (continuous_fam ha hb hB hG (p := fun k => (g * j k, h)) ((continuous_const.mul hjc).prodMk continuous_const)).comp hv)
    (GlobalTheory.FrComb.slice_left (isBiTheta_avg μ ha hb hB hjc hj hc hG) v) u
  simp only [hm] at this
  exact this

theorem ker_avg (ha : IsWeilDatumO ψ A S χA χS oma) (hb : IsWeilDatumO ψ S A' χS' χA' omb) (hB : BiAct D)
    (hjc : Continuous j) (hj : ∀ k, j k ∈ GinfC A) (hc : Continuous c) (hG : IsBiTheta ψ A S A' G) (g : GA D A) (h : GA D S)
    (q : GA D S × GA D A') (u : WO A S) (v : WO S A') :
    omb q (fun v' => oma (g, h) (fun u' => avg oma μ j c G u' v') u) v =
      ∫ k, c k * omb q (fun v' => oma (g * j k, h) (fun u' => G u' v') u) v ∂μ := by
  haveI := (GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D A).1
  have hBG := hB ψ A S A' _ _ _ _ oma omb ha hb G hG
  have hp : Continuous fun k => (g * j k, h) := (continuous_const.mul hjc).prodMk continuous_const
  have hI := GlobalTheory.FrComb.slice_right ((hB ψ A S A' _ _ _ _ oma omb ha hb _ (isBiTheta_avg μ ha hb hB hjc hj hc hG)).1 (g, h)) u
  simp only [om_avg μ ha hb hB hjc hj hc hG] at hI ⊢
  refine om_integral μ hb hc (F := fun k v' => oma (g * j k, h) (fun u' => G u' v') u) q
    (fun k => GlobalTheory.FrComb.slice_right (hBG.1 (g * j k, h)) u) ?_ ?_ hI v
  · exact (continuous_fam ha hb hB hG hp).comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
  · exact hBG.2.2.2.comp (show Continuous fun z : K × WO S A' => ((g * j z.1, h), q, u, z.2) from
      (hp.comp continuous_fst).prodMk (continuous_const.prodMk (continuous_const.prodMk continuous_snd)))

end Avg

end GlobalTheory.CenAvg

end
end
