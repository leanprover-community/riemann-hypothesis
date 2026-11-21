import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfDone
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHold
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHoldStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralLinearGroupUnimodular
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeCalculusHoldsStatement

section
noncomputable section

open MeasureTheory Set Filter Metric
open scoped ContDiff Topology

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cwave

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

def pX {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (Φ : ℝ × H → W) : ℝ × H → (H →L[ℝ] W) :=
  fun q => (fderiv ℝ Φ q).comp (ContinuousLinearMap.inr ℝ ℝ H)

def Good {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (O : Set H) (Φ : ℝ × H → W) (T : ℝ) : Prop :=
  ContDiffOn ℝ ∞ Φ (Set.univ ×ˢ O) ∧ ∀ t x, T < |t| → Φ (t, x) = 0

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {O : Set H}

theorem Good.deriv (hO : IsOpen O) {Φ : ℝ × H → W} {T : ℝ} (h : Good O Φ T) : Good O (pX Φ) T := by
  refine ⟨(h.1.fderiv_of_isOpen (isOpen_univ.prod hO) (by simp)).clm_comp contDiffOn_const, fun t x ht => ?_⟩
  have hO' : IsOpen {q : ℝ × H | T < |q.1|} := isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
  have hev : Φ =ᶠ[𝓝 (t, x)] fun _ => 0 :=
    Filter.eventuallyEq_of_mem (hO'.mem_nhds ht) fun q hq => h.2 q.1 q.2 hq
  show (fderiv ℝ Φ (t, x)).comp _ = 0
  rw [hev.fderiv_eq]
  simp

theorem Good.cont_line {Φ : ℝ × H → W} {T : ℝ} (h : Good O Φ T) {x : H} (hx : x ∈ O) :
    Continuous fun t => Φ (t, x) :=
  h.1.continuousOn.comp_continuous (continuous_id.prodMk continuous_const) fun t => ⟨mem_univ _, hx⟩

theorem Good.integrable {Φ : ℝ × H → W} {T : ℝ} (h : Good O Φ T) {x : H} (hx : x ∈ O) :
    Integrable (fun t => Φ (t, x)) := by
  refine (h.cont_line hx).integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := -T) (b := T)) fun t ht => ?_)
  refine h.2 t x ?_
  by_contra hc
  exact ht (abs_le.1 (not_lt.1 hc))

theorem Good.hasFDerivAt [CompleteSpace W] (hO : IsOpen O) {Φ : ℝ × H → W} {T : ℝ} (h : Good O Φ T) {x₀ : H}
    (hx₀ : x₀ ∈ O) : HasFDerivAt (fun x => ∫ t, Φ (t, x)) (∫ t, pX Φ (t, x₀)) x₀ := by
  obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.1 hO x₀ hx₀
  have hsub : closedBall x₀ (ε / 2) ⊆ O := (closedBall_subset_ball (by linarith)).trans hε
  have hK : IsCompact (Icc (-T) T ×ˢ closedBall x₀ (ε / 2)) := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKsub : Icc (-T) T ×ˢ closedBall x₀ (ε / 2) ⊆ Set.univ ×ˢ O := fun q hq => ⟨mem_univ _, hsub hq.2⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ((h.deriv hO).1.continuousOn.mono hKsub)
  have hdiff : ∀ t, ∀ x ∈ O, HasFDerivAt (fun y => Φ (t, y)) (pX Φ (t, x)) x := fun t x hx =>
    ((h.1.contDiffAt ((isOpen_univ.prod hO).mem_nhds ⟨mem_univ t, hx⟩)).differentiableAt (by simp)).hasFDerivAt.comp x
      (hasFDerivAt_prodMk_right t x)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x t => Φ (t, x)) (F' := fun x t => pX Φ (t, x)) (s := closedBall x₀ (ε / 2))
    (bound := (Icc (-T) T).indicator fun _ => C) (closedBall_mem_nhds _ (by linarith)) ?_ (h.integrable hx₀)
    ((h.deriv hO).cont_line hx₀).aestronglyMeasurable ?_ ?_ ?_
  · filter_upwards [hO.mem_nhds hx₀] with x hx using (h.cont_line hx).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t x hx => ?_
    by_cases ht : t ∈ Icc (-T) T
    · rw [indicator_of_mem ht]
      exact hC (t, x) ⟨ht, hx⟩
    · rw [indicator_of_notMem ht, (h.deriv hO).2 t x ?_, norm_zero]
      by_contra hc
      exact ht (abs_le.1 (not_lt.1 hc))
  · exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  · exact Filter.Eventually.of_forall fun t x hx => hdiff t x (hsub hx)

theorem integral_good_contDiffOn (hO : IsOpen O) (k : ℕ) : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (Φ : ℝ × H → W) (T : ℝ), Good O Φ T → ContDiffOn ℝ k (fun x => ∫ t, Φ (t, x)) O := by
  induction k with
  | zero =>
    intro W _ _ _ Φ T h
    exact contDiffOn_zero.2 fun x hx => (h.hasFDerivAt hO hx).continuousAt.continuousWithinAt
  | succ k ih =>
    intro W _ _ _ Φ T h
    rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by norm_cast, contDiffOn_succ_iff_fderiv_of_isOpen hO]
    refine ⟨fun x hx => (h.hasFDerivAt hO hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact (ih (pX Φ) T (h.deriv hO)).congr fun x hx => (h.hasFDerivAt hO hx).fderiv

theorem good_smooth [CompleteSpace W] (hO : IsOpen O) (Φ : ℝ × H → W) (T : ℝ) (h : Good O Φ T) :
    ContDiffOn ℝ ∞ (fun x => ∫ t, Φ (t, x)) O :=
  contDiffOn_infty.2 fun k => integral_good_contDiffOn hO k Φ T h

theorem good_fderiv_apply [CompleteSpace W] (hO : IsOpen O) {Φ : ℝ × H → W} {T : ℝ} (h : Good O Φ T) {x : H}
    (hx : x ∈ O) (v : H) : fderiv ℝ (fun x => ∫ t, Φ (t, x)) x v = ∫ t, fderiv ℝ (fun y => Φ (t, y)) x v := by
  rw [(h.hasFDerivAt hO hx).fderiv, ContinuousLinearMap.integral_apply (((h.deriv hO).integrable hx))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have hd : DifferentiableAt ℝ Φ (t, x) :=
    (h.1.contDiffAt ((isOpen_univ.prod hO).mem_nhds ⟨mem_univ t, hx⟩)).differentiableAt (by simp)
  have e : HasFDerivAt (fun y => Φ (t, y)) (pX Φ (t, x)) x := hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  show pX Φ (t, x) v = fderiv ℝ (fun y => Φ (t, y)) x v
  rw [e.fderiv]

end PositivityTheory.RgBcC.LfSt.ChainPf.Cwave
end
end

section
noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cwave

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.RCalc (isOpen_GLs differentiableAt_of_smooth)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private theorem good_smul_bump_of_isWave {n : ℕ} (E : KMod n) (u : ℝ → Mat n → E.V) (hu : IsWave E u)
    (g : ℝ → ℝ) (T : ℝ) (hg : IsBump g T) :
    Good (GLs n) (fun q : ℝ × Mat n => ((g q.1 : ℂ)) • u q.1 q.2) T := by
  refine ⟨?_, ?_⟩
  · have h1 : ContDiff ℝ ∞ (fun q : ℝ × Mat n => ((g q.1 : ℂ))) :=
      Complex.ofRealCLM.contDiff.comp (hg.1.comp contDiff_fst)
    exact h1.contDiffOn.smul hu.1
  · intro t x ht
    simp [hg.2.2 t ht]

theorem paramInt : ParamInt := by
  intro n E u hu g T hg
  have hG := good_smul_bump_of_isWave E u hu g T hg
  refine ⟨good_smooth isOpen_GLs _ T hG, ?_⟩
  intro X x hx
  unfold Rd
  refine (good_fderiv_apply isOpen_GLs hG hx (x * X)).trans ?_
  congr 1
  funext t
  have hd : DifferentiableAt ℝ (u t) x := by
    apply differentiableAt_of_smooth _ hx
    have h2 : ContDiffOn ℝ ∞ (fun y : Mat n => Function.uncurry u (t, y)) (GLs n) :=
      hu.1.comp (contDiffOn_const.prodMk contDiffOn_id) (fun y hy => ⟨mem_univ _, hy⟩)
    exact h2
  have hf : fderiv ℝ (fun y => ((g t : ℂ)) • u t y) x = ((g t : ℂ)) • fderiv ℝ (u t) x :=
    (hd.hasFDerivAt.const_smul ((g t : ℂ))).fderiv
  show (fderiv ℝ (fun y => ((g t : ℂ)) • u t y) x) (x * X) = _
  rw [hf]
  rfl

end PositivityTheory.RgBcC.LfSt.ChainPf.Cwave
end
end

section
noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cact

variable {H Z : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {Γ : Type} [TopologicalSpace Γ] [T2Space Γ] [MeasurableSpace Γ] [BorelSpace Γ]

def LocSupp {W : Type} [Zero W] (O : Set H) (ι : Γ → Z) (Φ : H × Z → W) : Prop :=
  ∀ x₀ ∈ O, ∃ U : Set H, IsOpen U ∧ x₀ ∈ U ∧ U ⊆ O ∧
    ∃ K : Set Γ, IsCompact K ∧ ∀ x ∈ U, ∀ y : Γ, y ∉ K → Φ (x, ι y) = 0

def pd {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (Φ : H × Z → W) (p : H × Z) : H →L[ℝ] W :=
  (fderiv ℝ Φ p).comp (ContinuousLinearMap.inl ℝ H Z)

variable {O : Set H} {OZ : Set Z}

theorem contDiffOn_pd {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {Φ : H × Z → W}
    (hO : IsOpen O) (hOZ : IsOpen OZ) (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ)) : ContDiffOn ℝ ∞ (pd Φ) (O ×ˢ OZ) := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ Φ) (O ×ˢ OZ) := hΦ.fderiv_of_isOpen (hO.prod hOZ) (by simp)
  exact h1.clm_comp contDiffOn_const

theorem hasFDerivAt_pd {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {Φ : H × Z → W}
    (hO : IsOpen O) (hOZ : IsOpen OZ) (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ)) {x : H} {z : Z} (hx : x ∈ O)
    (hz : z ∈ OZ) : HasFDerivAt (fun x' => Φ (x', z)) (pd Φ (x, z)) x := by
  have hd : DifferentiableAt ℝ Φ (x, z) :=
    (hΦ.differentiableOn (by simp)).differentiableAt ((hO.prod hOZ).mem_nhds ⟨hx, hz⟩)
  exact hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x z)

theorem pd_eq_zero {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {Φ : H × Z → W}
    (hO : IsOpen O) (hOZ : IsOpen OZ) (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ)) {U : Set H} (hU : IsOpen U)
    (hUO : U ⊆ O) {z : Z} (hz : z ∈ OZ) (h0 : ∀ x ∈ U, Φ (x, z) = 0) {x : H} (hx : x ∈ U) : pd Φ (x, z) = 0 := by
  have h1 := hasFDerivAt_pd hO hOZ hΦ (hUO hx) hz
  have h2 : HasFDerivAt (fun x' => Φ (x', z)) (0 : H →L[ℝ] W) x :=
    (hasFDerivAt_const (0 : W) x).congr_of_eventuallyEq
      (eventually_of_mem (hU.mem_nhds hx) fun x' hx' => h0 x' hx')
  exact h1.unique h2

theorem locSupp_pd {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {Φ : H × Z → W} {ι : Γ → Z}
    (hO : IsOpen O) (hOZ : IsOpen OZ) (hι : ∀ y, ι y ∈ OZ) (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ))
    (hS : LocSupp O ι Φ) : LocSupp O ι (pd Φ) := by
  intro x₀ hx₀
  obtain ⟨U, hUo, hxU, hUO, K, hK, hKz⟩ := hS x₀ hx₀
  exact ⟨U, hUo, hxU, hUO, K, hK, fun x hx y hy =>
    pd_eq_zero hO hOZ hΦ hUo hUO (hι y) (fun x' hx' => hKz x' hx' y hy) hx⟩

theorem continuous_slice {W : Type} [TopologicalSpace W] {Φ : H × Z → W} {ι : Γ → Z} (hιc : Continuous ι)
    (hι : ∀ y, ι y ∈ OZ) (hΦ : ContinuousOn Φ (O ×ˢ OZ)) {x : H} (hx : x ∈ O) :
    Continuous fun y : Γ => Φ (x, ι y) :=
  hΦ.comp_continuous (continuous_const.prodMk hιc) fun y => ⟨hx, hι y⟩

section Int

variable (μ : Measure Γ) [IsFiniteMeasureOnCompacts μ] {ι : Γ → Z}

theorem integrable_slice {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {Φ : H × Z → W} (hιc : Continuous ι) (hι : ∀ y, ι y ∈ OZ) (hΦ : ContinuousOn Φ (O ×ˢ OZ)) {x : H} (hx : x ∈ O)
    {K : Set Γ} (hK : IsCompact K) (hKz : ∀ y : Γ, y ∉ K → Φ (x, ι y) = 0) :
    Integrable (fun y : Γ => Φ (x, ι y)) μ :=
  (continuous_slice hιc hι hΦ hx).integrable_of_hasCompactSupport (HasCompactSupport.intro hK hKz)

theorem integrable_pd {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {Φ : H × Z → W} (hO : IsOpen O) (hOZ : IsOpen OZ) (hιc : Continuous ι) (hι : ∀ y, ι y ∈ OZ)
    (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ)) (hS : LocSupp O ι Φ) {x : H} (hx : x ∈ O) :
    Integrable (fun y : Γ => pd Φ (x, ι y)) μ := by
  obtain ⟨U, hUo, hxU, hUO, K, hK, hKz⟩ := locSupp_pd hO hOZ hι hΦ hS x hx
  exact integrable_slice μ hιc hι (contDiffOn_pd hO hOZ hΦ).continuousOn hx hK fun y hy => hKz x hxU y hy

theorem hasFDerivAt_int {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {Φ : H × Z → W} (hO : IsOpen O) (hOZ : IsOpen OZ) (hιc : Continuous ι) (hι : ∀ y, ι y ∈ OZ)
    (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ)) (hS : LocSupp O ι Φ) {x₀ : H} (hx₀ : x₀ ∈ O) :
    HasFDerivAt (fun x => ∫ y : Γ, Φ (x, ι y) ∂μ) (∫ y : Γ, pd Φ (x₀, ι y) ∂μ) x₀ := by
  haveI : CompleteSpace W := FiniteDimensional.complete ℝ W
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  obtain ⟨U, hUo, hxU, hUO, K, hK, hKz⟩ := hS x₀ hx₀
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hUo x₀ hxU
  have hcb : closedBall x₀ (r / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hrU
  have hpdc : ContinuousOn (pd Φ) (O ×ˢ OZ) := (contDiffOn_pd hO hOZ hΦ).continuousOn
  have hcomp : IsCompact (closedBall x₀ (r / 2) ×ˢ K) := (isCompact_closedBall x₀ (r / 2)).prod hK
  have hcont : ContinuousOn (fun q : H × Γ => ‖pd Φ (q.1, ι q.2)‖) (closedBall x₀ (r / 2) ×ˢ K) := by
    refine (hpdc.comp (continuous_fst.prodMk (hιc.comp continuous_snd)).continuousOn ?_).norm
    intro q hq
    exact ⟨hUO (hcb hq.1), hι q.2⟩
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hcont
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (F' := fun x y => pd Φ (x, ι y)) (s := ball x₀ (r / 2))
    (bound := K.indicator fun _ => C) (ball_mem_nhds x₀ (by linarith)) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hUo.mem_nhds hxU] with x hx
    exact (continuous_slice hιc hι hΦ.continuousOn (hUO hx)).aestronglyMeasurable
  · exact integrable_slice μ hιc hι hΦ.continuousOn hx₀ hK fun y hy => hKz x₀ hxU y hy
  · exact (continuous_slice hιc hι hpdc hx₀).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y x hx => ?_
    by_cases hy : y ∈ K
    · rw [indicator_of_mem hy]
      have := hC (x, y) ⟨ball_subset_closedBall hx, hy⟩
      simpa using this
    · rw [indicator_of_notMem hy, pd_eq_zero hO hOZ hΦ hUo hUO (hι y) (fun x' hx' => hKz x' hx' y hy)
        (hcb (ball_subset_closedBall hx))]
      simp
  · exact (integrable_indicator_iff hKm).2 (integrableOn_const hK.measure_lt_top.ne)
  · exact Filter.Eventually.of_forall fun y x hx =>
      hasFDerivAt_pd hO hOZ hΦ (hUO (hcb (ball_subset_closedBall hx))) (hι y)

theorem contDiffOn_int_nat (hO : IsOpen O) (hOZ : IsOpen OZ) (hιc : Continuous ι) (hι : ∀ y, ι y ∈ OZ) :
    ∀ (m : ℕ) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {Φ : H × Z → W}, ContDiffOn ℝ ∞ Φ (O ×ˢ OZ) → LocSupp O ι Φ →
    ContDiffOn ℝ m (fun x => ∫ y : Γ, Φ (x, ι y) ∂μ) O := by
  intro m
  induction m with
  | zero =>
    intro W _ _ _ Φ hΦ hS
    refine contDiffOn_zero.2 fun x hx => ?_
    exact (hasFDerivAt_int μ hO hOZ hιc hι hΦ hS hx).continuousAt.continuousWithinAt
  | succ m ih =>
    intro W _ _ _ Φ hΦ hS
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiffOn_succ_iff_fderiv_of_isOpen hO]
    refine ⟨fun x hx => (hasFDerivAt_int μ hO hOZ hιc hι hΦ hS hx).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    have h1 := ih (contDiffOn_pd hO hOZ hΦ) (locSupp_pd hO hOZ hι hΦ hS)
    exact h1.congr fun x hx => (hasFDerivAt_int μ hO hOZ hιc hι hΦ hS hx).fderiv

theorem contDiffOn_int {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {Φ : H × Z → W} (hO : IsOpen O) (hOZ : IsOpen OZ) (hιc : Continuous ι) (hι : ∀ y, ι y ∈ OZ)
    (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ)) (hS : LocSupp O ι Φ) :
    ContDiffOn ℝ ∞ (fun x => ∫ y : Γ, Φ (x, ι y) ∂μ) O :=
  contDiffOn_infty.2 fun m => contDiffOn_int_nat μ hO hOZ hιc hι m hΦ hS

end Int

end PositivityTheory.RgBcC.LfSt.ChainPf.Cact
end
end

section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology Metric Set
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cact

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open GlobalTheory.CompanionTheory.LengthGL (isOpen_GLs contDiffOn_inv mem_GLs_val isCompact_G lg_mul_le fderiv_inv_mul
  differentiableAt_inv contDiffOn_lg)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem inv_mem {a : Mat n} (ha : a ∈ GLs n) : a⁻¹ ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq, Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at *
  exact inv_ne_zero ha

theorem mul_mem {a b : Mat n} (ha : a ∈ GLs n) (hb : b ∈ GLs n) : a * b ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq, Matrix.det_mul] at *
  exact mul_ne_zero ha hb

theorem isUnit_det {a : Mat n} (ha : a ∈ GLs n) : IsUnit a.det := isUnit_iff_ne_zero.2 ha

def mulR (z : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => w * z, map_add' := fun a b => Matrix.add_mul a b z,
      map_smul' := fun c a => Matrix.smul_mul c a z }

def mulL (x : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => x * w, map_add' := fun a b => Matrix.mul_add x a b,
      map_smul' := fun c a => Matrix.mul_smul x c a }

theorem cdo_mul {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {s : Set X} {A B : X → Mat n}
    (hA : ContDiffOn ℝ ∞ A s) (hB : ContDiffOn ℝ ∞ B s) : ContDiffOn ℝ ∞ (fun x => A x * B x) s := by
  have hAe : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) s := fun i j =>
    (GlobalTheory.CompanionTheory.LengthGL.ent i j).contDiff.comp_contDiffOn hA
  have hBe : ∀ i j, ContDiffOn ℝ ∞ (fun x => B x i j) s := fun i j =>
    (GlobalTheory.CompanionTheory.LengthGL.ent i j).contDiff.comp_contDiffOn hB
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun c _ => (hAe i c).mul (hBe c j)

def Psi {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (k : Mat n → (V →L[ℂ] V)) (f : Mat n → V)
    (p : Mat n × Mat n) : V :=
  k (p.1⁻¹ * p.2) (f p.2)

theorem contDiffOn_Psi {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {k : Mat n → (V →L[ℂ] V)}
    {f : Mat n → V} (hk : ContDiffOn ℝ ∞ k (GLs n)) (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (Psi k f) (GLs n ×ˢ GLs n) := by
  have h1 : ContDiffOn ℝ ∞ (fun p : Mat n × Mat n => p.1⁻¹ * p.2) (GLs n ×ˢ GLs n) :=
    cdo_mul (contDiffOn_inv.comp contDiffOn_fst fun p hp => hp.1) contDiffOn_snd
  have h2 : MapsTo (fun p : Mat n × Mat n => p.1⁻¹ * p.2) (GLs n ×ˢ GLs n) (GLs n) :=
    fun p hp => mul_mem (inv_mem hp.1) hp.2
  have h3 : ContDiffOn ℝ ∞ (fun p : Mat n × Mat n => k (p.1⁻¹ * p.2)) (GLs n ×ˢ GLs n) := hk.comp h1 h2
  have h4 : ContDiffOn ℝ ∞ (fun p : Mat n × Mat n => f p.2) (GLs n ×ˢ GLs n) :=
    hf.comp contDiffOn_snd fun (p : Mat n × Mat n) (hp : p ∈ GLs n ×ˢ GLs n) => hp.2
  have h3' : ContDiffOn ℝ ∞ (fun p : Mat n × Mat n => (k (p.1⁻¹ * p.2)).restrictScalars ℝ) (GLs n ×ˢ GLs n) :=
    (ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ).contDiff.comp_contDiffOn h3
  exact h3'.clm_apply h4

theorem locSupp_Psi {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {k : Mat n → (V →L[ℂ] V)}
    (f : Mat n → V) (hkc : Cpt k) : LocSupp (GLs n) (fun y : G n => y.val) (Psi k f) := by
  obtain ⟨R, hR⟩ := hkc
  intro x₀ hx₀
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 isOpen_GLs x₀ hx₀
  have hcb : closedBall x₀ (r / 2) ⊆ GLs n := (closedBall_subset_ball (by linarith)).trans hrU
  haveI : ProperSpace (Mat n) := FiniteDimensional.proper ℝ (Mat n)
  obtain ⟨M, hM⟩ := (isCompact_closedBall x₀ (r / 2)).exists_bound_of_continuousOn
    (contDiffOn_lg.continuousOn.mono hcb)
  refine ⟨ball x₀ (r / 2), isOpen_ball, mem_ball_self (by linarith), ball_subset_closedBall.trans hcb,
    {y : G n | lg y.val ≤ R + M}, isCompact_G _, fun x hx y hy => ?_⟩
  have hxG : x ∈ GLs n := hcb (ball_subset_closedBall hx)
  have hlx : lg x ≤ M := (le_abs_self _).trans (by simpa using hM x (ball_subset_closedBall hx))
  have hy' : R + M < lg y.val := lt_of_not_ge hy
  have hsub : lg y.val ≤ lg x + lg (x⁻¹ * y.val) := by
    have := lg_mul_le x (x⁻¹ * y.val)
    rwa [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_det hxG)] at this
  have hz : k (x⁻¹ * y.val) = 0 := hR _ (mul_mem (inv_mem hxG) (mem_GLs_val y)) (by linarith)
  simp [Psi, hz]

section Int

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

theorem act_eq_Psi (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V))
    (f : Mat n → E.V) {x : Mat n} (hx : x ∈ GLs n) :
    act μ E k f x = ∫ y : G n, Psi k f (x, y.val) ∂μ := by
  let u : G n := Matrix.nonsingInvUnit x (isUnit_det hx)
  have hu : (u : Mat n) = x := rfl
  rw [← integral_mul_left_eq_self (fun y : G n => Psi k f (x, y.val)) u]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Psi, Units.val_mul, hu, Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_det hx)]

theorem hasFDerivAt_Psi_slice {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {k : Mat n → (V →L[ℂ] V)}
    (f : Mat n → V) (hk : ContDiffOn ℝ ∞ k (GLs n)) {x z : Mat n} (hx : x ∈ GLs n) (hz : z ∈ GLs n) :
    HasFDerivAt (fun x' => Psi k f (x', z))
      (((ContinuousLinearMap.apply ℂ V (f z)).restrictScalars ℝ).comp
        ((fderiv ℝ k (x⁻¹ * z)).comp ((mulR z).comp (fderiv ℝ (fun y : Mat n => y⁻¹) x)))) x := by
  have hg : HasFDerivAt (fun x' : Mat n => x'⁻¹ * z) ((mulR z).comp (fderiv ℝ (fun y : Mat n => y⁻¹) x)) x :=
    (mulR z).hasFDerivAt.comp x (differentiableAt_inv hx).hasFDerivAt
  have hk' : HasFDerivAt k (fderiv ℝ k (x⁻¹ * z)) (x⁻¹ * z) :=
    ((hk.differentiableOn (by simp)).differentiableAt
      (isOpen_GLs.mem_nhds (mul_mem (inv_mem hx) hz))).hasFDerivAt
  have hev : HasFDerivAt (fun L : V →L[ℂ] V => L (f z)) ((ContinuousLinearMap.apply ℂ V (f z)).restrictScalars ℝ)
      (k (x⁻¹ * z)) :=
    ((ContinuousLinearMap.apply ℂ V (f z)).restrictScalars ℝ).hasFDerivAt
  exact hev.comp x (hk'.comp x hg)

theorem pd_Psi_apply (E : KMod n) {k : Mat n → (E.V →L[ℂ] E.V)} (f : Mat n → E.V) (hk : ContDiffOn ℝ ∞ k (GLs n))
    (hf : ContDiffOn ℝ ∞ f (GLs n)) {x z : Mat n} (hx : x ∈ GLs n) (hz : z ∈ GLs n) (X : Mat n) :
    pd (Psi k f) (x, z) (x * X) = Ld X k (x⁻¹ * z) (f z) := by
  have h1 := hasFDerivAt_pd isOpen_GLs isOpen_GLs (contDiffOn_Psi hk hf) hx hz
  have key : pd (Psi k f) (x, z) (x * X) =
      (fderiv ℝ k (x⁻¹ * z) (mulR z (fderiv ℝ (fun y : Mat n => y⁻¹) x (x * X)))) (f z) := by
    rw [h1.unique (hasFDerivAt_Psi_slice f hk hx hz)]
    rfl
  rw [key, fderiv_inv_mul hx X]
  have : mulR z (-(X * x⁻¹)) = -(X * (x⁻¹ * z)) := by
    show -(X * x⁻¹) * z = -(X * (x⁻¹ * z))
    rw [neg_mul, Matrix.mul_assoc]
  rw [this, map_neg]
  rfl

theorem actDer : ActDer := by
  intro _hU n _ _ μ _ E k f hk hkc hf
  have hΦ := contDiffOn_Psi hk hf
  have hS := locSupp_Psi f hkc
  have hιc : Continuous fun y : G n => y.val := Units.continuous_val
  have hι : ∀ y : G n, (fun y : G n => y.val) y ∈ GLs n := mem_GLs_val
  have hI := contDiffOn_int μ isOpen_GLs isOpen_GLs hιc hι hΦ hS
  refine ⟨hI.congr fun x hx => act_eq_Psi μ E k f hx, fun X x hx => ?_⟩
  have heq : act μ E k f =ᶠ[𝓝 x] fun x => ∫ y : G n, Psi k f (x, y.val) ∂μ :=
    eventually_of_mem (isOpen_GLs.mem_nhds hx) fun x' hx' => act_eq_Psi μ E k f hx'
  have hD : HasFDerivAt (fun x => ∫ y : G n, Psi k f (x, y.val) ∂μ)
      (∫ y : G n, pd (Psi k f) (x, y.val) ∂μ) x := hasFDerivAt_int μ isOpen_GLs isOpen_GLs hιc hι hΦ hS hx
  have hint : Integrable (fun y : G n => pd (Psi k f) (x, y.val)) μ :=
    integrable_pd μ isOpen_GLs isOpen_GLs hιc hι hΦ hS hx
  have hA : HasFDerivAt (act μ E k f) (∫ y : G n, pd (Psi k f) (x, y.val) ∂μ) x := hD.congr_of_eventuallyEq heq
  have h1 : Rd X (act μ E k f) x = (∫ y : G n, pd (Psi k f) (x, y.val) ∂μ) (x * X) :=
    congrArg (fun L => L (x * X)) hA.fderiv
  rw [h1, ContinuousLinearMap.integral_apply hint]
  let u : G n := Matrix.nonsingInvUnit x (isUnit_det hx)
  have hu : (u : Mat n) = x := rfl
  rw [← integral_mul_left_eq_self (fun y : G n => pd (Psi k f) (x, y.val) (x * X)) u]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Units.val_mul, hu]
  rw [pd_Psi_apply E f hk hf hx (mul_mem hx (mem_GLs_val y)) X,
    Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_det hx)]

end Int

end PositivityTheory.RgBcC.LfSt.ChainPf.Cact
end
end

section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology Metric Set
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cact

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open GlobalTheory.CompanionTheory.LengthGL (isOpen_GLs mem_GLs_val isCompact_G contDiffOn_lg)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem fderiv_eq_zero_of_lg {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {g : Mat n → V} {R : ℝ}
    (hg : ∀ y ∈ GLs n, R < lg y → g y = 0) {y : Mat n} (hy : y ∈ GLs n) (hR : R < lg y) : fderiv ℝ g y = 0 := by
  have hN : IsOpen (GLs n ∩ lg ⁻¹' Ioi R) := contDiffOn_lg.continuousOn.isOpen_inter_preimage isOpen_GLs isOpen_Ioi
  have h0 : g =ᶠ[𝓝 y] fun _ => (0 : V) :=
    eventually_of_mem (hN.mem_nhds ⟨hy, hR⟩) fun w hw => hg w hw.1 hw.2
  rw [h0.fderiv_eq]
  exact fderiv_const_apply 0

theorem continuousOn_Rd {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {g : Mat n → V}
    (hg : ContDiffOn ℝ ∞ g (GLs n)) (X : Mat n) : ContinuousOn (Rd X g) (GLs n) := by
  have h1 : ContinuousOn (fderiv ℝ g) (GLs n) := hg.continuousOn_fderiv_of_isOpen isOpen_GLs (by simp)
  have h2 : ContinuousOn (fun y : Mat n => y * X) (GLs n) := (cdo_mul contDiffOn_id contDiffOn_const).continuousOn
  exact h1.clm_apply h2

theorem ibpAct : IBPAct := by
  intro _hU hRc n _ _ μ _ E k f hk hkc hf X x hx
  have hmap : MapsTo (fun y : Mat n => x * y) (GLs n) (GLs n) := fun y hy => mul_mem hx hy
  have hxy : ContDiffOn ℝ ∞ (fun y : Mat n => x * y) (GLs n) := cdo_mul contDiffOn_const contDiffOn_id
  have hkr : ContDiffOn ℝ ∞ (fun y => (k y).restrictScalars ℝ) (GLs n) :=
    (ContinuousLinearMap.restrictScalarsL ℂ E.V E.V ℝ ℝ).contDiff.comp_contDiffOn hk
  have hF : ContDiffOn ℝ ∞ (fun y : Mat n => k y (f (x * y))) (GLs n) := hkr.clm_apply (hf.comp hxy hmap)
  obtain ⟨R, hR⟩ := hkc
  have hFc : Cpt (fun y : Mat n => k y (f (x * y))) := ⟨R, fun y hy h => by simp [hR y hy h]⟩
  have h0 := (hRc n).2.2 μ E.V (fun y : Mat n => k y (f (x * y))) hF hFc X
  have hdF : ∀ y ∈ GLs n, Rd X (fun y : Mat n => k y (f (x * y))) y =
      Rd X k y (f (x * y)) + k y (Rd X f (x * y)) := by
    intro y hy
    have hk' : HasFDerivAt k (fderiv ℝ k y) y :=
      ((hk.differentiableOn (by simp)).differentiableAt (isOpen_GLs.mem_nhds hy)).hasFDerivAt
    have hk2 : HasFDerivAt (fun y => (k y).restrictScalars ℝ)
        ((ContinuousLinearMap.restrictScalarsL ℂ E.V E.V ℝ ℝ).comp (fderiv ℝ k y)) y :=
      (ContinuousLinearMap.restrictScalarsL ℂ E.V E.V ℝ ℝ).hasFDerivAt.comp y hk'
    have hf' : HasFDerivAt f (fderiv ℝ f (x * y)) (x * y) :=
      ((hf.differentiableOn (by simp)).differentiableAt (isOpen_GLs.mem_nhds (hmap hy))).hasFDerivAt
    have hg : HasFDerivAt (fun y : Mat n => f (x * y)) ((fderiv ℝ f (x * y)).comp (mulL x)) y :=
      hf'.comp y (mulL x).hasFDerivAt
    have hFD := hk2.clm_apply hg
    have e1 : Rd X (fun y : Mat n => k y (f (x * y))) y =
        k y (fderiv ℝ f (x * y) (x * (y * X))) + (fderiv ℝ k y (y * X)) (f (x * y)) := by
      exact (congrArg (fun L => L (y * X)) hFD.fderiv).trans rfl
    rw [e1, ← Matrix.mul_assoc]
    show _ = fderiv ℝ k y (y * X) (f (x * y)) + k y (fderiv ℝ f (x * y) (x * y * X))
    exact add_comm _ _
  have hK := isCompact_G (n := n) R
  have hA : Integrable (fun y : G n => Rd X k y.val (f (x * y.val))) μ := by
    refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.intro hK fun y hy => ?_)
    · have hc : ContinuousOn (fun y : Mat n => Rd X k y (f (x * y))) (GLs n) :=
        (continuousOn_Rd hk X).clm_apply (hf.continuousOn.comp hxy.continuousOn hmap)
      exact hc.comp_continuous Units.continuous_val mem_GLs_val
    · have : fderiv ℝ k y.val = 0 := fderiv_eq_zero_of_lg hR (mem_GLs_val y) (lt_of_not_ge hy)
      simp [Rd, this]
  have hB : Integrable (fun y : G n => k y.val (Rd X f (x * y.val))) μ := by
    refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.intro hK fun y hy => ?_)
    · have hc : ContinuousOn (fun y : Mat n => k y (Rd X f (x * y))) (GLs n) :=
        hk.continuousOn.clm_apply ((continuousOn_Rd hf X).comp hxy.continuousOn hmap)
      exact hc.comp_continuous Units.continuous_val mem_GLs_val
    · simp [hR y.val (mem_GLs_val y) (lt_of_not_ge hy)]
  have hsum : ∫ y : G n, Rd X (fun y : Mat n => k y (f (x * y))) y.val ∂μ =
      ∫ y : G n, Rd X k y.val (f (x * y.val)) ∂μ + ∫ y : G n, k y.val (Rd X f (x * y.val)) ∂μ := by
    rw [← integral_add hA hB]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => hdF y.val (mem_GLs_val y))
  rw [hsum] at h0
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact h0

end PositivityTheory.RgBcC.LfSt.ChainPf.Cact
end
end

section
noncomputable section

open Matrix Finset

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cdc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat hb)

variable {n : ℕ}

theorem isOpen_GLs : IsOpen (GLs n) :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

theorem hb_herm (p : Fin n × Fin n) : (hb p : Mat n).IsHermitian := by
  obtain ⟨a, b⟩ := p
  unfold hb
  split_ifs with h1 h2
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_single]
  · simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_single]
    simp [add_comm]
  · simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_single]
    simp [star_mul', Complex.conj_I]
    rw [← smul_neg, neg_sub]

theorem hb_apply (p : Fin n × Fin n) (i j : Fin n) : (hb p : Mat n) i j =
    if p.1 = p.2 then (if p.1 = i ∧ p.1 = j then 1 else 0)
    else if p.1 < p.2 then ((Real.sqrt 2)⁻¹ : ℂ) * ((if p.1 = i ∧ p.2 = j then 1 else 0) + (if p.2 = i ∧ p.1 = j then 1 else 0))
    else (((Real.sqrt 2)⁻¹ : ℂ) * Complex.I) * ((if p.1 = i ∧ p.2 = j then 1 else 0) - (if p.2 = i ∧ p.1 = j then 1 else 0)) := by
  obtain ⟨a, b⟩ := p
  unfold hb
  dsimp only
  by_cases hab : a = b
  · subst hab
    simp only [if_true, Matrix.single_apply]
  · rw [if_neg hab, if_neg hab]
    by_cases hlt : a < b
    · rw [if_pos hlt, if_pos hlt]
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply, smul_eq_mul]
    · rw [if_neg hlt, if_neg hlt]
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply, smul_eq_mul]

theorem hb_tr (H : Mat n) (p : Fin n × Fin n) : (H * hb p).trace =
    if p.1 = p.2 then H p.1 p.1
    else if p.1 < p.2 then ((Real.sqrt 2)⁻¹ : ℂ) * (H p.2 p.1 + H p.1 p.2)
    else (((Real.sqrt 2)⁻¹ : ℂ) * Complex.I) * (H p.2 p.1 - H p.1 p.2) := by
  obtain ⟨a, b⟩ := p
  unfold hb
  dsimp only
  by_cases hab : a = b
  · subst hab
    simp [Matrix.trace_mul_single]
  · rw [if_neg hab, if_neg hab]
    by_cases hlt : a < b
    · rw [if_pos hlt, if_pos hlt]
      simp [Matrix.mul_add, Matrix.trace_add, Matrix.trace_mul_single]
      ring
    · rw [if_neg hlt, if_neg hlt]
      simp [Matrix.mul_sub, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_mul_single]

theorem key_pair (h : ℂ) (s : ℝ) (hs : s * s = 2) :
    (((((s : ℂ))⁻¹ * (star h + h)).re : ℝ) : ℂ) * ((s : ℂ))⁻¹ +
      (((((s : ℂ))⁻¹ * Complex.I * (h - star h)).re : ℝ) : ℂ) * (-((s : ℂ))⁻¹ * Complex.I) = h := by
  rw [← Complex.ofReal_inv]
  have hc2 : s⁻¹ * s⁻¹ = 1 / 2 := by rw [← mul_inv, hs]; norm_num
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
    linear_combination (2 * h.re) * hc2
  · simp [Complex.mul_re, Complex.mul_im]
    linear_combination (2 * h.im) * hc2

theorem key_pair2 (h : ℂ) (s : ℝ) (hs : s * s = 2) :
    (((((s : ℂ))⁻¹ * Complex.I * (star h - h)).re : ℝ) : ℂ) * (((s : ℂ))⁻¹ * Complex.I) +
      (((((s : ℂ))⁻¹ * (h + star h)).re : ℝ) : ℂ) * ((s : ℂ))⁻¹ = h := by
  rw [← Complex.ofReal_inv]
  have hc2 : s⁻¹ * s⁻¹ = 1 / 2 := by rw [← mul_inv, hs]; norm_num
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
    linear_combination (2 * h.re) * hc2
  · simp [Complex.mul_re, Complex.mul_im]
    linear_combination (2 * h.im) * hc2

theorem hb_expand (H : Mat n) (hH : H.IsHermitian) : ∑ p, ((H * hb p).trace.re : ℝ) • (hb p : Mat n) = H := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  have hji : H j i = star (H i j) := (hH.apply j i).symm
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  by_cases hij : i = j
  · subst hij
    have him : (H i i).im = 0 := by
      have := congrArg Complex.im (hH.apply i i)
      simp only [Complex.star_def, Complex.conj_im] at this
      linarith
    rw [Finset.sum_eq_single (i, i)]
    · rw [hb_tr, hb_apply]
      simp only [if_true, and_self, Complex.real_smul, mul_one]
      apply Complex.ext <;> simp [him]
    · intro p _ hp
      obtain ⟨a, b⟩ := p
      have hne : ¬(a = i ∧ b = i) := fun h => hp (by rw [h.1, h.2])
      have hne' : ¬(b = i ∧ a = i) := fun h => hne ⟨h.2, h.1⟩
      rw [hb_apply]
      dsimp only
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl, if_neg hne, smul_zero]
      · rw [if_neg hab, if_neg hne, if_neg hne']
        split_ifs <;> simp
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hne : (i, j) ≠ (j, i) := fun h => hij (Prod.mk.inj h).1
    rw [Finset.sum_eq_add (i, j) (j, i) hne]
    · rw [hb_tr, hb_tr, hb_apply, hb_apply]
      dsimp only
      rw [if_neg hij, if_neg (Ne.symm hij)]
      simp only [hji, Complex.real_smul]
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · rw [if_pos hlt, if_pos hlt, if_neg (not_lt.mpr hlt.le), if_neg (not_lt.mpr hlt.le)]
        simp only [and_self, if_true, hij, Ne.symm hij, false_and, if_false, add_zero, zero_sub, mul_one, mul_neg]
        have := key_pair (H i j) (Real.sqrt 2) hs
        convert this using 1
        ring
      · simp only [hlt, not_lt.mpr hlt.le, if_true, if_false]
        simp only [and_self, if_true, hij, Ne.symm hij, false_and, and_false, if_false, add_zero, zero_add, sub_zero,
          zero_sub, mul_one, mul_neg]
        have := key_pair2 (H i j) (Real.sqrt 2) hs
        convert this using 1
    · intro p _ hp
      obtain ⟨a, b⟩ := p
      have h1 : ¬(a = i ∧ b = j) := fun h => hp.1 (by rw [h.1, h.2])
      have h2 : ¬(b = i ∧ a = j) := fun h => hp.2 (by rw [h.1, h.2])
      rw [hb_apply]
      dsimp only
      by_cases hab : a = b
      · subst hab
        have h3 : ¬(a = i ∧ a = j) := fun h => hij (h.1.symm.trans h.2)
        rw [if_pos rfl, if_neg h3, smul_zero]
      · rw [if_neg hab, if_neg h1, if_neg h2]
        split_ifs <;> simp
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h

theorem unit_mul_star (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 * (k.1)ᴴ = 1 := by
  have := Matrix.mem_unitaryGroup_iff.mp k.2
  rwa [Matrix.star_eq_conjTranspose] at this

theorem unit_star_mul (k : Matrix.unitaryGroup (Fin n) ℂ) : (k.1)ᴴ * k.1 = 1 := by
  have := Matrix.mem_unitaryGroup_iff'.mp k.2
  rwa [Matrix.star_eq_conjTranspose] at this

theorem conj_herm (k : Mat n) (H : Mat n) (hH : H.IsHermitian) : (k * H * kᴴ).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH.eq, Matrix.mul_assoc]

theorem expand_conj (k : Matrix.unitaryGroup (Fin n) ℂ) (H : Mat n) (hH : H.IsHermitian) :
    ∑ p, ((H * (k.1 * hb p * (k.1)ᴴ)).trace.re : ℝ) • (k.1 * hb p * (k.1)ᴴ) = H := by
  have h1 := hb_expand ((k.1)ᴴ * H * k.1) (by
    have := conj_herm (k.1)ᴴ H hH
    rwa [Matrix.conjTranspose_conjTranspose] at this)
  have h2 : ∀ p, ((k.1)ᴴ * H * k.1 * hb p).trace = (H * (k.1 * hb p * (k.1)ᴴ)).trace := by
    intro p
    rw [show (k.1)ᴴ * H * k.1 * hb p = (k.1)ᴴ * (H * k.1 * hb p) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm, show H * k.1 * hb p * (k.1)ᴴ = H * (k.1 * hb p * (k.1)ᴴ) by simp only [Matrix.mul_assoc]]
  simp only [h2] at h1
  have h3 := congrArg (fun M => k.1 * M * (k.1)ᴴ) h1
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul] at h3
  rw [h3, ← Matrix.mul_assoc, ← Matrix.mul_assoc, unit_mul_star, Matrix.one_mul, Matrix.mul_assoc, unit_mul_star,
    Matrix.mul_one]

theorem basis_inv {W : Type} [AddCommGroup W] [Module ℝ W] (B : Mat n →ₗ[ℝ] Mat n →ₗ[ℝ] W)
    (k : Matrix.unitaryGroup (Fin n) ℂ) :
    ∑ p, B (k.1 * hb p * (k.1)ᴴ) (k.1 * hb p * (k.1)ᴴ) = ∑ p, B (hb p) (hb p) := by
  set Y : Fin n × Fin n → Mat n := fun p => k.1 * hb p * (k.1)ᴴ with hYdef
  have hY : ∀ p, (Y p).IsHermitian := fun p => conj_herm k.1 (hb p) (hb_herm p)
  calc ∑ p, B (Y p) (Y p) = ∑ p, B (Y p) (∑ q, ((Y p * hb q).trace.re : ℝ) • (hb q : Mat n)) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hb_expand _ (hY p)]
    _ = ∑ p, ∑ q, ((Y p * hb q).trace.re : ℝ) • B (Y p) (hb q) := by
        simp only [map_sum, map_smul]
    _ = ∑ q, ∑ p, ((hb q * Y p).trace.re : ℝ) • B (Y p) (hb q) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
        rw [Matrix.trace_mul_comm]
    _ = ∑ q, B (∑ p, ((hb q * Y p).trace.re : ℝ) • Y p) (hb q) := by
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    _ = ∑ q, B (hb q) (hb q) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [expand_conj k (hb q) (hb_herm q)]

end PositivityTheory.RgBcC.LfSt.ChainPf.Cdc
end
end

section
noncomputable section

open Matrix Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cdc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def mulRL (c : Mat n) : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ c)

@[simp] theorem mulRL_apply (c y : Mat n) : mulRL c y = y * c := rfl

def mulLRL (a c : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap ((LinearMap.mulLeft ℝ a).comp (LinearMap.mulRight ℝ c))

@[simp] theorem mulLRL_apply (a c y : Mat n) : mulLRL a c y = a * (y * c) := rfl

theorem mem_GLs_mul {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

theorem unit_mem (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq]
  intro h
  have := congrArg Matrix.det (unit_star_mul k)
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at this
  exact zero_ne_one this

theorem unit_star_mem (k : Matrix.unitaryGroup (Fin n) ℂ) : (k.1)ᴴ ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq]
  intro h
  have := congrArg Matrix.det (unit_mul_star k)
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at this
  exact zero_ne_one this

theorem inv_val (k : Matrix.unitaryGroup (Fin n) ℂ) : (k⁻¹ : Matrix.unitaryGroup (Fin n) ℂ).1 = (k.1)ᴴ := by
  rw [← Matrix.star_eq_conjTranspose]
  rfl

theorem fderiv_right {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (F : Mat n → W) (c g : Mat n) (Φ : W →L[ℝ] W)
    (hF : DifferentiableAt ℝ F (g * c)) (hF' : DifferentiableAt ℝ F g)
    (hEq : (fun y => F (y * c)) =ᶠ[nhds g] fun y => Φ (F y)) (Z : Mat n) :
    fderiv ℝ F (g * c) (Z * c) = Φ (fderiv ℝ F g Z) := by
  have e := hEq.fderiv_eq (𝕜 := ℝ)
  have h1 : HasFDerivAt (fun y => F (y * c)) ((fderiv ℝ F (g * c)).comp (mulRL c)) g := by
    exact hF.hasFDerivAt.comp g (mulRL c).hasFDerivAt
  have h2 : HasFDerivAt (fun y => Φ (F y)) (Φ.comp (fderiv ℝ F g)) g := Φ.hasFDerivAt.comp g hF'.hasFDerivAt
  rw [h1.fderiv, h2.fderiv] at e
  have := congrArg (fun L : Mat n →L[ℝ] W => L Z) e
  simpa using this

section Cx

variable {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
  {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}

theorem fr_star (h : CxData lam E Fr ε ι S Γ T) (k : Matrix.unitaryGroup (Fin n) ℂ) : Fr (k.1)ᴴ = E.ρ k⁻¹ := by
  rw [← inv_val, h.onK]

theorem rho_mul_inv (k : Matrix.unitaryGroup (Fin n) ℂ) : E.ρ k * E.ρ k⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

theorem eps_rho_inv (h : CxData lam E Fr ε ι S Γ T) (k : Matrix.unitaryGroup (Fin n) ℂ) (X : Mat n) (hX : X.IsHermitian) :
    ε X * E.ρ k⁻¹ = E.ρ k⁻¹ * ε (k.1 * X * (k.1)ᴴ) := by
  have := h.frε (k.1)ᴴ (unit_star_mem k) X hX
  rwa [fr_star h, Matrix.conjTranspose_conjTranspose] at this

theorem eps_rho (h : CxData lam E Fr ε ι S Γ T) (k : Matrix.unitaryGroup (Fin n) ℂ) (Y : Mat n) (hY : Y.IsHermitian) :
    ε Y * E.ρ k = E.ρ k * ε ((k.1)ᴴ * Y * k.1) := by
  have := h.frε k.1 (unit_mem k) Y hY
  rwa [h.onK] at this

theorem fr_diff (h : CxData lam E Fr ε ι S Γ T) {x : Mat n} (hx : x ∈ GLs n) : DifferentiableAt ℝ Fr x :=
  (h.smooth.differentiableOn (by simp)).differentiableAt (isOpen_GLs.mem_nhds hx)

theorem one_mem_GLs : (1 : Mat n) ∈ GLs n := by
  simp [GLs]

theorem dFr_conj (h : CxData lam E Fr ε ι S Γ T) (k : Matrix.unitaryGroup (Fin n) ℂ) (Y : Mat n) :
    fderiv ℝ Fr 1 ((k.1)ᴴ * (Y * k.1)) = E.ρ k⁻¹ * fderiv ℝ Fr 1 Y * E.ρ k := by
  set L : (E.V →L[ℂ] E.V) →L[ℝ] (E.V →L[ℂ] E.V) :=
    (ContinuousLinearMap.mulLeftRight ℂ (E.V →L[ℂ] E.V) (E.ρ k⁻¹) (E.ρ k)).restrictScalars ℝ with hL
  have hEq : (fun y => Fr ((k.1)ᴴ * (y * k.1))) =ᶠ[nhds (1 : Mat n)] fun y => L (Fr y) := by
    filter_upwards [isOpen_GLs.mem_nhds (one_mem_GLs (n := n))] with y hy
    rw [h.mul _ (unit_star_mem k) _ (mem_GLs_mul hy (unit_mem k)), h.mul _ hy _ (unit_mem k), fr_star h, h.onK]
    simp [hL, ContinuousLinearMap.mulLeftRight_apply, mul_assoc]
  have e := hEq.fderiv_eq (𝕜 := ℝ)
  have hpt : (k.1)ᴴ * ((1 : Mat n) * k.1) = 1 := by rw [Matrix.one_mul, unit_star_mul]
  have h1 : HasFDerivAt (fun y => Fr ((k.1)ᴴ * (y * k.1))) ((fderiv ℝ Fr 1).comp (mulLRL (k.1)ᴴ k.1)) 1 := by
    have hd := (fr_diff h (one_mem_GLs (n := n))).hasFDerivAt
    rw [← hpt] at hd
    have := hd.comp (1 : Mat n) (mulLRL (k.1)ᴴ k.1).hasFDerivAt
    rw [hpt] at this
    exact this
  have h2 : HasFDerivAt (fun y => L (Fr y)) (L.comp (fderiv ℝ Fr 1)) 1 :=
    L.hasFDerivAt.comp (1 : Mat n) (fr_diff h (one_mem_GLs (n := n))).hasFDerivAt
  rw [h1.fderiv, h2.fderiv] at e
  have := congrArg (fun M : Mat n →L[ℝ] (E.V →L[ℂ] E.V) => M Y) e
  simpa [hL, ContinuousLinearMap.mulLeftRight_apply] using this

end Cx

end PositivityTheory.RgBcC.LfSt.ChainPf.Cdc
end
end

section
noncomputable section

open Matrix Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cdc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem hb_conj_back (k : Matrix.unitaryGroup (Fin n) ℂ) (X : Mat n) :
    (k.1)ᴴ * ((k.1 * X * (k.1)ᴴ) * k.1) = X := by
  have h : (k.1)ᴴ * ((k.1 * X * (k.1)ᴴ) * k.1) = ((k.1)ᴴ * k.1) * X * ((k.1)ᴴ * k.1) := by
    simp only [Matrix.mul_assoc]
  rw [h, unit_star_mul]
  simp

theorem dCinCE : DCinCE := by
  intro n lam E Fr ε ι S Γ T hD f hf
  obtain ⟨hs, heq⟩ := hf
  have hdiff : ∀ x ∈ GLs n, DifferentiableAt ℝ f x := fun x hx =>
    (hs.differentiableOn (by simp)).differentiableAt (isOpen_GLs.mem_nhds hx)
  refine ⟨?_, ?_⟩
  · have hfa := contDiffOn_fderivWithin_apply (m := ∞) hs isOpen_GLs.uniqueDiffOn (le_of_eq rfl)
    unfold DC
    refine ContDiffOn.sum fun p _ => ?_
    have h1 : ContDiffOn ℝ ∞ (fun x => Rd (hb p) f x) (GLs n) := by
      refine (hfa.comp (contDiffOn_id.prodMk (mulRL (hb p)).contDiff.contDiffOn)
        (fun x hx => ⟨hx, Set.mem_univ _⟩)).congr fun x hx => ?_
      show fderiv ℝ f x (x * hb p) = fderivWithin ℝ f (GLs n) x (mulRL (hb p) x)
      rw [fderivWithin_of_isOpen isOpen_GLs hx, mulRL_apply]
    have h2 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ Fr 1 (hb p) (f x)) (GLs n) :=
      ((fderiv ℝ Fr 1 (hb p)).restrictScalars ℝ).contDiff.comp_contDiffOn hs
    exact ((ε (hb p)).restrictScalars ℝ).contDiff.comp_contDiffOn (h1.add h2)
  · intro g hg k
    have hgk : g * k.1 ∈ GLs n := mem_GLs_mul hg (unit_mem k)
    have hRd : ∀ X : Mat n, Rd X f (g * k.1) = E.ρ k⁻¹ (Rd (k.1 * X * (k.1)ᴴ) f g) := by
      intro X
      have hev : (fun y : Mat n => f (y * k.1)) =ᶠ[nhds g]
          fun y => ((E.ρ k⁻¹).restrictScalars ℝ) (f y) := by
        filter_upwards [isOpen_GLs.mem_nhds hg] with y hy
        simpa using heq y hy k
      have h := fderiv_right f k.1 g _ (hdiff _ hgk) (hdiff _ hg) hev (g * (k.1 * X * (k.1)ᴴ))
      have hm : g * (k.1 * X * (k.1)ᴴ) * k.1 = g * k.1 * X := by
        simp only [Matrix.mul_assoc, unit_star_mul, Matrix.mul_one]
      show fderiv ℝ f (g * k.1) (g * k.1 * X) = E.ρ k⁻¹ (fderiv ℝ f g (g * (k.1 * X * (k.1)ᴴ)))
      rw [← hm]
      simpa using h
    have hv : ∀ v, E.ρ k (E.ρ k⁻¹ v) = v := by
      intro v
      rw [← ContinuousLinearMap.mul_apply, rho_mul_inv]
      rfl
    have hdF : ∀ (X : Mat n) (v : E.V), (fderiv ℝ Fr 1 X) (E.ρ k⁻¹ v)
        = E.ρ k⁻¹ (fderiv ℝ Fr 1 (k.1 * X * (k.1)ᴴ) v) := by
      intro X v
      have h := dFr_conj hD k (k.1 * X * (k.1)ᴴ)
      rw [hb_conj_back k X] at h
      rw [h, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hv]
    have heps : ∀ (X : Mat n), IsHermitian X → ∀ w,
        ε X (E.ρ k⁻¹ w) = E.ρ k⁻¹ (ε (k.1 * X * (k.1)ᴴ) w) := by
      intro X hX w
      rw [← ContinuousLinearMap.mul_apply, eps_rho_inv hD k X hX, ContinuousLinearMap.mul_apply]
    let B : Mat n →ₗ[ℝ] Mat n →ₗ[ℝ] E.V :=
      LinearMap.mk₂ ℝ (fun Y Z => ε Y (Rd Z f g + fderiv ℝ Fr 1 Z (f g)))
        (by
          intro a b c
          simp only [map_add, ContinuousLinearMap.add_apply]
          abel)
        (by intro c a b; simp only [map_smul, ContinuousLinearMap.smul_apply])
        (by
          intro a b c
          simp only [Rd, Matrix.mul_add, map_add, ContinuousLinearMap.add_apply]
          abel)
        (by
          intro c a b
          simp only [Rd, Matrix.mul_smul, map_smul, ContinuousLinearMap.smul_apply]
          rw [← smul_add]
          exact (ε a).map_smul_of_tower c _)
    have key := basis_inv B k
    unfold DC
    rw [heq g hg k]
    calc ∑ p : Fin n × Fin n, ε (hb p) (Rd (hb p) f (g * k.1) + fderiv ℝ Fr 1 (hb p) (E.ρ k⁻¹ (f g)))
        = ∑ p : Fin n × Fin n, E.ρ k⁻¹ (B (k.1 * hb p * (k.1)ᴴ) (k.1 * hb p * (k.1)ᴴ)) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [hRd, hdF, ← map_add, heps _ (hb_herm p)]
          rfl
      _ = E.ρ k⁻¹ (∑ p : Fin n × Fin n, B (hb p) (hb p)) := by rw [← map_sum, key]
      _ = _ := rfl

end PositivityTheory.RgBcC.LfSt.ChainPf.Cdc
end
end

section
noncomputable section

open Matrix Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cdc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def mulLL (a : Mat n) : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ a)

@[simp] theorem mulLL_apply (a y : Mat n) : mulLL a y = a * y := rfl

theorem hb_conj_back' (k : Matrix.unitaryGroup (Fin n) ℂ) (X : Mat n) :
    (k.1)ᴴ * (k.1 * X * (k.1)ᴴ) * k.1 = X := by
  rw [show (k.1)ᴴ * (k.1 * X * (k.1)ᴴ) * k.1 = (k.1)ᴴ * (((k.1 * X * (k.1)ᴴ)) * k.1) by simp only [Matrix.mul_assoc],
    hb_conj_back]

theorem kapEquiv : KapEquiv := by
  intro n lam E Fr ε ι S Γ T h k hk hkK
  have hopen := isOpen_GLs (n := n)
  have hkd : ∀ y ∈ GLs n, DifferentiableAt ℝ k y := fun y hy =>
    (hk.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hy)
  have hcont := hk.continuousOn_fderiv_of_isOpen hopen (by simp)
  refine ⟨?_, ?_, ?_⟩
  · unfold kapL
    apply continuousOn_finsetSum
    intro p _
    apply continuousOn_const.mul
    apply ContinuousOn.add
    · unfold Ld
      exact (hcont.clm_apply (mulLL (hb p)).continuous.continuousOn).neg
    · exact continuousOn_const.mul hk.continuousOn
  · unfold kapR
    apply continuousOn_finsetSum
    intro p _
    apply ContinuousOn.add
    · unfold Rd
      exact (hcont.clm_apply (mulRL (hb p)).continuous.continuousOn).neg.mul continuousOn_const
    · exact (hk.continuousOn.mul continuousOn_const).mul continuousOn_const
  · intro y hy k₂
    set Φ : (E.V →L[ℂ] E.V) →L[ℝ] (E.V →L[ℂ] E.V) :=
      ((ContinuousLinearMap.mul ℂ (E.V →L[ℂ] E.V)).flip (E.ρ k₂)).restrictScalars ℝ with hΦ
    have hyk : y * k₂.1 ∈ GLs n := mem_GLs_mul hy (unit_mem k₂)
    have hEq : (fun z => k (z * k₂.1)) =ᶠ[nhds y] fun z => Φ (k z) := by
      filter_upwards [hopen.mem_nhds hy] with z hz
      rw [hkK z hz k₂]
      rfl
    have hD : ∀ Z, fderiv ℝ k (y * k₂.1) (Z * k₂.1) = fderiv ℝ k y Z * E.ρ k₂ := fun Z =>
      fderiv_right k k₂.1 y Φ (hkd _ hyk) (hkd y hy) hEq Z
    constructor
    · have hLd : ∀ X, Ld X k (y * k₂.1) = Ld X k y * E.ρ k₂ := by
        intro X
        unfold Ld
        rw [show X * (y * k₂.1) = (X * y) * k₂.1 by rw [Matrix.mul_assoc], hD, neg_mul]
      unfold kapL
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hLd, hkK y hy k₂]
      simp only [mul_assoc, add_mul]
    · set Y : Fin n × Fin n → Mat n := fun p => k₂.1 * hb p * (k₂.1)ᴴ with hYdef
      have hRd : ∀ p, Rd (hb p) k (y * k₂.1) = Rd (Y p) k y * E.ρ k₂ := by
        intro p
        unfold Rd
        rw [show y * k₂.1 * hb p = (y * Y p) * k₂.1 by
          simp only [hYdef, Matrix.mul_assoc, unit_star_mul, Matrix.mul_one], hD]
      have hε : ∀ p, E.ρ k₂ * ε (hb p) = ε (Y p) * E.ρ k₂ := by
        intro p
        rw [eps_rho h k₂ (Y p) (conj_herm _ _ (hb_herm p)), hYdef]
        dsimp only
        rw [hb_conj_back']
      have hF : ∀ p, E.ρ k₂ * fderiv ℝ Fr 1 (hb p) = fderiv ℝ Fr 1 (Y p) * E.ρ k₂ := by
        intro p
        have := dFr_conj h k₂ (Y p)
        rw [hYdef, hb_conj_back] at this
        rw [this, ← mul_assoc, ← mul_assoc, rho_mul_inv, one_mul]
      let B : Mat n →ₗ[ℝ] Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V) := LinearMap.mk₂ ℝ
        (fun H H' => -(fderiv ℝ k y (y * H')) * ε H + k y * ε H * fderiv ℝ Fr 1 H')
        (fun H₁ H₂ H' => by simp only [map_add, mul_add, add_mul]; abel)
        (fun c H H' => by simp only [map_smul, mul_smul_comm, smul_mul_assoc, smul_add])
        (fun H H₁ H₂ => by simp only [Matrix.mul_add, map_add, neg_add, add_mul, mul_add]; abel)
        (fun c H H' => by
          simp only [Matrix.mul_smul, map_smul, neg_smul, smul_mul_assoc, mul_smul_comm, smul_add, ← smul_neg])
      have hkapR : kapR ε Fr k y = ∑ p, B (hb p) (hb p) := rfl
      have hterm : ∀ p, -(Rd (hb p) k (y * k₂.1)) * ε (hb p) + k (y * k₂.1) * ε (hb p) * fderiv ℝ Fr 1 (hb p) =
          B (Y p) (Y p) * E.ρ k₂ := by
        intro p
        rw [hRd, hkK y hy k₂]
        show -(Rd (Y p) k y * E.ρ k₂) * ε (hb p) + k y * E.ρ k₂ * ε (hb p) * fderiv ℝ Fr 1 (hb p) =
          (-(fderiv ℝ k y (y * Y p)) * ε (Y p) + k y * ε (Y p) * fderiv ℝ Fr 1 (Y p)) * E.ρ k₂
        rw [neg_mul, mul_assoc (Rd (Y p) k y), hε, mul_assoc (k y), hε, mul_assoc (k y), mul_assoc (ε (Y p)), hF]
        simp only [Rd, add_mul, neg_mul, mul_assoc]
      unfold kapR
      rw [Finset.sum_congr rfl (fun p _ => hterm p), ← Finset.sum_mul]
      congr 1
      rw [basis_inv B k₂]
      rfl

end PositivityTheory.RgBcC.LfSt.ChainPf.Cdc
end
end

section
namespace PositivityTheory.RgBcC.LfSt.ChainPf

open PositivityTheory.RgBcC

theorem chain_identity_multiplier_kernels (hU : Unimod) (hR : RCalc) (hL : LgFacts) : ChainOf' :=
  Done.chainOf'_of Cdc.dCinCE Cwave.paramInt Cact.actDer Cact.ibpAct Cdc.kapEquiv hU hR hL

end PositivityTheory.RgBcC.LfSt.ChainPf
end

section
namespace PositivityTheory.RgBcC.LfSt

theorem chainOf'_holds : PositivityTheory.RgBcC.ChainOf' := ChainPf.chain_identity_multiplier_kernels GlobalTheory.T.general_linear_group_unimodular GlobalTheory.T.right_derivative_calculus_holds GlobalTheory.T.length_function_facts_hold

end PositivityTheory.RgBcC.LfSt
end
