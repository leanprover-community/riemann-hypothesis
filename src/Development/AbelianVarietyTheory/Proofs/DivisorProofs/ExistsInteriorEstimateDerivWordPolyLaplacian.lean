import Mathlib
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
import GroundTheory.AutomorphicForms.DixmierMalliavin
import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftInvariantVectorFieldsExpCoordsSmoothFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ZeroMemSolSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DwSmoothLocalLinear
import Formalism.UnipotentAdelicQuotients.EllRegCheck
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefVFContDiffOn

section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction

noncomputable section

namespace GlobalTheory.HCA.SolSub

variable {d : ℕ}

theorem contDiff_dw {f : E d → ℂ} (hf : ContDiff ℝ ∞ f) : ∀ w : List (Fin d), ContDiff ℝ ∞ (dw w f)
  | [] => hf
  | j :: w => by
      have h := contDiff_dw hf w
      show ContDiff ℝ ∞ (fun x => fderiv ℝ (dw w f) x (ev j))
      exact (h.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem hasCompactSupport_dw {f : E d → ℂ} (hf : HasCompactSupport f) :
    ∀ w : List (Fin d), HasCompactSupport (dw w f)
  | [] => hf
  | j :: w => by
      have h := hasCompactSupport_dw hf w
      show HasCompactSupport (fun x => fderiv ℝ (dw w f) x (ev j))
      exact h.fderiv_apply (𝕜 := ℝ) (ev j)

theorem contDiff_mul_of_on {U : Set (E d)} (hU : IsOpen U) {b φ : E d → ℂ}
    (hb : ContDiffOn ℝ ∞ b U) (hφ : ContDiff ℝ ∞ φ) (hs : tsupport φ ⊆ U) :
    ContDiff ℝ ∞ (fun y => b y * φ y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (hb.contDiffAt (hU.mem_nhds hx)).mul hφ.contDiffAt
  · have hx' : x ∉ tsupport φ := fun h => hx (hs h)
    have h0 : φ =ᶠ[nhds x] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hx'
    have : (fun y => b y * φ y) =ᶠ[nhds x] fun _ => (0 : ℂ) := by
      filter_upwards [h0] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq this

theorem integrable_tr {ι : Type} (P : Sys d ι) {U : Set (E d)} (hU : IsOpen U)
    (ha : ∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) (i : ι) {φ : E d → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ U) :
    Integrable (P.tr i φ) := by
  unfold Sys.tr trOp
  refine integrable_finset_sum _ (fun n _ => integrable_finset_sum _ (fun w _ => ?_))
  refine Integrable.const_mul ?_ _
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (contDiff_dw (contDiff_mul_of_on hU (ha i n w) hφ hs) _).continuous
  · refine hasCompactSupport_dw ?_ _
    exact hc.mul_left

theorem norm_extendByZeroOffSubset_le {U : Set (E d)} (u : U →ᵇ ℂ) (x : E d) : ‖ext0 U u x‖ ≤ ‖u‖ := by
  by_cases hx : x ∈ U
  · simp only [ext0, hx, dif_pos]; exact u.norm_coe_le_norm _
  · simp [ext0, hx]

theorem aestronglyMeasurable_extendByZeroOffSubset {U : Set (E d)} (hU : IsOpen U) (u : U →ᵇ ℂ) :
    AEStronglyMeasurable (ext0 U u) volume := by
  have heq : U.indicator (ext0 U u) = ext0 U u := by
    funext x; by_cases hx : x ∈ U <;> simp [ext0, hx]
  have hc : ContinuousOn (ext0 U u) U := by
    rw [continuousOn_iff_continuous_restrict]
    have : U.domRestrict (ext0 U u) = u := by funext x; exact dif_pos x.2
    rw [this]; exact u.continuous
  have : AEStronglyMeasurable (U.indicator (ext0 U u)) volume :=
    (aestronglyMeasurable_indicator_iff hU.measurableSet).mpr (hc.aestronglyMeasurable hU.measurableSet)
  rwa [heq] at this

theorem integrable_extendByZeroOffSubset_mul {U : Set (E d)} (hU : IsOpen U) (u : U →ᵇ ℂ) {ψ : E d → ℂ}
    (hψ : Integrable ψ) : Integrable (fun x => ext0 U u x * ψ x) :=
  hψ.bdd_mul (aestronglyMeasurable_extendByZeroOffSubset hU u) (Filter.Eventually.of_forall fun x => norm_extendByZeroOffSubset_le u x)

theorem matrixExtendByZero_add {U : Set (E d)} (u v : U →ᵇ ℂ) (x : E d) :
    ext0 U (⇑(u + v)) x = ext0 U u x + ext0 U v x := by
  by_cases hx : x ∈ U <;> simp [ext0, hx]

theorem extendByZeroOffSubset_smul_apply {U : Set (E d)} (c : ℂ) (u : U →ᵇ ℂ) (x : E d) :
    ext0 U (⇑(c • u)) x = c * ext0 U u x := by
  by_cases hx : x ∈ U <;> simp [ext0, hx]

def pair {U : Set (E d)} (hU : IsOpen U) (ψ : E d → ℂ) (hψ : Integrable ψ) : (U →ᵇ ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun u => ∫ x, ext0 U u x * ψ x
      map_add' := fun u v => by
        simp only [matrixExtendByZero_add, add_mul]
        exact integral_add (integrable_extendByZeroOffSubset_mul hU u hψ) (integrable_extendByZeroOffSubset_mul hU v hψ)
      map_smul' := fun c u => by
        simp only [extendByZeroOffSubset_smul_apply, mul_assoc, RingHom.id_apply, smul_eq_mul]
        exact integral_const_mul c _ }
    (∫ x, ‖ψ x‖) (fun u => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      calc ‖∫ x, ext0 U u x * ψ x‖ ≤ ∫ x, ‖u‖ * ‖ψ x‖ := by
            refine norm_integral_le_of_norm_le (hψ.norm.const_mul _) (Filter.Eventually.of_forall ?_)
            intro x
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (norm_extendByZeroOffSubset_le u x) (norm_nonneg _)
        _ = (∫ x, ‖ψ x‖) * ‖u‖ := by rw [integral_const_mul, mul_comm])

end GlobalTheory.HCA.SolSub

open GlobalTheory.HCA.SolSub in

theorem GlobalTheory.HCA.solSet_closed_submodule :
    ∀ (d : ℕ) (ι : Type) (P : Sys d ι) (U : Set (E d)), IsOpen U → (∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) →
      IsClosed (solSet P U) ∧ ∃ S : Submodule ℂ (U →ᵇ ℂ), (S : Set (U →ᵇ ℂ)) = solSet P U := by
  intro d ι P U hU ha
  have hint : ∀ (i : ι) (φ : E d → ℂ) (h : ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U),
      Integrable (P.tr i φ) := fun i φ h => integrable_tr P hU ha i h.1 h.2.1 h.2.2
  have key : ∀ u : U →ᵇ ℂ, u ∈ solSet P U ↔
      ∀ (i : ι) (φ : E d → ℂ) (h : ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U),
        pair hU (P.tr i φ) (hint i φ h) u = 0 := by
    intro u
    constructor
    · intro hu i φ h
      exact hu i φ h.1 h.2.1 h.2.2
    · intro hu i φ h1 h2 h3
      exact hu i φ ⟨h1, h2, h3⟩
  refine ⟨?_, ?_⟩
  · have : solSet P U = ⋂ (i : ι) (φ : E d → ℂ) (h : ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U),
        {u | pair hU (P.tr i φ) (hint i φ h) u = 0} := by
      ext u; simp only [Set.mem_iInter, Set.mem_setOf_eq]; exact key u
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun φ => isClosed_iInter fun h =>
      isClosed_eq (pair hU (P.tr i φ) (hint i φ h)).continuous continuous_const
  · refine ⟨{ carrier := solSet P U, add_mem' := ?_, zero_mem' := zero_mem_solSet P U, smul_mem' := ?_ }, rfl⟩
    · intro u v hu hv
      rw [key] at hu hv ⊢
      intro i φ h
      rw [map_add, hu i φ h, hv i φ h, add_zero]
    · intro c u hu
      rw [key] at hu ⊢
      intro i φ h
      rw [map_smul, hu i φ h, smul_zero]
end
end

section
section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory Filter Topology
open scoped ContDiff BoundedContinuousFunction

namespace GlobalTheory.HCA

theorem tendsto_diffQuot_dw {d : ℕ} {U : Set (E d)} (hU : IsOpen U) (f : E d → ℂ)
    (hf : ContDiffOn ℝ ∞ f U) (w : List (Fin d)) (j : Fin d) {x : E d} (hx : x ∈ U) :
    Tendsto (fun n : ℕ => ((n : ℂ) + 1) * (dw w f (x + (1 / ((n : ℝ) + 1)) • ev j) - dw w f x))
      atTop (𝓝 (dw (j :: w) f x)) := by
  have hn := hU.mem_nhds hx
  have hd : DifferentiableAt ℝ (dw w f) x :=
    ((contDiffOn_dw_of_isOpen hU w f hf).contDiffAt hn).differentiableAt (by simp)
  have hline : HasDerivAt (fun t : ℝ => dw w f (x + t • ev j)) (fderiv ℝ (dw w f) x (ev j)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t • ev j) (ev j) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const (ev j)).const_add x
    have h2 : HasFDerivAt (dw w f) (fderiv ℝ (dw w f) x) (x + (0:ℝ) • ev j) := by
      simpa using hd.hasFDerivAt
    exact h2.comp_hasDerivAt (0:ℝ) h1
  have hs := hasDerivAt_iff_tendsto_slope.1 hline
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun n => ?_⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    positivity
  have h3 := hs.comp ht
  show Tendsto _ atTop (𝓝 (fderiv ℝ (dw w f) x (ev j)))
  refine h3.congr (fun n => ?_)
  simp only [Function.comp, slope_def_module, zero_smul, add_zero, sub_zero, Complex.real_smul]
  push_cast
  field_simp

theorem dw_continuousFunctional : ∀ (d : ℕ) (U : Set (E d)), IsOpen U → ∀ (B : Type)
    [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (R : B →ₗ[ℂ] (E d → ℂ)),
    (∀ x ∈ U, Continuous fun u => R u x) → (∀ u, ContDiffOn ℝ ∞ (R u) U) →
    ∀ (w : List (Fin d)), ∀ x ∈ U, ∃ l : B →L[ℂ] ℂ, ∀ u, l u = dw w (R u) x := by
  intro d U hU B _ _ _ R hR hsm w
  induction w with
  | nil =>
    intro x hx
    exact ⟨⟨(LinearMap.proj x : (E d → ℂ) →ₗ[ℂ] ℂ).comp R, hR x hx⟩, fun u => rfl⟩
  | cons j w ih =>
    intro x hx
    choose! L hL using ih
    let y : ℕ → E d := fun n => x + (1 / ((n : ℝ) + 1)) • ev j
    let g : ℕ → B →L[ℂ] ℂ := fun n => ((n : ℂ) + 1) • (L (y n) - L x)
    have hev : ∀ᶠ n in atTop, y n ∈ U := by
      have hy : Tendsto y atTop (𝓝 x) := by
        have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (ev j)
        simpa [y] using h0.const_add x
      exact hy (hU.mem_nhds hx)
    have hlim : Tendsto (fun n u => g n u) atTop (𝓝 (fun u => dw (j :: w) (R u) x)) := by
      rw [tendsto_pi_nhds]
      intro u
      refine (tendsto_diffQuot_dw hU (R u) (hsm u) w j hx).congr' ?_
      filter_upwards [hev] with n hn
      simp only [g, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_eq_mul,
        hL _ hn, hL _ hx, y]
    exact ⟨continuousLinearMapOfTendsto g hlim, fun u => rfl⟩

end GlobalTheory.HCA
end

open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_functional_iterPartialDeriv : ∀ (d : ℕ) (U : Set (E d)), IsOpen U → ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (R : B →ₗ[ℂ] (E d → ℂ)), (∀ x ∈ U, Continuous fun u => R u x) → (∀ u, ContDiffOn ℝ ∞ (R u) U) → ∀ (w : List (Fin d)), ∀ x ∈ U, ∃ l : B →L[ℂ] ℂ, ∀ u, l u = dw w (R u) x := by
  atlas_forward_decl GlobalTheory.HCA.dw_continuousFunctional
end

section
section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction

noncomputable section

namespace GlobalTheory.HCA.SolFunc

variable {d : ℕ}

def extLin {U : Set (E d)} (S : Submodule ℂ (U →ᵇ ℂ)) : S →ₗ[ℂ] (E d → ℂ) where
  toFun u := ext0 U ((u : U →ᵇ ℂ) : U → ℂ)
  map_add' u v := by funext x; exact GlobalTheory.HCA.SolSub.matrixExtendByZero_add (u : U →ᵇ ℂ) v x
  map_smul' c u := by funext x; exact GlobalTheory.HCA.SolSub.extendByZeroOffSubset_smul_apply c (u : U →ᵇ ℂ) x

theorem continuous_extLin_apply {U : Set (E d)} (S : Submodule ℂ (U →ᵇ ℂ)) (x : E d) :
    Continuous fun u : S => extLin S u x := by
  by_cases hx : x ∈ U
  · have : (fun u : S => extLin S u x) = fun u : S => (u : U →ᵇ ℂ) ⟨x, hx⟩ := by
      funext u; simp [extLin, ext0, hx]
    rw [this]
    exact (BoundedContinuousFunction.evalCLM ℂ (⟨x, hx⟩ : U)).continuous.comp continuous_subtype_val
  · have : (fun u : S => extLin S u x) = fun _ => 0 := by
      funext u; simp [extLin, ext0, hx]
    rw [this]; exact continuous_const

theorem continuousOn_extendByZeroOffSubset {U : Set (E d)} (u : U →ᵇ ℂ) : ContinuousOn (ext0 U u) U := by
  rw [continuousOn_iff_continuous_restrict]
  have : U.domRestrict (ext0 U u) = u := by funext x; exact dif_pos x.2
  rw [this]; exact u.continuous

end GlobalTheory.HCA.SolFunc

open GlobalTheory.HCA.SolFunc in

theorem GlobalTheory.HCA.dw_solSet_continuous_functional : ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (U : Set (E d)), IsOpen U → (∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) → (∀ x ∈ U, ∀ ξ : E d, ξ ≠ 0 → ∃ i, P.symb i x ξ ≠ 0) → ∀ S : Submodule ℂ (U →ᵇ ℂ), (S : Set (U →ᵇ ℂ)) = solSet P U → ∀ (w : List (Fin d)), ∀ x ∈ U, ∃ l : S →L[ℂ] ℂ, ∀ u : S, l u = dw w (ext0 U (u : U →ᵇ ℂ)) x := by
  intro d ι _ P U hU ha hell S hS w x hx
  have hcl : IsClosed (S : Set (U →ᵇ ℂ)) := by
    rw [hS]; exact (GlobalTheory.HCA.solSet_closed_submodule d ι P U hU ha).1
  haveI : CompleteSpace S := hcl.completeSpace_coe
  have hsm : ∀ u : S, ContDiffOn ℝ ∞ (extLin S u) U := by
    intro u
    have hu : (u : U →ᵇ ℂ) ∈ solSet P U := by rw [← hS]; exact u.2
    exact ZetaZeros.D.EllReg.elliptic_regularity_of_parts d ι P U _ ⟨hU, ha, hell, continuousOn_extendByZeroOffSubset _, hu⟩
  obtain ⟨l, hl⟩ := GlobalTheory.T.exists_continuous_functional_iterPartialDeriv d U hU S (extLin S) (fun y _ => continuous_extLin_apply S y) hsm w x hx
  exact ⟨l, fun u => hl u⟩
end
end

open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ellipticSystem_derivative_continuous_functional : ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (U : Set (E d)), IsOpen U → (∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) → (∀ x ∈ U, ∀ ξ : E d, ξ ≠ 0 → ∃ i, P.symb i x ξ ≠ 0) → ∀ S : Submodule ℂ (U →ᵇ ℂ), (S : Set (U →ᵇ ℂ)) = solSet P U → ∀ (w : List (Fin d)), ∀ x ∈ U, ∃ l : S →L[ℂ] ℂ, ∀ u : S, l u = dw w (ext0 U (u : U →ᵇ ℂ)) x := by
  atlas_forward_decl GlobalTheory.HCA.dw_solSet_continuous_functional
end

section
section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction

noncomputable section

namespace GlobalTheory.HCA.SupEst

variable {d : ℕ}

theorem dw_zero_fun : ∀ w : List (Fin d), dw w (fun _ : E d => (0 : ℂ)) = fun _ => 0
  | [] => rfl
  | j :: w => by
      funext x
      show fderiv ℝ (dw w (fun _ : E d => (0 : ℂ))) x (ev j) = 0
      rw [dw_zero_fun w]
      simp

theorem tr_eq_zero_of_notMem {ι : Type} (P : Sys d ι) (i : ι) {φ : E d → ℂ} {x : E d}
    (hx : x ∉ tsupport φ) : P.tr i φ x = 0 := by
  unfold Sys.tr trOp
  refine Finset.sum_eq_zero fun n _ => Finset.sum_eq_zero fun w _ => ?_
  have hO : IsOpen (tsupport φ)ᶜ := (isClosed_tsupport φ).isOpen_compl
  have hEq : Set.EqOn (fun y => P.a i n w y * φ y) (fun _ => (0 : ℂ)) (tsupport φ)ᶜ := by
    intro y hy
    have : φ y = 0 := image_eq_zero_of_notMem_tsupport hy
    simp [this]
  have := eqOn_dw_of_isOpen hO (List.ofFn w) _ _ hEq hx
  rw [this, dw_zero_fun]
  simp

end GlobalTheory.HCA.SupEst

open GlobalTheory.HCA.SupEst in

theorem GlobalTheory.HCA.dw_le_sup : ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (U : Set (E d)), IsOpen U → (∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) → (∀ x ∈ U, ∀ ξ : E d, ξ ≠ 0 → ∃ i, P.symb i x ξ ≠ 0) → ∀ (w : List (Fin d)), ∀ x₀ ∈ U, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : E d → ℂ, ContinuousOn u U → WeakSol P U u → ∀ M : ℝ, (∀ x ∈ U, ‖u x‖ ≤ M) → ‖dw w u x₀‖ ≤ C * M := by
  intro d ι _ P U hU ha hell w x₀ hx₀
  obtain ⟨S, hS⟩ := (solSet_closed_submodule d ι P U hU ha).2
  obtain ⟨l, hl⟩ := GlobalTheory.T.ellipticSystem_derivative_continuous_functional d ι P U hU ha hell S hS w x₀ hx₀
  refine ⟨‖l‖, norm_nonneg _, ?_⟩
  intro u hu hweak M hM
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x₀ hx₀)
  have hcont : Continuous (U.restrict u) := continuousOn_iff_continuous_restrict.mp hu
  let u' : U →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup (U.restrict u) hcont M
    (fun x => hM x.1 x.2)
  have hu'n : ‖u'‖ ≤ M := BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hM0 _
  have hext : Set.EqOn (ext0 U u') u U := by
    intro x hx
    simp only [ext0, hx, dif_pos, u']
    rfl
  have hmem : u' ∈ solSet P U := by
    intro i φ h1 h2 h3
    rw [← hweak i φ h1 h2 h3]
    congr 1
    funext x
    by_cases hx : x ∈ U
    · rw [hext hx]
    · have : x ∉ tsupport φ := fun h => hx (h3 h)
      rw [tr_eq_zero_of_notMem P i this]
      simp
  have hmemS : u' ∈ S := by rw [← SetLike.mem_coe, hS]; exact hmem
  have hval : l ⟨u', hmemS⟩ = dw w u x₀ := by
    rw [hl]
    exact eqOn_dw_of_isOpen hU w _ _ hext hx₀
  rw [← hval]
  calc ‖l ⟨u', hmemS⟩‖ ≤ ‖l‖ * ‖(⟨u', hmemS⟩ : S)‖ := l.le_opNorm _
    _ = ‖l‖ * ‖u'‖ := rfl
    _ ≤ ‖l‖ * M := mul_le_mul_of_nonneg_left hu'n (norm_nonneg _)

end
end

open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.elliptic_weakSol_wordDeriv_le_const_mul_sup : ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (U : Set (E d)), IsOpen U → (∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) → (∀ x ∈ U, ∀ ξ : E d, ξ ≠ 0 → ∃ i, P.symb i x ξ ≠ 0) → ∀ (w : List (Fin d)), ∀ x₀ ∈ U, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : E d → ℂ, ContinuousOn u U → WeakSol P U u → ∀ M : ℝ, (∀ x ∈ U, ‖u x‖ ≤ M) → ‖dw w u x₀‖ ≤ C * M := by
  atlas_forward_decl GlobalTheory.HCA.dw_le_sup
end

section
section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

theorem apOp_sum_coef {d : ℕ} {ι : Type} (s : Finset ι) (m : ℕ) (a : ι → (n : ℕ) → (Fin n → Fin d) → E d → ℂ)
    (u : E d → ℂ) (x : E d) :
    apOp m (fun n w y => ∑ i ∈ s, a i n w y) u x = ∑ i ∈ s, apOp m (a i) u x := by
  simp only [apOp, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_comm]

theorem symb_sum_coef {d : ℕ} {ι : Type} (s : Finset ι) (m : ℕ) (a : ι → (n : ℕ) → (Fin n → Fin d) → E d → ℂ)
    (x ξ : E d) :
    symb m (fun n w y => ∑ i ∈ s, a i n w y) x ξ = ∑ i ∈ s, symb m (a i) x ξ := by
  simp only [symb, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem exists_apOp_sumSq_pow : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (r : ℝ) (c : 𝔤 → Fin d → E d → ℝ), ((∀ X j, ContDiffOn ℝ ∞ (c X j) (Metric.ball 0 r)) ∧ (∀ x ∈ Metric.ball (0 : E d) r, ∀ ξ : E d, ξ ≠ 0 → ∃ i, ∑ j, c (b i) j x * ξ j ≠ 0) ∧ ∀ f : G → ℂ, h.IsSmoothFun f → ∀ X : 𝔤, ∀ x ∈ Metric.ball (0 : E d) r, h.rightDeriv X f (h.expG (coordEquiv b (x))) = ∑ j, (c X j x : ℂ) * fderiv ℝ (fun y => f (h.expG (coordEquiv b (y)))) x (ev j)) → ∀ k : ℕ, ∃ a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a n w) (Metric.ball 0 r)) ∧ (∀ x ξ : E d, symb (2 * k) a x ξ = (((∑ i, (∑ j, c (b i) j x * ξ j) ^ 2) ^ k : ℝ) : ℂ)) ∧ ∀ f : h.smoothFuns (F := ℂ), ∀ x ∈ Metric.ball (0 : E d) r, (((∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) ^ k) f : G → ℂ) (h.expG (coordEquiv b (x))) = apOp (2 * k) a (fun y => (f : G → ℂ) (h.expG (coordEquiv b (y)))) x := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b r c ⟨hc, _, hder⟩ k
  set U : Set (E d) := Metric.ball 0 r with hUdef
  have hU : IsOpen U := Metric.isOpen_ball
  have hchart : ∀ f : G → ℂ, h.IsSmoothFun f →
      ContDiff ℝ ∞ (fun y : E d => f (h.expG (coordEquiv b y))) := by
    intro f hf
    simpa using h.contDiff_comp_coordEquiv hf 1 b
  have step : ∀ (X : 𝔤) (f : G → ℂ), h.IsSmoothFun f → ∀ v : E d → ℂ,
      (∀ y ∈ U, f (h.expG (coordEquiv b y)) = v y) → ∀ x ∈ U,
      h.rightDeriv X f (h.expG (coordEquiv b x)) = ∑ j, (c X j x : ℂ) * fderiv ℝ v x (ev j) := by
    intro X f hf v hv x hx
    rw [hder f hf X x hx]
    have e : (fun y : E d => f (h.expG (coordEquiv b y))) =ᶠ[nhds x] v :=
      Filter.eventually_of_mem (hU.mem_nhds hx) hv
    rw [e.fderiv_eq]
  have hcC : ∀ i j, ContDiffOn ℝ ∞ (fun y => ((c (b i) j y : ℝ) : ℂ)) U := fun i j =>
    Complex.ofRealCLM.contDiff.comp_contDiffOn (hc (b i) j)
  induction k with
  | zero =>
    refine ⟨fun _ _ _ => 1, fun _ _ => contDiffOn_const, ?_, ?_⟩
    · intro x ξ; simp [symb]
    · intro f x _
      simp [apOp_zero_one]
  | succ k ih =>
    obtain ⟨a, ha, hsa, hap⟩ := ih
    choose a1 ha1 hs1 hap1 using fun i : Fin d =>
      GlobalTheory.VFComp.vectorField_comp d (2 * k) U hU a (fun j y => ((c (b i) j y : ℝ) : ℂ)) ha (hcC i)
    choose a2 ha2 hs2 hap2 using fun i : Fin d =>
      GlobalTheory.VFComp.vectorField_comp d (2 * k + 1) U hU (a1 i) (fun j y => ((c (b i) j y : ℝ) : ℂ)) (ha1 i) (hcC i)
    have e2 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    refine ⟨fun n w y => ∑ i, a2 i n w y, fun n w => ContDiffOn.sum fun i _ => ha2 i n w, ?_, ?_⟩
    · intro x ξ
      rw [symb_sum_coef, e2]
      simp only [hs2, hs1, hsa]
      push_cast
      rw [pow_succ', Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    · intro f x hx
      rw [apOp_sum_coef, e2, pow_succ', Module.End.mul_apply]
      set g := ((∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) ^ k) f with hg
      simp only [LinearMap.sum_apply, Finset.sum_apply, Submodule.coe_sum, Module.End.mul_apply,
        IsExpLieAlgebra.coe_rightDerivEnd]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hf0 := hchart _ f.2
      have h1 : ∀ y ∈ U, h.rightDeriv (b i) (g : G → ℂ) (h.expG (coordEquiv b y)) =
          apOp (2 * k + 1) (a1 i) (fun y => (f : G → ℂ) (h.expG (coordEquiv b y))) y := by
        intro y hy
        rw [step (b i) _ g.2 _ (fun z hz => hap f z hz) y hy]
        exact hap1 i _ hf0.contDiffOn y hy
      rw [step (b i) _ (h.isSmoothFun_rightDeriv g.2 (b i)) _ h1 x hx]
      exact hap2 i _ hf0.contDiffOn x hx

end GlobalTheory.HCA
end

open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sumSquaresRightDeriv_pow_differentialOperator : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (r : ℝ) (c : 𝔤 → Fin d → E d → ℝ), ((∀ X j, ContDiffOn ℝ ∞ (c X j) (Metric.ball 0 r)) ∧ (∀ x ∈ Metric.ball (0 : E d) r, ∀ ξ : E d, ξ ≠ 0 → ∃ i, ∑ j, c (b i) j x * ξ j ≠ 0) ∧ ∀ f : G → ℂ, h.IsSmoothFun f → ∀ X : 𝔤, ∀ x ∈ Metric.ball (0 : E d) r, h.rightDeriv X f (h.expG (coordEquiv b (x))) = ∑ j, (c X j x : ℂ) * fderiv ℝ (fun y => f (h.expG (coordEquiv b (y)))) x (ev j)) → ∀ k : ℕ, ∃ a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a n w) (Metric.ball 0 r)) ∧ (∀ x ξ : E d, symb (2 * k) a x ξ = (((∑ i, (∑ j, c (b i) j x * ξ j) ^ 2) ^ k : ℝ) : ℂ)) ∧ ∀ f : h.smoothFuns (F := ℂ), ∀ x ∈ Metric.ball (0 : E d) r, (((∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) ^ k) f : G → ℂ) (h.expG (coordEquiv b (x))) = apOp (2 * k) a (fun y => (f : G → ℂ) (h.expG (coordEquiv b (y)))) x := by
  atlas_forward_decl GlobalTheory.HCA.exists_apOp_sumSq_pow
end

section
section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

theorem isSmoothFun_leftTranslate (h : IsExpLieAlgebra G 𝔤) {f : G → ℂ}
    (hf : h.IsSmoothFun f) (g : G) : h.IsSmoothFun (fun y => f (g * y)) := by
  rw [IsExpLieAlgebra.isSmoothFun_iff] at hf ⊢
  intro g'
  simpa only [mul_assoc] using hf (g * g')

def leftTranslateSmoothEnd (h : IsExpLieAlgebra G 𝔤) (g : G) :
    Module.End ℂ (h.smoothFuns (F := ℂ)) where
  toFun f := ⟨fun y => (f : G → ℂ) (g * y), isSmoothFun_leftTranslate h f.2 g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coe_leftTranslateSmoothEnd (h : IsExpLieAlgebra G 𝔤) (g : G)
    (f : h.smoothFuns (F := ℂ)) (y : G) :
    ((leftTranslateSmoothEnd h g f : h.smoothFuns (F := ℂ)) : G → ℂ) y = (f : G → ℂ) (g * y) :=
  rfl

theorem commute_rightDerivEnd_leftTranslate (h : IsExpLieAlgebra G 𝔤) (g : G) (X : 𝔤) :
    Commute (h.rightDerivEnd (F := ℂ) X) (leftTranslateSmoothEnd h g) := by
  ext f y
  simp only [Module.End.mul_apply, IsExpLieAlgebra.coe_rightDerivEnd,
    coe_leftTranslateSmoothEnd, IsExpLieAlgebra.rightDeriv]
  simp only [mul_assoc]

theorem leftTranslate_smooth_commute (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸)
    (h : IsExpLieAlgebra G 𝔤) (f : h.smoothFuns (F := ℂ)) (g : G) :
    ∃ f' : h.smoothFuns (F := ℂ), (∀ y, (f' : G → ℂ) y = (f : G → ℂ) (g * y)) ∧
      ∀ T ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))), ∀ y,
        (T f' : G → ℂ) y = (T f : G → ℂ) (g * y) := by
  refine ⟨leftTranslateSmoothEnd h g f, fun y => rfl, fun T hT y => ?_⟩
  have hc : Commute T (leftTranslateSmoothEnd h g) := by
    refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hT ?_).symm
    rintro _ ⟨X, rfl⟩
    exact (commute_rightDerivEnd_leftTranslate h g X).symm
  have := congrArg (fun S : Module.End ℂ (h.smoothFuns (F := ℂ)) => ((S f : h.smoothFuns (F := ℂ)) : G → ℂ) y) hc.eq
  simpa only [Module.End.mul_apply, coe_leftTranslateSmoothEnd] using this

end GlobalTheory
end

open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leftTranslate_smooth_commute_leftInvariantOps : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (f : h.smoothFuns (F := ℂ)) (g : G), ∃ f' : h.smoothFuns (F := ℂ), (∀ y, (f' : G → ℂ) y = (f : G → ℂ) (g * y)) ∧ ∀ T ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))), ∀ y, (T f' : G → ℂ) y = (T f : G → ℂ) (g * y) := by
  atlas_forward_decl GlobalTheory.leftTranslate_smooth_commute
end

section
section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction

namespace GlobalTheory.HCA

theorem exists_apOp_add_smul : ∀ (d m m' : ℕ) (U : Set (E d)) (a a' : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (t : ℂ), m' ≤ m → (∀ n w, ContDiffOn ℝ ∞ (a n w) U) → (∀ n w, ContDiffOn ℝ ∞ (a' n w) U) → ∃ a'' : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a'' n w) U) ∧ (∀ x ξ : E d, symb m a'' x ξ = symb m a x ξ + if m' = m then t * symb m' a' x ξ else 0) ∧ ∀ (u : E d → ℂ) (x : E d), apOp m a'' u x = apOp m a u x + t * apOp m' a' u x := by
  intro d m m' U a a' t hm ha ha'
  refine ⟨fun n w x => a n w x + if n ≤ m' then t * a' n w x else 0, ?_, ?_, ?_⟩
  · intro n w
    by_cases h : n ≤ m'
    · simp only [h, if_true]
      exact (ha n w).add (contDiffOn_const.mul (ha' n w))
    · simp only [h, if_false, add_zero]
      exact ha n w
  · intro x ξ
    by_cases h : m' = m
    · subst h
      simp only [symb, le_refl, if_true, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    · have h' : ¬ m ≤ m' := fun h2 => h (le_antisymm hm h2)
      simp only [symb, h, h', if_false, add_zero]
  · intro u x
    simp only [apOp, add_mul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    symm
    have hs : Finset.range (m' + 1) ⊆ Finset.range (m + 1) := by
      intro n hn
      simp only [Finset.mem_range] at hn ⊢
      omega
    rw [← Finset.sum_subset hs]
    · refine Finset.sum_congr rfl fun n hn => ?_
      have h : n ≤ m' := by simp only [Finset.mem_range] at hn; omega
      simp only [h, if_true, Finset.mul_sum, mul_assoc]
    · intro n _ hn
      have h : ¬ n ≤ m' := by simp only [Finset.mem_range] at hn; omega
      simp [h]

end GlobalTheory.HCA
end

open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_apOp_add_smul' : ∀ (d m m' : ℕ) (U : Set (E d)) (a a' : (n : ℕ) → (Fin n → Fin d) → E d → ℂ) (t : ℂ), m' ≤ m → (∀ n w, ContDiffOn ℝ ∞ (a n w) U) → (∀ n w, ContDiffOn ℝ ∞ (a' n w) U) → ∃ a'' : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a'' n w) U) ∧ (∀ x ξ : E d, symb m a'' x ξ = symb m a x ξ + if m' = m then t * symb m' a' x ξ else 0) ∧ ∀ (u : E d → ℂ) (x : E d), apOp m a'' u x = apOp m a u x + t * apOp m' a' u x := by
  atlas_forward_decl GlobalTheory.HCA.exists_apOp_add_smul
end

section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dw_contDiffOn_local_linear : ∀ (d : ℕ) (U : Set (E d)), IsOpen U → ∀ (w : List (Fin d)), (∀ u : E d → ℂ, ContDiffOn ℝ ∞ u U → ContDiffOn ℝ ∞ (dw w u) U) ∧ (∀ u v : E d → ℂ, Set.EqOn u v U → Set.EqOn (dw w u) (dw w v) U) ∧ (∀ u v : E d → ℂ, ContDiffOn ℝ ∞ u U → ContDiffOn ℝ ∞ v U → ∀ s t : ℂ, Set.EqOn (dw w (s • u + t • v)) (s • dw w u + t • dw w v) U) := by
  first | exact @GlobalTheory.HCA.dw_smooth_local_linear | exact GlobalTheory.HCA.dw_smooth_local_linear | (intros; apply GlobalTheory.HCA.dw_smooth_local_linear <;> assumption)
end

section
section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction

namespace GlobalTheory.HCA

theorem integrable_mul_of_tsupport_subset {d : ℕ} {U : Set (E d)} (hU : IsOpen U)
    {f g : E d → ℂ} (hf : ContinuousOn f U) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hs : tsupport g ⊆ U) : Integrable (fun x => f x * g x) := by
  have hc : Continuous (fun x => f x * g x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ U
    · exact (hf.continuousAt (hU.mem_nhds hx)).mul hg.continuousAt
    · have hx' : x ∉ tsupport g := fun h => hx (hs h)
      have h0 : (fun x => f x * g x) =ᶠ[nhds x] fun _ => (0 : ℂ) := by
        filter_upwards [(notMem_tsupport_iff_eventuallyEq).1 hx'] with y hy
        simp [hy]
      exact (continuousAt_congr h0).2 continuousAt_const
  exact hc.integrable_of_hasCompactSupport hgc.mul_left

theorem integral_mul_partial_eq_neg {d : ℕ} {U : Set (E d)} (hU : IsOpen U) (j : Fin d)
    {u ψ : E d → ℂ} (hu : ContDiffOn ℝ ∞ u U) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ U) :
    ∫ x, u x * fderiv ℝ ψ x (ev j) = - ∫ x, fderiv ℝ u x (ev j) * ψ x := by
  have hu1 : ContDiffOn ℝ ∞ (fun x => fderiv ℝ u x (ev j)) U :=
    contDiffOn_dw_of_isOpen hU [j] u hu
  have hψ1 : Continuous (fun x => fderiv ℝ ψ x (ev j)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsub : tsupport (fun x => fderiv ℝ ψ x (ev j)) ⊆ tsupport ψ := by
    refine (closure_mono ?_).trans (tsupport_fderiv_subset (𝕜 := ℝ) (f := ψ))
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h; exact hx (by simp [h])
  have hψ1c : HasCompactSupport (fun x => fderiv ℝ ψ x (ev j)) :=
    (hψc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : E d →L[ℝ] ℂ => L (ev j)) (by simp)
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact integrable_mul_of_tsupport_subset hU hu1.continuousOn hψ.continuous hψc hψs
  · exact integrable_mul_of_tsupport_subset hU hu.continuousOn hψ1 hψ1c (hsub.trans hψs)
  · exact integrable_mul_of_tsupport_subset hU hu.continuousOn hψ.continuous hψc hψs
  · intro x hx
    exact (hu.contDiffAt (hU.mem_nhds (hψs hx))).differentiableAt (by simp)
  · intro x _
    exact hψ.differentiable (by simp) x

theorem dw_contDiff_tsupport {d : ℕ} (w : List (Fin d)) {φ : E d → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (dw w φ) ∧ tsupport (dw w φ) ⊆ tsupport φ := by
  induction w with
  | nil => exact ⟨hφ, subset_rfl⟩
  | cons j w ih =>
    refine ⟨(ih.1.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const, ?_⟩
    refine (closure_mono ?_).trans ((tsupport_fderiv_subset (𝕜 := ℝ) (f := dw w φ)).trans ih.2)
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro h; apply hx; show fderiv ℝ (dw w φ) x (ev j) = 0; simp [h]

theorem dw_append {d : ℕ} (w v : List (Fin d)) (f : E d → ℂ) : dw (w ++ v) f = dw w (dw v f) := by
  induction w with
  | nil => rfl
  | cons j w ih => funext x; show fderiv ℝ (dw (w ++ v) f) x (ev j) = _; rw [ih]; rfl

theorem dw_swap {d : ℕ} {U : Set (E d)} (hU : IsOpen U) (a b : Fin d) {g : E d → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) : Set.EqOn (dw [a, b] g) (dw [b, a] g) U := by
  intro x hx
  have hx' := hU.mem_nhds hx
  have hga : ContDiffAt ℝ ∞ g x := hg.contDiffAt hx'
  have hsym := hga.isSymmSndFDerivAt (by simpa using (WithTop.coe_le_coe.2 le_top : (2 : WithTop ℕ∞) ≤ ∞))
  have hd1 : ∀ᶠ y in nhds x, DifferentiableAt ℝ g y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (hg.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  have hdf : DifferentiableAt ℝ (fderiv ℝ g) x := by
    have := (contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hg
    exact (this.2.contDiffAt hx').differentiableAt (by simp)
  show fderiv ℝ (fun y => fderiv ℝ g y (ev b)) x (ev a) = fderiv ℝ (fun y => fderiv ℝ g y (ev a)) x (ev b)
  rw [fderiv_clm_apply hdf (differentiableAt_const _), fderiv_clm_apply hdf (differentiableAt_const _)]
  have h0 : ∀ c : E d, fderiv ℝ (fun _ : E d => c) x = 0 := fun c => fderiv_const_apply c
  simp only [h0, ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  exact hsym _ _

end GlobalTheory.HCA

namespace GlobalTheory.HCA

theorem dw_perm {d : ℕ} {U : Set (E d)} (hU : IsOpen U) {w₁ w₂ : List (Fin d)} (h : w₁.Perm w₂) :
    ∀ u : E d → ℂ, ContDiffOn ℝ ∞ u U → Set.EqOn (dw w₁ u) (dw w₂ u) U := by
  induction h with
  | nil => intro u _; exact fun _ _ => rfl
  | cons j _ ih =>
    intro u hu z hz
    show fderiv ℝ _ z (ev j) = fderiv ℝ _ z (ev j)
    rw [((ih u hu).eventuallyEq_of_mem (hU.mem_nhds hz)).fderiv_eq]
  | swap x y l =>
    intro u hu
    have e1 := dw_append [y, x] l u
    have e2 := dw_append [x, y] l u
    simp only [List.cons_append, List.nil_append] at e1 e2
    rw [e1, e2]
    exact dw_swap hU y x (contDiffOn_dw_of_isOpen hU l u hu)
  | trans _ _ ih₁ ih₂ => intro u hu; exact (ih₁ u hu).trans (ih₂ u hu)

theorem integral_mul_dw_eq_reverse {d : ℕ} {U : Set (E d)} (hU : IsOpen U) (w : List (Fin d)) :
    ∀ (u φ : E d → ℂ), ContDiffOn ℝ ∞ u U → ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
      ∫ x, u x * dw w φ x = (-1 : ℂ) ^ w.length * ∫ x, dw w.reverse u x * φ x := by
  induction w with
  | nil => intro u φ _ _ _ _; simp [dw]
  | cons j w ih =>
    intro u φ hu hφ hφc hφs
    obtain ⟨hψ, hψs⟩ := dw_contDiff_tsupport w hφ
    have hψc : HasCompactSupport (dw w φ) := IsCompact.of_isClosed_subset hφc (isClosed_tsupport _) hψs
    have step := integral_mul_partial_eq_neg hU j hu hψ hψc (hψs.trans hφs)
    have hu1 : ContDiffOn ℝ ∞ (dw [j] u) U := contDiffOn_dw_of_isOpen hU [j] u hu
    have ih' := ih (dw [j] u) φ hu1 hφ hφc hφs
    have e : dw w.reverse (dw [j] u) = dw (j :: w).reverse u := by
      rw [List.reverse_cons, dw_append]
    show ∫ x, u x * fderiv ℝ (dw w φ) x (ev j) = _
    rw [step]
    change -∫ x, dw [j] u x * dw w φ x = _
    rw [ih', e, List.length_cons, pow_succ]
    ring

theorem integral_mul_dw_eq_neg_pow : ∀ (d : ℕ) (U : Set (E d)), IsOpen U → ∀ (w : List (Fin d))
    (u φ : E d → ℂ), ContDiffOn ℝ ∞ u U → ContDiff ℝ ∞ φ → HasCompactSupport φ →
    tsupport φ ⊆ U → ∫ x, u x * dw w φ x = (-1 : ℂ) ^ w.length * ∫ x, dw w u x * φ x := by
  intro d U hU w u φ hu hφ hφc hφs
  rw [integral_mul_dw_eq_reverse hU w u φ hu hφ hφc hφs]
  congr 2
  funext x
  by_cases hx : x ∈ U
  · rw [dw_perm hU (List.reverse_perm w) u hu hx]
  · have : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hφs h))
    simp [this]

end GlobalTheory.HCA
end

open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_mul_iterPartialDeriv_eq_neg_pow : ∀ (d : ℕ) (U : Set (E d)), IsOpen U → ∀ (w : List (Fin d)) (u φ : E d → ℂ), ContDiffOn ℝ ∞ u U → ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∫ x, u x * dw w φ x = (-1 : ℂ) ^ w.length * ∫ x, dw w u x * φ x := by
  atlas_forward_decl GlobalTheory.HCA.integral_mul_dw_eq_neg_pow
end

section
section
noncomputable section

open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction Topology

namespace GlobalTheory.HCA

theorem integrable_mul_of_continuousOn_of_tsupport {d : ℕ} {U : Set (E d)} (hU : IsOpen U)
    {f g : E d → ℂ} (hf : ContinuousOn f U) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ U) : Integrable (fun x => f x * g x) := by
  have hcont : Continuous (fun x => f x * g x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ U
    · exact (hf.continuousAt (hU.mem_nhds hx)).mul hg.continuousAt
    · have hx' : x ∉ tsupport g := fun h => hx (hgU h)
      have h0 : (fun x => f x * g x) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
        simp [hy]
      exact continuousAt_const.congr h0.symm
  exact hcont.integrable_of_hasCompactSupport (hgc.mul_left)

theorem dw_hasCompactSupport_tsupport {d : ℕ} (w : List (Fin d)) {f : E d → ℂ}
    (hf : HasCompactSupport f) : HasCompactSupport (dw w f) ∧ tsupport (dw w f) ⊆ tsupport f := by
  induction w with
  | nil => exact ⟨hf, subset_rfl⟩
  | cons j w ih =>
    refine ⟨ih.1.fderiv_apply (𝕜 := ℝ) (ev j), ?_⟩
    exact (tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := dw w f) (ev j)).trans ih.2

theorem contDiff_mul_of_contDiffOn_of_tsupport {d : ℕ} {U : Set (E d)} (hU : IsOpen U)
    {b φ : E d → ℂ} (hb : ContDiffOn ℝ ∞ b U) (hφ : ContDiff ℝ ∞ φ) (hs : tsupport φ ⊆ U) :
    ContDiff ℝ ∞ (fun y => b y * φ y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (hb.contDiffAt (hU.mem_nhds hx)).mul hφ.contDiffAt
  · have hx' : x ∉ tsupport φ := fun h => hx (hs h)
    have h0 : (fun y => b y * φ y) =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq h0

theorem weakSol_of_smooth :
    ∀ (d m : ℕ) (U : Set (E d)), IsOpen U → ∀ (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ),
      (∀ n w, ContDiffOn ℝ ∞ (a n w) U) → ∀ u : E d → ℂ, ContDiffOn ℝ ∞ u U →
      (∀ x ∈ U, apOp m a u x = 0) → WeakSol (oneSys m a) U u := by
  intro d m U hU a ha u hu hap i φ hφ hc hs
  show ∫ x, u x * trOp m a φ x = 0
  have hψ : ∀ n w, ContDiff ℝ ∞ (fun y => a n w y * φ y) := fun n w =>
    contDiff_mul_of_contDiffOn_of_tsupport hU (ha n w) hφ hs
  have hψc : ∀ n w, HasCompactSupport (fun y => a n w y * φ y) := fun n w => hc.mul_left
  have hψs : ∀ n w, tsupport (fun y => a n w y * φ y) ⊆ U := fun n w =>
    (tsupport_mul_subset_right).trans hs
  have hI1 : ∀ n (w : Fin n → Fin d),
      Integrable (fun x => u x * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => a n w y * φ y) x)) := by
    intro n w
    have hdc := dw_hasCompactSupport_tsupport (List.ofFn w) (hψc n w)
    have hcont : Continuous (dw (List.ofFn w) (fun y => a n w y * φ y)) := by
      have := (GlobalTheory.T.dw_contDiffOn_local_linear d Set.univ isOpen_univ (List.ofFn w)).1 _ (hψ n w).contDiffOn
      exact (contDiffOn_univ.1 this).continuous
    have := integrable_mul_of_continuousOn_of_tsupport hU hu.continuousOn
      (g := fun x => (-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => a n w y * φ y) x)
      (continuous_const.mul hcont) (hdc.1.mul_left)
      ((tsupport_mul_subset_right).trans (hdc.2.trans (hψs n w)))
    exact this
  have hI2 : ∀ n (w : Fin n → Fin d),
      Integrable (fun x => dw (List.ofFn w) u x * (a n w x * φ x)) := by
    intro n w
    exact integrable_mul_of_continuousOn_of_tsupport hU
      ((GlobalTheory.T.dw_contDiffOn_local_linear d U hU (List.ofFn w)).1 u hu).continuousOn (hψ n w).continuous (hψc n w) (hψs n w)
  have hterm : ∀ n (w : Fin n → Fin d),
      ∫ x, u x * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => a n w y * φ y) x) =
        ∫ x, dw (List.ofFn w) u x * (a n w x * φ x) := by
    intro n w
    have hibp := GlobalTheory.T.integral_mul_iterPartialDeriv_eq_neg_pow d U hU (List.ofFn w) u (fun y => a n w y * φ y) hu (hψ n w) (hψc n w)
      (hψs n w)
    rw [List.length_ofFn] at hibp
    have e1 : (fun x => u x * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => a n w y * φ y) x)) =
        fun x => (-1 : ℂ) ^ n * (u x * dw (List.ofFn w) (fun y => a n w y * φ y) x) := by
      funext x; ring
    rw [e1, integral_const_mul, hibp, ← mul_assoc, ← mul_pow]
    norm_num
  have hsplit : (fun x => u x * trOp m a φ x) = fun x => ∑ n ∈ Finset.range (m + 1),
      ∑ w : Fin n → Fin d, u x * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => a n w y * φ y) x) := by
    funext x
    simp only [trOp, Finset.mul_sum]
  rw [hsplit, integral_finset_sum _ (fun n _ => integrable_finset_sum _ (fun w _ => hI1 n w))]
  have hin : ∀ n ∈ Finset.range (m + 1),
      ∫ x, ∑ w : Fin n → Fin d, u x * ((-1 : ℂ) ^ n * dw (List.ofFn w) (fun y => a n w y * φ y) x) =
        ∫ x, ∑ w : Fin n → Fin d, dw (List.ofFn w) u x * (a n w x * φ x) := by
    intro n _
    rw [integral_finset_sum _ (fun w _ => hI1 n w), integral_finset_sum _ (fun w _ => hI2 n w)]
    exact Finset.sum_congr rfl fun w _ => hterm n w
  rw [Finset.sum_congr rfl hin,
    ← integral_finset_sum _ (fun n _ => integrable_finset_sum _ (fun w _ => hI2 n w))]
  have hzero : (fun x => ∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
      dw (List.ofFn w) u x * (a n w x * φ x)) = fun _ => (0 : ℂ) := by
    funext x
    by_cases hx : x ∈ U
    · have h := hap x hx
      have e : (∑ n ∈ Finset.range (m + 1), ∑ w : Fin n → Fin d,
          dw (List.ofFn w) u x * (a n w x * φ x)) = apOp m a u x * φ x := by
        simp only [apOp, Finset.sum_mul]
        refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun w _ => ?_
        ring
      rw [e, h, zero_mul]
    · have h0 : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hs h)
      simp [h0]
  rw [hzero, integral_zero]

end GlobalTheory.HCA

end
end

open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weakSolution_of_smooth_solution : ∀ (d m : ℕ) (U : Set (E d)), IsOpen U → ∀ (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ), (∀ n w, ContDiffOn ℝ ∞ (a n w) U) → ∀ u : E d → ℂ, ContDiffOn ℝ ∞ u U → (∀ x ∈ U, apOp m a u x = 0) → WeakSol (oneSys m a) U u := by
  atlas_forward_decl GlobalTheory.HCA.weakSol_of_smooth
end

section
section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

theorem exists_apOp_add_lower_sum {d : ℕ} (U : Set (E d)) (k : ℕ)
    (A : ℕ → (n : ℕ) → (Fin n → Fin d) → E d → ℂ)
    (hA : ∀ i n w, ContDiffOn ℝ ∞ (A i n w) U) (t : ℕ → ℂ) :
    ∀ N ≤ k, ∃ a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a n w) U) ∧
      (∀ x ξ : E d, symb (2 * k) a x ξ = symb (2 * k) (A k) x ξ) ∧
      ∀ (u : E d → ℂ) (x : E d), apOp (2 * k) a u x =
        apOp (2 * k) (A k) u x + ∑ i ∈ Finset.range N, t i * apOp (2 * i) (A i) u x := by
  intro N
  induction N with
  | zero => intro _; exact ⟨A k, hA k, fun _ _ => rfl, fun u x => by simp⟩
  | succ N ih =>
    intro hN
    obtain ⟨a, ha, hs, hop⟩ := ih (by omega)
    obtain ⟨a'', h1, h2, h3⟩ :=
      GlobalTheory.T.exists_apOp_add_smul' d (2 * k) (2 * N) U a (A N) (t N) (by omega) ha (hA N)
    refine ⟨a'', h1, fun x ξ => ?_, fun u x => ?_⟩
    · rw [h2, if_neg (by omega), add_zero, hs]
    · rw [h3, hop, Finset.sum_range_succ]; ring

theorem exists_elliptic_weakSol_of_aeval_eq_zero : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∃ r > 0, ∃ (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ), (∀ n w, ContDiffOn ℝ ∞ (a n w) (Metric.ball 0 r)) ∧ (∀ x ∈ Metric.ball (0 : E d) r, ∀ ξ : E d, ξ ≠ 0 → symb m a x ξ ≠ 0) ∧ ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P f = 0 → ∀ g : G, WeakSol (oneSys m a) (Metric.ball 0 r) (fun y => (f : G → ℂ) (g * h.expG (coordEquiv b (y)))) := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b P hP
  obtain ⟨r, hr, c, hc, hspan, hder⟩ := GlobalTheory.T.leftInvariantVectorFields_expCoords_smooth_frame 𝔸 G 𝔤 h d b
  choose A hAs hAsymb hAop using GlobalTheory.T.exists_sumSquaresRightDeriv_pow_differentialOperator 𝔸 G 𝔤 h d b r c ⟨hc, hspan, hder⟩
  obtain ⟨a, ha, hsa, hopa⟩ := exists_apOp_add_lower_sum (Metric.ball (0 : E d) r) P.natDegree A
    (fun i => hAs i) (fun i => P.coeff i) P.natDegree le_rfl
  refine ⟨r, hr, 2 * P.natDegree, a, ha, ?_, ?_⟩
  · intro x hx ξ hξ
    rw [hsa, hAsymb]
    obtain ⟨i, hi⟩ := hspan x hx ξ hξ
    have hpos : 0 < ∑ i, (∑ j, c (b i) j x * ξ j) ^ 2 :=
      lt_of_lt_of_le (by positivity : 0 < (∑ j, c (b i) j x * ξ j) ^ 2)
        (Finset.single_le_sum (f := fun i => (∑ j, c (b i) j x * ξ j) ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ i))
    exact_mod_cast (pow_pos hpos P.natDegree).ne'
  · intro f hf g
    obtain ⟨f', hf'1, hf'2⟩ := GlobalTheory.T.leftTranslate_smooth_commute_leftInvariantOps 𝔸 G 𝔤 h f g
    set Δ := ∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i) with hΔdef
    have hΔ : Δ ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) :=
      Subalgebra.sum_mem _ (fun i _ => Subalgebra.mul_mem _
        (Algebra.subset_adjoin ⟨b i, rfl⟩) (Algebra.subset_adjoin ⟨b i, rfl⟩))
    have hmem : Polynomial.aeval Δ P ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))) :=
      Algebra.adjoin_le (Set.singleton_subset_iff.2 hΔ) (Polynomial.aeval_mem_adjoin_singleton ℂ Δ)
    have hzero : ∀ y, (Polynomial.aeval Δ P f' : G → ℂ) y = 0 := by
      intro y; rw [hf'2 _ hmem y, hf]; rfl
    have hu : (fun y : E d => (f : G → ℂ) (g * h.expG (coordEquiv b y))) =
        fun y => (f' : G → ℂ) (h.expG (coordEquiv b y)) := by
      funext y; rw [hf'1]
    refine GlobalTheory.T.weakSolution_of_smooth_solution d (2 * P.natDegree) (Metric.ball 0 r) Metric.isOpen_ball a ha _
      (h.contDiff_comp_coordEquiv f.2 g b).contDiffOn ?_
    intro x hx
    rw [hopa, hu]
    have key := hzero (h.expG (coordEquiv b x))
    rw [Polynomial.aeval_eq_sum_range] at key
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, LinearMap.sum_apply, LinearMap.smul_apply] at key
    rw [← key, Finset.sum_range_succ _ P.natDegree, hP.coeff_natDegree, one_mul, add_comm]
    congr 1
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [hAop i f' x hx]
    · rw [hAop P.natDegree f' x hx]

end GlobalTheory.HCA
end

open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_elliptic_weakSol_of_polynomial_laplacian_zero : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∃ r > 0, ∃ (m : ℕ) (a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ), (∀ n w, ContDiffOn ℝ ∞ (a n w) (Metric.ball 0 r)) ∧ (∀ x ∈ Metric.ball (0 : E d) r, ∀ ξ : E d, ξ ≠ 0 → symb m a x ξ ≠ 0) ∧ ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P f = 0 → ∀ g : G, WeakSol (oneSys m a) (Metric.ball 0 r) (fun y => (f : G → ℂ) (g * h.expG (coordEquiv b (y)))) := by
  atlas_forward_decl GlobalTheory.HCA.exists_elliptic_weakSol_of_aeval_eq_zero
end

section
section
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.WordExp

theorem isSmoothFun_foldr {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
    {f : G → ℂ} (hf : h.IsSmoothFun f) : ∀ l : List 𝔤, h.IsSmoothFun (l.foldr h.rightDeriv f)
  | [] => hf
  | X :: l => h.isSmoothFun_rightDeriv (isSmoothFun_foldr h hf l) X

end GlobalTheory.WordExp

theorem GlobalTheory.WordExp.word_apOp : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (r : ℝ) (c : 𝔤 → Fin d → E d → ℝ), ((∀ X j, ContDiffOn ℝ ∞ (c X j) (Metric.ball 0 r)) ∧ (∀ x ∈ Metric.ball (0 : E d) r, ∀ ξ : E d, ξ ≠ 0 → ∃ i, ∑ j, c (b i) j x * ξ j ≠ 0) ∧ ∀ f : G → ℂ, h.IsSmoothFun f → ∀ X : 𝔤, ∀ x ∈ Metric.ball (0 : E d) r, h.rightDeriv X f (h.expG (coordEquiv b (x))) = ∑ j, (c X j x : ℂ) * fderiv ℝ (fun y => f (h.expG (coordEquiv b (y)))) x (ev j)) → ∀ l : List 𝔤, ∃ a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a n w) (Metric.ball 0 r)) ∧ ∀ f : G → ℂ, h.IsSmoothFun f → ∀ x ∈ Metric.ball (0 : E d) r, l.foldr h.rightDeriv f (h.expG (coordEquiv b (x))) = apOp l.length a (fun y => f (h.expG (coordEquiv b (y)))) x := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b r c hyp l
  obtain ⟨hc, -, hX⟩ := hyp
  induction l with
  | nil =>
    refine ⟨fun _ _ _ => 1, fun _ _ => contDiffOn_const, fun f _ x _ => ?_⟩
    simp only [List.foldr_nil, List.length_nil]
    rw [apOp_zero_one]
  | cons X l ih =>
    obtain ⟨a, ha, hl⟩ := ih
    have hcX : ∀ j, ContDiffOn ℝ ∞ (fun x : E d => ((c X j x : ℝ) : ℂ)) (Metric.ball 0 r) := fun j =>
      Complex.ofRealCLM.contDiff.comp_contDiffOn (hc X j)
    obtain ⟨a', ha', -, hcomp⟩ := GlobalTheory.VFComp.vectorField_comp d l.length (Metric.ball 0 r)
      Metric.isOpen_ball a (fun j x => ((c X j x : ℝ) : ℂ)) ha hcX
    refine ⟨a', ha', fun f hf x hx => ?_⟩
    simp only [List.foldr_cons, List.length_cons]
    have hF := GlobalTheory.WordExp.isSmoothFun_foldr h hf l
    rw [hX _ hF X x hx]
    have heq : (fun y : E d => l.foldr h.rightDeriv f (h.expG (coordEquiv b y))) =ᶠ[nhds x]
        apOp l.length a (fun y => f (h.expG (coordEquiv b y))) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy using hl f hf y hy
    have hu : ContDiffOn ℝ ∞ (fun y : E d => f (h.expG (coordEquiv b y))) (Metric.ball 0 r) := by
      have := h.contDiff_comp_coordEquiv hf 1 b
      simp only [one_mul] at this
      exact this.contDiffOn
    rw [heq.fderiv_eq]
    exact hcomp _ hu x hx
end

open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightDerivWord_expCoords_differentialOperator : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (r : ℝ) (c : 𝔤 → Fin d → E d → ℝ), ((∀ X j, ContDiffOn ℝ ∞ (c X j) (Metric.ball 0 r)) ∧ (∀ x ∈ Metric.ball (0 : E d) r, ∀ ξ : E d, ξ ≠ 0 → ∃ i, ∑ j, c (b i) j x * ξ j ≠ 0) ∧ ∀ f : G → ℂ, h.IsSmoothFun f → ∀ X : 𝔤, ∀ x ∈ Metric.ball (0 : E d) r, h.rightDeriv X f (h.expG (coordEquiv b (x))) = ∑ j, (c X j x : ℂ) * fderiv ℝ (fun y => f (h.expG (coordEquiv b (y)))) x (ev j)) → ∀ l : List 𝔤, ∃ a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a n w) (Metric.ball 0 r)) ∧ ∀ f : G → ℂ, h.IsSmoothFun f → ∀ x ∈ Metric.ball (0 : E d) r, l.foldr h.rightDeriv f (h.expG (coordEquiv b (x))) = apOp l.length a (fun y => f (h.expG (coordEquiv b (y)))) x := by
  atlas_forward_decl GlobalTheory.WordExp.word_apOp
end

section
section
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff Manifold

namespace GlobalTheory

open ZetaZeros.D.EllReg GlobalTheory.HCA

theorem foldr_rightDeriv_leftTranslate {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
    (F : G → ℂ) (g : G) (l : List 𝔤) :
    l.foldr h.rightDeriv (fun y => F (g * y)) = fun y => l.foldr h.rightDeriv F (g * y) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    funext y
    simp only [IsExpLieAlgebra.rightDeriv, mul_assoc]

theorem interior_word_bound : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∃ Kc : Set G, IsCompact Kc ∧ ∀ l : List 𝔤, ∃ C : ℝ, 0 ≤ C ∧ ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P f = 0 → ∀ (g : G) (M : ℝ), (∀ y ∈ Kc, ‖(f : G → ℂ) (g * y)‖ ≤ M) → ‖l.foldr h.rightDeriv (f : G → ℂ) g‖ ≤ C * M := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b P hP
  obtain ⟨r₁, hr₁, m, a, ha, hell, hsol⟩ := GlobalTheory.T.exists_elliptic_weakSol_of_polynomial_laplacian_zero 𝔸 G 𝔤 h d b P hP
  obtain ⟨r₂, hr₂, c, hc⟩ := GlobalTheory.T.leftInvariantVectorFields_expCoords_smooth_frame 𝔸 G 𝔤 h d b
  refine ⟨(fun x : E d => h.expG (coordEquiv b x)) '' Metric.closedBall 0 r₁,
    (isCompact_closedBall 0 r₁).image (h.continuous_expG.comp (coordEquiv b).continuous), ?_⟩
  intro l
  obtain ⟨al, -, hword⟩ := GlobalTheory.T.rightDerivWord_expCoords_differentialOperator 𝔸 G 𝔤 h d b r₂ c hc l
  have hsup : ∀ w : List (Fin d), ∃ C : ℝ, 0 ≤ C ∧ ∀ u : E d → ℂ, ContinuousOn u (Metric.ball 0 r₁) →
      WeakSol (oneSys m a) (Metric.ball 0 r₁) u → ∀ M : ℝ, (∀ x ∈ Metric.ball (0 : E d) r₁, ‖u x‖ ≤ M) →
      ‖dw w u 0‖ ≤ C * M := fun w =>
    GlobalTheory.T.elliptic_weakSol_wordDeriv_le_const_mul_sup d Unit (oneSys m a) (Metric.ball 0 r₁) Metric.isOpen_ball (fun _ n w => ha n w)
      (fun x hx ξ hξ => ⟨(), hell x hx ξ hξ⟩) w 0 (Metric.mem_ball_self hr₁)
  choose Cw hCw0 hCw using hsup
  refine ⟨∑ n ∈ Finset.range (l.length + 1), ∑ w : Fin n → Fin d, ‖al n w 0‖ * Cw (List.ofFn w),
    Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun w _ => mul_nonneg (norm_nonneg _) (hCw0 _), ?_⟩
  intro f hf g M hM
  have hfs : h.IsSmoothFun (f : G → ℂ) := f.2
  have hf' : h.IsSmoothFun (fun y : G => (f : G → ℂ) (g * y)) := by
    letI := h.chartedSpace
    haveI := h.lieGroup ∞
    exact ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hfs (contMDiff_const.mul contMDiff_id)
  have key : l.foldr h.rightDeriv (f : G → ℂ) g =
      apOp l.length al (fun y => (f : G → ℂ) (g * h.expG (coordEquiv b y))) 0 := by
    have := hword _ hf' 0 (Metric.mem_ball_self hr₂)
    rw [foldr_rightDeriv_leftTranslate] at this
    simpa [coordEquiv_zero] using this
  have hu : ContinuousOn (fun y => (f : G → ℂ) (g * h.expG (coordEquiv b y))) (Metric.ball 0 r₁) :=
    (h.contDiff_comp_coordEquiv hfs g b).continuous.continuousOn
  have hbd : ∀ x ∈ Metric.ball (0 : E d) r₁, ‖(f : G → ℂ) (g * h.expG (coordEquiv b x))‖ ≤ M :=
    fun x hx => hM _ ⟨x, Metric.ball_subset_closedBall hx, rfl⟩
  have hdw : ∀ w : List (Fin d),
      ‖dw w (fun y => (f : G → ℂ) (g * h.expG (coordEquiv b y))) 0‖ ≤ Cw w * M :=
    fun w => hCw w _ hu (hsol f hf g) M hbd
  rw [key, apOp]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun n _ => ?_
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hdw _) (norm_nonneg _)

end GlobalTheory
end

open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_interior_estimate_deriv_word_polyLaplacian : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (P : Polynomial ℂ), P.Monic → ∃ Kc : Set G, IsCompact Kc ∧ ∀ l : List 𝔤, ∃ C : ℝ, 0 ≤ C ∧ ∀ f : h.smoothFuns (F := ℂ), Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P f = 0 → ∀ (g : G) (M : ℝ), (∀ y ∈ Kc, ‖(f : G → ℂ) (g * y)‖ ≤ M) → ‖l.foldr h.rightDeriv (f : G → ℂ) g‖ ≤ C * M := by
  atlas_forward_decl GlobalTheory.interior_word_bound
end
