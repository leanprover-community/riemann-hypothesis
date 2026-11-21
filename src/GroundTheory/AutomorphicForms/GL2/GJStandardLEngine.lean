import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJStandardLTensor
import GroundTheory.AutomorphicForms.GL2.GJStandardLDefs

section
open MeasureTheory Filter Set Topology Metric IsDedekindDomain NumberField NumberField.mixedEmbedding
open scoped NumberField.AdeleRing SchwartzMap Classical ENNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace GJStandardL

open GodementJacquet GLnLocal

set_option linter.unusedSectionVars false

section Local

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]

theorem exists_localBump (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] {V : Type*} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin n) F) V) {ξ : V} (hξ : ξ ∈ smoothVectors π)
    (ℓ : Module.Dual ℂ V) {g₀ : GL (Fin n) F} (h0 : Parabolic.matrixCoeff π ξ ℓ g₀ ≠ 0) :
    ∃ Φ : Matrix (Fin n) (Fin n) F → ℂ, IsSchwartzBruhat Φ ∧ ∃ a : ℂ, a ≠ 0 ∧ ∀ s : ℂ,
      Integrable (fun g : GL (Fin n) F ↦ Φ (g : Matrix (Fin n) (Fin n) F) * Parabolic.matrixCoeff π ξ ℓ g *
        detPow g (s + ((n : ℂ) - 1) / 2)) μ ∧
      ∫⁻ g : GL (Fin n) F, ‖Φ (g : Matrix (Fin n) (Fin n) F) * Parabolic.matrixCoeff π ξ ℓ g *
        detPow g (s + ((n : ℂ) - 1) / 2)‖ₑ ∂μ ≠ 0 ∧
      zetaIntegral μ Φ (Parabolic.matrixCoeff π ξ ℓ) s = a * detPow g₀ (s + ((n : ℂ) - 1) / 2) := by
  set U : Subgroup (GL (Fin n) F) := stabilizerOf π ξ ⊓ integralGL F n with hU
  have hUo : IsOpen (U : Set (GL (Fin n) F)) := by
    rw [hU, Subgroup.coe_inf]
    exact (mem_smoothVectors.1 hξ).inter (isOpen_integralGL F n)
  have hUc : IsCompact (U : Set (GL (Fin n) F)) :=
    (isCompact_integralGL F n).of_isClosed_subset (Subgroup.isClosed_of_isOpen U hUo)
      (by rw [hU, Subgroup.coe_inf]; exact inter_subset_right)
  set W : Set (GL (Fin n) F) := (g₀ * ·) '' (U : Set (GL (Fin n) F)) with hW
  have hWo : IsOpen W := (Homeomorph.mulLeft g₀).isOpenMap _ hUo
  have hWc : IsCompact W := hUc.image (continuous_const_mul g₀)
  have hWm : MeasurableSet W := hWo.measurableSet
  have hg₀ : g₀ ∈ W := ⟨1, U.one_mem, mul_one g₀⟩
  have hval := Measures.isOpenEmbedding_val F n
  set S : Set (Matrix (Fin n) (Fin n) F) := Units.val '' W with hS
  have hSo : IsOpen S := hval.isOpenMap _ hWo
  have hSc : IsCompact S := hWc.image Units.continuous_val
  have hmemS : ∀ g : GL (Fin n) F, (g : Matrix (Fin n) (Fin n) F) ∈ S ↔ g ∈ W := by
    intro g
    constructor
    · rintro ⟨h, hh, he⟩
      rwa [← Units.ext he]
    · intro h
      exact ⟨g, h, rfl⟩
  set Φ : Matrix (Fin n) (Fin n) F → ℂ := S.indicator fun _ ↦ (1 : ℂ) with hΦ
  set c : ℂ := Parabolic.matrixCoeff π ξ ℓ g₀ with hc
  have hfW : ∀ g ∈ W, Parabolic.matrixCoeff π ξ ℓ g = c := by
    rintro g ⟨u, hu, rfl⟩
    have hu1 : π u ξ = ξ := mem_stabilizerOf.1 (Subgroup.mem_inf.1 hu).1
    simp only [hc, Parabolic.matrixCoeff, map_mul, Module.End.mul_apply, hu1]
  have hdW : ∀ g ∈ W, ∀ s, detPow g s = detPow g₀ s := by
    rintro g ⟨u, hu, rfl⟩ s
    rw [detPow_mul, detPow_of_mem_integralGL (Subgroup.mem_inf.1 hu).2, mul_one]
  have hfun' : ∀ (s : ℂ) (g : GL (Fin n) F), Φ g * Parabolic.matrixCoeff π ξ ℓ g * detPow g s =
      W.indicator (fun _ ↦ c * detPow g₀ s) g := by
    intro s g
    by_cases hg : g ∈ W
    · rw [hΦ, indicator_of_mem ((hmemS g).2 hg), indicator_of_mem hg, one_mul, hfW g hg, hdW g hg]
    · rw [hΦ, indicator_of_notMem (fun h ↦ hg ((hmemS g).1 h)), indicator_of_notMem hg, zero_mul,
        zero_mul]
  have hfun : ∀ s : ℂ, (fun g : GL (Fin n) F ↦ Φ g * Parabolic.matrixCoeff π ξ ℓ g * detPow g s) =
      W.indicator fun _ ↦ c * detPow g₀ s := fun s ↦ funext (hfun' s)
  have hdne : ∀ s, detPow g₀ s ≠ 0 := fun s ↦ by
    rw [detPow_eq_qs_zpow]
    exact zpow_ne_zero _ (qs_ne_zero s)
  have hWpos : 0 < μ.real W :=
    ENNReal.toReal_pos (hWo.measure_pos μ ⟨g₀, hg₀⟩).ne' hWc.measure_lt_top.ne
  refine ⟨Φ, ⟨?_, ?_⟩, (μ.real W : ℂ) * c, mul_ne_zero (by exact_mod_cast hWpos.ne') h0, fun s ↦ ⟨?_, ?_, ?_⟩⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro X
    by_cases hX : X ∈ S
    · exact ⟨S, hSo, hX, fun Y hY ↦ by rw [hΦ, indicator_of_mem hY, indicator_of_mem hX]⟩
    · exact ⟨Sᶜ, hSc.isClosed.isOpen_compl, hX, fun Y hY ↦ by
        rw [hΦ, indicator_of_notMem hY, indicator_of_notMem hX]⟩
  · exact HasCompactSupport.intro hSc fun x hx ↦ indicator_of_notMem hx _
  · rw [hfun]
    exact (integrableOn_const hWc.measure_lt_top.ne).integrable_indicator hWm
  · simp_rw [hfun', enorm_indicator_eq_indicator_enorm]
    rw [lintegral_indicator_const hWm]
    exact mul_ne_zero (enorm_ne_zero.2 (mul_ne_zero h0 (hdne _))) (hWo.measure_pos μ ⟨g₀, hg₀⟩).ne'
  · rw [zetaIntegral]
    rw [hfun, integral_indicator_const _ hWm, Complex.real_smul]
    ring

end Local

section Arch

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem isUnit_infiniteAdeleRing_iff {x : InfiniteAdeleRing K} :
    IsUnit x ↔ ∀ w : InfinitePlace K, x w ≠ 0 := by
  constructor
  · rintro ⟨u, rfl⟩ w hw
    have h := congrFun u.mul_inv w
    change (u : InfiniteAdeleRing K) w * (↑u⁻¹ : InfiniteAdeleRing K) w = 1 at h
    rw [hw, zero_mul] at h
    exact zero_ne_one h
  · intro h
    refine ⟨⟨x, fun w ↦ (x w)⁻¹, ?_, ?_⟩, rfl⟩
    · funext w
      exact mul_inv_cancel₀ (h w)
    · funext w
      exact inv_mul_cancel₀ (h w)

def infInv (x : InfiniteAdeleRing K) : InfiniteAdeleRing K := fun w ↦ (x w)⁻¹

theorem ringInverse_eq_infInv {x : InfiniteAdeleRing K} (hx : IsUnit x) : Ring.inverse x = infInv x := by
  have h1 : Ring.inverse x * x = 1 := Ring.inverse_mul_cancel x hx
  funext w
  have h2 := congrFun h1 w
  exact eq_inv_of_mul_eq_one_left h2

variable (K n) in

theorem isOpenEmbedding_val_infiniteAdelicGL :
    IsOpenEmbedding (Units.val : AdelicGLn.InfiniteAdelicGL K n → Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) := by
  have hdet : Continuous fun A : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K) ↦ A.det :=
    Continuous.matrix_det (continuous_id (X := Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)))
  refine ⟨Units.isEmbedding_val_mk' (f := fun A ↦ infInv A.det • A.adjugate) ?_ fun u ↦ ?_, ?_⟩
  · have h1 : ContinuousOn (fun A : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K) ↦
        ((fun w ↦ (A.det w)⁻¹ : ∀ w : InfinitePlace K, w.Completion))) {A | IsUnit A} := by
      refine continuousOn_pi.2 fun w ↦ ?_
      exact ((continuous_apply (A := fun v : InfinitePlace K ↦ v.Completion) w).comp hdet).continuousOn.inv₀
        fun A hA ↦ isUnit_infiniteAdeleRing_iff.1 ((Matrix.isUnit_iff_isUnit_det A).1 hA) w
    have h2 : Continuous fun A : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K) ↦ A.adjugate :=
      Continuous.matrix_adjugate (continuous_id (X := Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)))
    exact ContinuousOn.smul (M := InfiniteAdeleRing K) h1 h2.continuousOn
  · have hu : IsUnit (u : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit
    show infInv (u : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)).det •
      (u : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)).adjugate = ↑u⁻¹
    rw [Matrix.coe_units_inv, Matrix.inv_def, ringInverse_eq_infInv hu]
  · have : Set.range (Units.val : AdelicGLn.InfiniteAdelicGL K n → Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) =
        ⋂ w : InfinitePlace K, (fun A : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K) ↦ A.det w) ⁻¹' {0}ᶜ := by
      ext A
      simp only [Set.mem_range, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨u, rfl⟩
        exact isUnit_infiniteAdeleRing_iff.1 ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit)
      · intro h
        exact ⟨((Matrix.isUnit_iff_isUnit_det A).2 (isUnit_infiniteAdeleRing_iff.2 h)).unit, rfl⟩
    rw [this]
    exact isOpen_iInter_of_finite fun w ↦
      isOpen_compl_singleton.preimage ((continuous_apply w).comp hdet)

variable (K n) in

def archEntries : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K) ≃ₜ (Fin n × Fin n → mixedSpace K) where
  toFun x ij := GroundTheory.Global.homeomorphMixedSpace K (x ij.1 ij.2)
  invFun y := Matrix.of fun i j ↦ (GroundTheory.Global.homeomorphMixedSpace K).symm (y (i, j))
  left_inv x := by
    ext i j
    simp
  right_inv y := by
    funext ij
    simp
  continuous_toFun := continuous_pi fun ij ↦ (GroundTheory.Global.homeomorphMixedSpace K).continuous.comp
    ((continuous_apply ij.2).comp (continuous_apply ij.1))
  continuous_invFun := continuous_pi fun i ↦ continuous_pi fun j ↦
    (GroundTheory.Global.homeomorphMixedSpace K).symm.continuous.comp (continuous_apply (i, j))

theorem archSchwartz_eq (φ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ))
    (x : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) : archSchwartz φ x = φ (archEntries K n x) := rfl

theorem archAbsDet_pos (x : AdelicGLn.InfiniteAdelicGL K n) : 0 < archAbsDet x := by
  have hu : IsUnit (x : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 x.isUnit
  exact Finset.prod_pos fun w _ ↦ pow_pos (norm_pos_iff.2 (isUnit_infiniteAdeleRing_iff.1 hu w)) _

theorem continuous_det_infiniteAdelicGL :
    Continuous fun x : AdelicGLn.InfiniteAdelicGL K n ↦ (x : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)).det :=
  (Continuous.matrix_det (continuous_id (X := Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)))).comp
    Units.continuous_val

theorem continuous_archAbsDet : Continuous (archAbsDet (K := K) (n := n)) := by
  refine continuous_finsetProd _ fun w _ ↦ ?_
  have h : Continuous fun x : AdelicGLn.InfiniteAdelicGL K n ↦
      (x : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)).det w :=
    (continuous_apply (A := fun v : InfinitePlace K ↦ v.Completion) w).comp continuous_det_infiniteAdelicGL
  exact (continuous_norm.comp h).pow _

theorem continuous_archDetPow (s : ℂ) : Continuous fun x : AdelicGLn.InfiniteAdelicGL K n ↦ archDetPow x s :=
  (Complex.continuous_ofReal.comp continuous_archAbsDet).cpow continuous_const fun x ↦
    Complex.ofReal_mem_slitPlane.2 (archAbsDet_pos x)

theorem archDetPow_ne_zero (x : AdelicGLn.InfiniteAdelicGL K n) (s : ℂ) : archDetPow x s ≠ 0 := by
  rw [archDetPow, Ne, Complex.cpow_eq_zero_iff]
  exact fun h ↦ (archAbsDet_pos x).ne' (by exact_mod_cast h.1)

theorem exists_archBump (μ : Measure (AdelicGLn.InfiniteAdelicGL K n)) [μ.IsHaarMeasure]
    {f : AdelicGLn.InfiniteAdelicGL K n → ℂ} (hf : Continuous f) {x₀ : AdelicGLn.InfiniteAdelicGL K n}
    (h0 : f x₀ ≠ 0) :
    ∃ φ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ), (∀ s, Integrable (archIntegrand φ f s) μ) ∧
      (∀ s, ∫⁻ x, ‖archIntegrand φ f s x‖ₑ ∂μ ≠ 0) ∧ Differentiable ℂ (archZeta μ φ f) ∧
      ∃ s, archZeta μ φ f s ≠ 0 := by
  set J : AdelicGLn.InfiniteAdelicGL K n → (Fin n × Fin n → mixedSpace K) :=
    fun x ↦ archEntries K n (x : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) with hJdef
  have hJ : IsOpenEmbedding J :=
    (archEntries K n).isOpenEmbedding.comp (isOpenEmbedding_val_infiniteAdelicGL K n)
  set c₀ : ℂ := f x₀ with hc₀
  set W : Set (AdelicGLn.InfiniteAdelicGL K n) := {x | 0 < (starRingEnd ℂ c₀ * f x).re} with hWdef
  have hWo : IsOpen W := isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_const.mul hf))
  have hc₀re : 0 < (starRingEnd ℂ c₀ * c₀).re := by
    rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    exact pow_pos (norm_pos_iff.2 h0) 2
  have hx₀W : x₀ ∈ W := hc₀re
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hJ.isOpenMap W hWo) (J x₀) ⟨x₀, hx₀W, rfl⟩
  let ψ : ContDiffBump (J x₀) := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hψc : HasCompactSupport fun y ↦ (ψ y : ℂ) := ψ.hasCompactSupport.comp_left Complex.ofReal_zero
  have hψd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y ↦ (ψ y : ℂ) := Complex.ofRealCLM.contDiff.comp ψ.contDiff
  set φ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ) := hψc.toSchwartzMap hψd with hφdef
  have hsub : closedBall (J x₀) (ε / 2) ⊆ J '' W := fun y hy ↦
    hball (closedBall_subset_ball (by linarith) hy)
  have hKc : IsCompact (J ⁻¹' closedBall (J x₀) (ε / 2)) := by
    rw [hJ.isEmbedding.isCompact_iff, image_preimage_eq_of_subset (hsub.trans (image_subset_range _ _))]
    exact isCompact_closedBall _ _
  have hψzero : ∀ x, x ∉ J ⁻¹' closedBall (J x₀) (ε / 2) → ψ (J x) = 0 := by
    intro x hx
    by_contra h
    have : J x ∈ Function.support ψ := h
    rw [ψ.support_eq] at this
    exact hx (ball_subset_closedBall this)
  have hψW : ∀ x, ψ (J x) ≠ 0 → x ∈ W := by
    intro x hx
    have : J x ∈ Function.support ψ := hx
    rw [ψ.support_eq] at this
    obtain ⟨y, hy, hyx⟩ := hball (ball_subset_ball (show ψ.rOut ≤ ε from by show ε / 2 ≤ ε; linarith) this)
    rwa [← hJ.injective hyx]
  have hcontψ : Continuous fun x ↦ (ψ (J x) : ℂ) :=
    Complex.continuous_ofReal.comp (ψ.continuous.comp hJ.continuous)
  have hint_eq : ∀ s x, archIntegrand φ f s x =
      (ψ (J x) : ℂ) * f x * archDetPow x (s + ((n : ℂ) - 1) / 2) := fun s x ↦ rfl
  have hcont : ∀ s, Continuous (archIntegrand φ f s) := fun s ↦ by
    have : archIntegrand φ f s = fun x ↦ (ψ (J x) : ℂ) * f x * archDetPow x (s + ((n : ℂ) - 1) / 2) :=
      funext (hint_eq s)
    rw [this]
    exact (hcontψ.mul hf).mul (continuous_archDetPow _)
  have hcs : ∀ s, HasCompactSupport (archIntegrand φ f s) := fun s ↦
    HasCompactSupport.intro hKc fun x hx ↦ by
      rw [hint_eq, hψzero x hx, Complex.ofReal_zero, zero_mul, zero_mul]
  have hInt : ∀ s, Integrable (archIntegrand φ f s) μ := fun s ↦
    (hcont s).integrable_of_hasCompactSupport (hcs s)
  have hψ₀ : ψ (J x₀) = 1 := ψ.one_of_mem_closedBall (mem_closedBall_self (by positivity))
  have hne₀ : ∀ s, archIntegrand φ f s x₀ ≠ 0 := fun s ↦ by
    rw [hint_eq, hψ₀, Complex.ofReal_one, one_mul]
    exact mul_ne_zero h0 (archDetPow_ne_zero _ _)
  refine ⟨φ, hInt, fun s hzero ↦ ?_, ?_, ?_⟩
  · have hae := (lintegral_eq_zero_iff' (hcont s).enorm.aemeasurable).1 hzero
    have hae' : archIntegrand φ f s =ᵐ[μ] 0 := hae.mono fun x hx ↦ enorm_eq_zero.1 hx
    have := (Continuous.ae_eq_iff_eq μ (hcont s) continuous_const).1 hae'
    exact hne₀ s (congrFun this x₀)
  ·
    intro s₀
    set c' : ℂ := ((n : ℂ) - 1) / 2 with hc'
    set σ : ℝ := (s₀ + c').re with hσ
    set A : AdelicGLn.InfiniteAdelicGL K n → ℝ := archAbsDet with hAdef
    have hA : ∀ x, 0 < A x := archAbsDet_pos
    have hAc : Continuous A := continuous_archAbsDet
    set g : AdelicGLn.InfiniteAdelicGL K n → ℂ := fun x ↦ (ψ (J x) : ℂ) * f x with hg
    have hgc : Continuous g := hcontψ.mul hf
    set F' : ℂ → AdelicGLn.InfiniteAdelicGL K n → ℂ :=
      fun s x ↦ g x * ((A x : ℂ) ^ (s + c') * Complex.log (A x)) with hF'
    set bound : AdelicGLn.InfiniteAdelicGL K n → ℝ :=
      fun x ↦ ‖g x‖ * (A x ^ (σ - 1) + A x ^ (σ + 1)) * |Real.log (A x)| with hbound
    have hderiv : ∀ x, ∀ s ∈ ball s₀ 1, HasDerivAt (fun s ↦ archIntegrand φ f s x) (F' s x) s := by
      intro x s _
      have h1 : HasDerivAt (fun s : ℂ ↦ (A x : ℂ) ^ (s + c'))
          ((A x : ℂ) ^ (s + c') * Complex.log (A x) * 1) s :=
        ((hasDerivAt_id s).add_const c').const_cpow (Or.inl (by exact_mod_cast (hA x).ne'))
      have h2 := h1.const_mul (g x)
      simp only [mul_one] at h2
      exact h2
    have hbd : ∀ x, ∀ s ∈ ball s₀ 1, ‖F' s x‖ ≤ bound x := by
      intro x s hs
      have hre : |s.re - s₀.re| < 1 := by
        rw [← Complex.sub_re]
        exact (Complex.abs_re_le_norm _).trans_lt (by rwa [mem_ball, dist_eq_norm] at hs)
      have hnorm1 : ‖(A x : ℂ) ^ (s + c')‖ = A x ^ (s + c').re :=
        Complex.norm_cpow_eq_rpow_re_of_pos (hA x) _
      have hnorm2 : ‖Complex.log (A x : ℂ)‖ = |Real.log (A x)| := by
        rw [← Complex.ofReal_log (hA x).le, Complex.norm_real, Real.norm_eq_abs]
      have hexp : (s + c').re = s.re + c'.re := Complex.add_re _ _
      have hσ' : σ = s₀.re + c'.re := Complex.add_re _ _
      have hrpow : A x ^ (s + c').re ≤ A x ^ (σ - 1) + A x ^ (σ + 1) := by
        rw [abs_lt] at hre
        by_cases h1 : 1 ≤ A x
        · calc A x ^ (s + c').re ≤ A x ^ (σ + 1) :=
                Real.rpow_le_rpow_of_exponent_le h1 (by rw [hexp, hσ']; linarith)
            _ ≤ _ := le_add_of_nonneg_left (Real.rpow_nonneg (hA x).le _)
        · push Not at h1
          calc A x ^ (s + c').re ≤ A x ^ (σ - 1) :=
                Real.rpow_le_rpow_of_exponent_ge (hA x) h1.le (by rw [hexp, hσ']; linarith)
            _ ≤ _ := le_add_of_nonneg_right (Real.rpow_nonneg (hA x).le _)
      simp only [hF', hbound, norm_mul, hnorm1, hnorm2]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrpow (abs_nonneg _)) (norm_nonneg _)
    have hboundc : Continuous bound :=
      ((continuous_norm.comp hgc).mul ((hAc.rpow_const fun x ↦ Or.inl (hA x).ne').add
        (hAc.rpow_const fun x ↦ Or.inl (hA x).ne'))).mul (hAc.log fun x ↦ (hA x).ne').abs
    have hbint : Integrable bound μ := by
      refine hboundc.integrable_of_hasCompactSupport (HasCompactSupport.intro hKc fun x hx ↦ ?_)
      simp only [hbound, hg, hψzero x hx, Complex.ofReal_zero, zero_mul, norm_zero]
    have hF'c : Continuous (F' s₀) :=
      hgc.mul ((continuous_archDetPow (s₀ + c')).mul
        ((Complex.continuous_ofReal.comp hAc).clog fun x ↦ Complex.ofReal_mem_slitPlane.2 (hA x)))
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun s x ↦ archIntegrand φ f s x) (x₀ := s₀) (ball_mem_nhds s₀ one_pos)
      (Filter.Eventually.of_forall fun s ↦ (hcont s).aestronglyMeasurable) (hInt s₀) (F' := F')
      hF'c.aestronglyMeasurable (ae_of_all _ fun x s hs ↦ hbd x s hs) hbint
      (ae_of_all _ fun x s hs ↦ hderiv x s hs)
    exact key.2.differentiableAt
  ·
    refine ⟨-(((n : ℂ) - 1) / 2), fun hz ↦ ?_⟩
    have hint1 : ∀ x, archIntegrand φ f (-(((n : ℂ) - 1) / 2)) x = (ψ (J x) : ℂ) * f x := fun x ↦ by
      rw [hint_eq, neg_add_cancel, archDetPow, Complex.cpow_zero, mul_one]
    set r : AdelicGLn.InfiniteAdelicGL K n → ℝ := fun x ↦ ψ (J x) * (starRingEnd ℂ c₀ * f x).re with hr
    have hr_eq : ∀ x, (starRingEnd ℂ c₀ * archIntegrand φ f (-(((n : ℂ) - 1) / 2)) x).re = r x := fun x ↦ by
      rw [hint1, mul_left_comm, Complex.re_ofReal_mul]
    have hrc : Continuous r :=
      (ψ.continuous.comp hJ.continuous).mul (Complex.continuous_re.comp (continuous_const.mul hf))
    have hr0 : 0 ≤ r := fun x ↦ by
      by_cases hx : ψ (J x) = 0
      · simp only [hr, hx, zero_mul, Pi.zero_apply, le_refl]
      · exact mul_nonneg ψ.nonneg (hψW x hx).le
    have hrint : Integrable r μ := by
      refine hrc.integrable_of_hasCompactSupport (HasCompactSupport.intro hKc fun x hx ↦ ?_)
      simp only [hr, hψzero x hx, zero_mul]
    have hpos : 0 < ∫ x, r x ∂μ := by
      rw [integral_pos_iff_support_of_nonneg hr0 hrint]
      refine hrc.isOpen_support.measure_pos μ ⟨x₀, ?_⟩
      show r x₀ ≠ 0
      simp only [hr, hψ₀, one_mul]
      exact hc₀re.ne'
    have hre := integral_re ((hInt (-(((n : ℂ) - 1) / 2))).const_mul (starRingEnd ℂ c₀))
    simp only [RCLike.re_to_complex] at hre
    have heq : ∫ x, r x ∂μ = (starRingEnd ℂ c₀ * archZeta μ φ f (-(((n : ℂ) - 1) / 2))).re := by
      rw [archZeta, ← integral_const_mul, ← hre]
      exact integral_congr_ae (ae_of_all _ fun x ↦ (hr_eq x).symm)
    rw [hz, mul_zero, Complex.zero_re] at heq
    linarith

end Arch

end GJStandardL

end

end GroundTheory.Automorphic
end

section
open MeasureTheory Filter Set Topology IsDedekindDomain NumberField NumberField.mixedEmbedding
open scoped NumberField.AdeleRing RestrictedProduct SchwartzMap Classical ENNReal NNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace GJStandardL

open GodementJacquet GLnLocal

section Local

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem continuous_matrixCoeff_of_smooth (π : Representation ℂ (GL (Fin n) F) V) {ξ : V}
    (hξ : ξ ∈ smoothVectors π) (ℓ : Module.Dual ℂ V) : Continuous (Parabolic.matrixCoeff π ξ ℓ) := by
  refine continuous_iff_continuousAt.2 fun g ↦ ?_
  have hopen : IsOpen ((fun h ↦ g⁻¹ * h) ⁻¹' (stabilizerOf π ξ : Set (GL (Fin n) F))) :=
    (mem_smoothVectors.1 hξ).preimage (continuous_const.mul continuous_id)
  have hg : g ∈ (fun h ↦ g⁻¹ * h) ⁻¹' (stabilizerOf π ξ : Set (GL (Fin n) F)) := by
    simp only [mem_preimage, inv_mul_cancel, SetLike.mem_coe]
    exact (stabilizerOf π ξ).one_mem
  refine (continuousAt_const (y := Parabolic.matrixCoeff π ξ ℓ g)).congr ?_
  filter_upwards [hopen.mem_nhds hg] with h hh
  have hfix : π (g⁻¹ * h) ξ = ξ := mem_stabilizerOf.1 hh
  have : π h ξ = π g ξ := by
    calc π h ξ = π (g * (g⁻¹ * h)) ξ := by rw [mul_inv_cancel_left]
      _ = π g (π (g⁻¹ * h) ξ) := by rw [map_mul, Module.End.mul_apply]
      _ = π g ξ := by rw [hfix]
  simp only [Parabolic.matrixCoeff]
  rw [this]

theorem continuous_localIntegrand [MeasurableSpace (GL (Fin n) F)] {Φ : Matrix (Fin n) (Fin n) F → ℂ}
    (hΦ : Continuous Φ) (π : Representation ℂ (GL (Fin n) F) V) {ξ : V} (hξ : ξ ∈ smoothVectors π)
    (ℓ : Module.Dual ℂ V) (s : ℂ) :
    Continuous fun g : GL (Fin n) F ↦
      Φ (g : Matrix (Fin n) (Fin n) F) * Parabolic.matrixCoeff π ξ ℓ g * detPow g (s + ((n : ℂ) - 1) / 2) :=
  ((hΦ.comp Units.continuous_val).mul (continuous_matrixCoeff_of_smooth π hξ ℓ)).mul (continuous_detPow _)

theorem localIntegrand_of_mem_integralGL (π : Representation ℂ (GL (Fin n) F) V) {ξ : V}
    (hξ : ξ ∈ fixedVectors π (integralGL F n)) {ℓ : Module.Dual ℂ V} (hℓ : ℓ ξ = 1) (s : ℂ)
    {k : GL (Fin n) F} (hk : k ∈ integralGL F n) :
    integralIndicator F n (k : Matrix (Fin n) (Fin n) F) * Parabolic.matrixCoeff π ξ ℓ k *
      detPow k (s + ((n : ℂ) - 1) / 2) = 1 := by
  have h1 : integralIndicator F n (k : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [integralIndicator, Set.indicator_of_mem (mem_integralMatrixSet.2 ((mem_integralGL_iff F n).1 hk).1)]
    rfl
  have h2 : Parabolic.matrixCoeff π ξ ℓ k = 1 := by
    rw [Parabolic.matrixCoeff, hξ k hk, hℓ]
  rw [h1, h2, detPow_of_mem_integralGL hk, one_mul, one_mul]

end Local

section Det

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def adeleToLocal (v : HeightOneSpectrum (𝓞 K)) : 𝔸[K] →+* v.adicCompletion K :=
  (GodementSection.adeleAt v).comp (RingHom.snd _ _)

theorem det_localMat (v : HeightOneSpectrum (𝓞 K)) (x : Matrix (Fin n) (Fin n) 𝔸[K]) :
    (localMat v x).det = (x.det).2 v :=
  (RingHom.map_det (adeleToLocal v) x).symm

theorem det_archMat (x : Matrix (Fin n) (Fin n) 𝔸[K]) : (archMat x).det = (x.det).1 :=
  (RingHom.map_det (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) x).symm

theorem absDet_localComp (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGLn.AdelicGL K n) :
    absDet (localComp n v g) = ‖((g : Matrix (Fin n) (Fin n) 𝔸[K]).det).2 v‖ := by
  rw [absDet, coe_localComp, det_localMat, GodementSection.modulus_adicCompletion]

theorem archAbsDet_archComp (g : AdelicGLn.AdelicGL K n) :
    archAbsDet (archComp K n g) =
      ∏ w : InfinitePlace K, ‖((g : Matrix (Fin n) (Fin n) 𝔸[K]).det).1 w‖ ^ w.mult := by
  rw [archAbsDet, coe_archComp, det_archMat]

theorem detModule_eq (g : AdelicGLn.AdelicGL K n) :
    (Reduction.detModule K n g : ℝ) = archAbsDet (archComp K n g) * ∏ᶠ v, absDet (localComp n v g) := by
  rw [archAbsDet_archComp]
  simp_rw [absDet_localComp]
  show (GroundTheory.Global.IdeleGroup.ideleModule K (AdelicGLn.det K n g) : ℝ) = _
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq, AdelicGLn.coe_det]

theorem absDet_of_mem_integralGL {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {k : GL (Fin n) F} (hk : k ∈ integralGL F n) : absDet k = 1 := by
  have h := detPow_of_mem_integralGL hk 1
  rw [detPow, Complex.cpow_one] at h
  exact_mod_cast h

theorem finite_setOf_not_mem (g : AdelicGLn.AdelicGL K n) :
    {v : HeightOneSpectrum (𝓞 K) | localComp n v g ∉ integralGL (v.adicCompletion K) n}.Finite :=
  Filter.eventually_cofinite.1 (eventually_localComp_mem g)

theorem detPow_eq (g : AdelicGLn.AdelicGL K n) (s : ℂ) :
    GJGlobal.detPow g s = archDetPow (archComp K n g) s * ∏ᶠ v, detPow (localComp n v g) s := by
  set T := (finite_setOf_not_mem g).toFinset with hT
  have hsub : ∀ v ∉ T, localComp n v g ∈ integralGL (v.adicCompletion K) n := fun v hv ↦ by
    by_contra h
    exact hv ((finite_setOf_not_mem g).mem_toFinset.2 h)
  have h1 : ∏ᶠ v, absDet (localComp n v g) = ∏ v ∈ T, absDet (localComp n v g) :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ by
      by_contra hvT
      exact hv (absDet_of_mem_integralGL (hsub v hvT))
  have h2 : ∏ᶠ v, detPow (localComp n v g) s = ∏ v ∈ T, detPow (localComp n v g) s :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ by
      by_contra hvT
      exact hv (detPow_of_mem_integralGL (hsub v hvT) s)
  have hA : 0 ≤ archAbsDet (archComp K n g) :=
    Finset.prod_nonneg fun w _ ↦ pow_nonneg (norm_nonneg _) _
  have hB : ∀ v, 0 ≤ absDet (localComp n v g) := fun v ↦ NNReal.coe_nonneg _
  rw [GJGlobal.detPow, detModule_eq, h1, h2, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hA (Finset.prod_nonneg fun v _ ↦ hB v),
    GodementSection.ofReal_prod_cpow T _ hB]
  rfl

end Det

section Product

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def prodConst (ν : Measure (AdelicGLn.AdelicGL K n)) [ν.IsHaarMeasure]
    (μi : Measure (AdelicGLn.InfiniteAdelicGL K n)) [μi.IsHaarMeasure] : ℝ≥0 :=
  Measure.haarScalarFactor (ν.map (AdelicGLn.prodEquiv K n))
    (μi.prod (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)))

theorem prodConst_pos (ν : Measure (AdelicGLn.AdelicGL K n)) [ν.IsHaarMeasure]
    (μi : Measure (AdelicGLn.InfiniteAdelicGL K n)) [μi.IsHaarMeasure] : 0 < prodConst ν μi :=
  Measure.haarScalarFactor_pos_of_isHaarMeasure _ _

theorem map_prodEquiv_eq (ν : Measure (AdelicGLn.AdelicGL K n)) [ν.IsHaarMeasure]
    (μi : Measure (AdelicGLn.InfiniteAdelicGL K n)) [μi.IsHaarMeasure] :
    ν.map (AdelicGLn.prodEquiv K n) =
      prodConst ν μi • μi.prod (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)) :=
  Measure.isMulLeftInvariant_eq_smul _ _

theorem integral_eq_mul (ν : Measure (AdelicGLn.AdelicGL K n)) [ν.IsHaarMeasure]
    (μi : Measure (AdelicGLn.InfiniteAdelicGL K n)) [μi.IsHaarMeasure]
    (A : AdelicGLn.InfiniteAdelicGL K n → ℂ) (B : AdelicGLn.FiniteAdelicGL K n → ℂ) :
    ∫ g, A (archComp K n g) * B (finComp K n g) ∂ν =
      ((prodConst ν μi : ℝ) : ℂ) * ((∫ x, A x ∂μi) * ∫ y, B y ∂Measure.haar) := by
  set me := (AdelicGLn.prodEquiv K n).toHomeomorph.toMeasurableEquiv
  have h1 : ∫ g, A (archComp K n g) * B (finComp K n g) ∂ν = ∫ p, A p.1 * B p.2 ∂(ν.map me) := by
    rw [integral_map_equiv me (fun p ↦ A p.1 * B p.2)]
    rfl
  have hme : ν.map me = ν.map (AdelicGLn.prodEquiv K n) := rfl
  rw [h1, hme, map_prodEquiv_eq ν μi, integral_smul_nnreal_measure, integral_prod_mul, NNReal.smul_def,
    Complex.real_smul]

theorem lintegral_eq_mul (ν : Measure (AdelicGLn.AdelicGL K n)) [ν.IsHaarMeasure]
    (μi : Measure (AdelicGLn.InfiniteAdelicGL K n)) [μi.IsHaarMeasure]
    {A : AdelicGLn.InfiniteAdelicGL K n → ℂ} {B : AdelicGLn.FiniteAdelicGL K n → ℂ}
    (hA : Measurable A) (hB : Measurable B) :
    ∫⁻ g, ‖A (archComp K n g) * B (finComp K n g)‖ₑ ∂ν =
      prodConst ν μi * ((∫⁻ x, ‖A x‖ₑ ∂μi) * ∫⁻ y, ‖B y‖ₑ ∂Measure.haar) := by
  set me := (AdelicGLn.prodEquiv K n).toHomeomorph.toMeasurableEquiv
  have h1 : ∫⁻ g, ‖A (archComp K n g) * B (finComp K n g)‖ₑ ∂ν =
      ∫⁻ p, ‖A p.1‖ₑ * ‖B p.2‖ₑ ∂(ν.map me) := by
    rw [lintegral_map_equiv (fun p ↦ ‖A p.1‖ₑ * ‖B p.2‖ₑ) me]
    refine lintegral_congr fun g ↦ ?_
    rw [enorm_mul]
    rfl
  have hme : ν.map me = ν.map (AdelicGLn.prodEquiv K n) := rfl
  rw [h1, hme, map_prodEquiv_eq ν μi, lintegral_smul_measure,
    lintegral_prod_mul hA.enorm.aemeasurable hB.enorm.aemeasurable, ENNReal.smul_def, smul_eq_mul]

end Product

section Finite

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

instance fact_isOpen_integralGL : Fact (∀ v : HeightOneSpectrum (𝓞 K),
    IsOpen (integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K)))) :=
  ⟨fun _ ↦ isOpen_integralGL _ n⟩

instance measurableSpace_finRes : MeasurableSpace (Πʳ v : HeightOneSpectrum (𝓞 K),
    [GL (Fin n) (v.adicCompletion K), (integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K)))]) :=
  _root_.borel _

instance borelSpace_finRes : BorelSpace (Πʳ v : HeightOneSpectrum (𝓞 K),
    [GL (Fin n) (v.adicCompletion K), (integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K)))]) :=
  ⟨rfl⟩

variable (K n) in

def finHaar : Measure (Πʳ v : HeightOneSpectrum (𝓞 K),
    [GL (Fin n) (v.adicCompletion K), (integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K)))]) :=
  (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)).map (AdelicGLn.finiteRestrictedEquiv K n)

instance isHaarMeasure_finHaar : (finHaar K n).IsHaarMeasure := by
  unfold finHaar
  infer_instance

variable (K n) in

def finConst : ℝ :=
  (finHaar K n).real {x | ∀ v, x v ∈ integralGL (v.adicCompletion K) n}

theorem finConst_pos : 0 < finConst K n :=
  RestrictedHaar.measureReal_setOf_forall_mem_pos _ (fun _ ↦ isOpen_integralGL _ n)
    (fun _ ↦ isCompact_integralGL _ n) _

theorem integral_finHaar_eq {B : AdelicGLn.FiniteAdelicGL K n → ℂ}
    (Φ : (Πʳ v : HeightOneSpectrum (𝓞 K),
      [GL (Fin n) (v.adicCompletion K), (integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K)))]) → ℂ)
    (hB : ∀ y, B y = Φ (AdelicGLn.finiteRestrictedEquiv K n y)) :
    ∫ y, B y ∂Measure.haar = ∫ x, Φ x ∂finHaar K n := by
  set me := (AdelicGLn.finiteRestrictedEquiv K n).toHomeomorph.toMeasurableEquiv
  rw [finHaar, show (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)).map
    (AdelicGLn.finiteRestrictedEquiv K n) = (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)).map me from rfl,
    integral_map_equiv me Φ]
  exact integral_congr_ae (Eventually.of_forall fun y ↦ hB y)

theorem integrable_finHaar_iff {B : AdelicGLn.FiniteAdelicGL K n → ℂ}
    (Φ : (Πʳ v : HeightOneSpectrum (𝓞 K),
      [GL (Fin n) (v.adicCompletion K), (integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K)))]) → ℂ)
    (hB : ∀ y, B y = Φ (AdelicGLn.finiteRestrictedEquiv K n y)) :
    Integrable B Measure.haar ↔ Integrable Φ (finHaar K n) := by
  set me := (AdelicGLn.finiteRestrictedEquiv K n).toHomeomorph.toMeasurableEquiv
  rw [finHaar, show (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)).map
    (AdelicGLn.finiteRestrictedEquiv K n) = (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)).map me from rfl,
    integrable_map_equiv me Φ]
  have : B = Φ ∘ me := funext hB
  rw [this]

theorem hasProd_finite (F : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin n) (v.adicCompletion K) → ℂ)
    (hF : ∀ v, Measurable (F v))
    (hF1 : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ∀ k ∈ integralGL (v.adicCompletion K) n, F v k = 1)
    {B : AdelicGLn.FiniteAdelicGL K n → ℂ}
    (hB : ∀ y, B y = ∏ᶠ v, F v (AdelicGLn.finiteRestrictedEquiv K n y v))
    (hint : Integrable B Measure.haar) :
    HasProd (fun v ↦ ∫ h, F v h ∂localHaar n v) ((finConst K n)⁻¹ * ∫ y, B y ∂Measure.haar) := by
  rw [integral_finHaar_eq (fun x ↦ ∏ᶠ v, F v (x v)) hB]
  have hν1 : ∀ v : HeightOneSpectrum (𝓞 K), localHaar n v
      (integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K))) = 1 :=
    fun v ↦ localHaar_integralGL v
  exact RestrictedHaar.hasProd_integral (G := fun v : HeightOneSpectrum (𝓞 K) ↦ GL (Fin n) (v.adicCompletion K))
    (fun v ↦ integralGL (v.adicCompletion K) n)
    (fun v ↦ isOpen_integralGL _ n) (fun v ↦ isCompact_integralGL _ n) (finHaar K n)
    (fun v ↦ localHaar n v) hν1 F hF hF1 (fun x ↦ ∏ᶠ v, F v (x v)) (fun x ↦ rfl)
    ((integrable_finHaar_iff _ hB).1 hint)

theorem integrable_factor_finite (F : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin n) (v.adicCompletion K) → ℂ)
    (hF : ∀ v, Measurable (F v))
    (hF1 : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ∀ k ∈ integralGL (v.adicCompletion K) n, F v k = 1)
    {B : AdelicGLn.FiniteAdelicGL K n → ℂ}
    (hB : ∀ y, B y = ∏ᶠ v, F v (AdelicGLn.finiteRestrictedEquiv K n y v))
    (hint : Integrable B Measure.haar)
    (hne : ∀ v : HeightOneSpectrum (𝓞 K), (¬ ∀ k ∈ integralGL (v.adicCompletion K) n, F v k = 1) → ∫⁻ h, ‖F v h‖ₑ ∂localHaar n v ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) : Integrable (F v) (localHaar n v) := by
  have hν1 : ∀ v : HeightOneSpectrum (𝓞 K), localHaar n v
      (integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K))) = 1 :=
    fun v ↦ localHaar_integralGL v
  exact RestrictedHaar.integrable_factor (G := fun v : HeightOneSpectrum (𝓞 K) ↦ GL (Fin n) (v.adicCompletion K))
    (fun v ↦ integralGL (v.adicCompletion K) n)
    (fun v ↦ isOpen_integralGL _ n) (fun v ↦ isCompact_integralGL _ n) (finHaar K n)
    (fun v ↦ localHaar n v) hν1 F hF hF1 (fun x ↦ ∏ᶠ v, F v (x v)) (fun x ↦ rfl)
    ((integrable_finHaar_iff _ hB).1 hint) hne v

end Finite

section ZetaNonvanishing₂

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
  {V : HeightOneSpectrum (𝓞 K) → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

def localIntegrand (Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ)
    (π : ∀ v, Representation ℂ (GL (Fin n) (v.adicCompletion K)) (V v)) (ξ : ∀ v, V v)
    (ℓ : ∀ v, Module.Dual ℂ (V v)) (s : ℂ) (v : HeightOneSpectrum (𝓞 K))
    (h : GL (Fin n) (v.adicCompletion K)) : ℂ :=
  Φ v (h : Matrix (Fin n) (Fin n) (v.adicCompletion K)) * Parabolic.matrixCoeff (π v) (ξ v) (ℓ v) h *
    detPow h (s + ((n : ℂ) - 1) / 2)

def finIntegrand (Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ)
    (π : ∀ v, Representation ℂ (GL (Fin n) (v.adicCompletion K)) (V v)) (ξ : ∀ v, V v)
    (ℓ : ∀ v, Module.Dual ℂ (V v)) (s : ℂ) (y : AdelicGLn.FiniteAdelicGL K n) : ℂ :=
  ∏ᶠ v, localIntegrand Φ π ξ ℓ s v (AdelicGLn.finiteRestrictedEquiv K n y v)

variable {S : Finset (HeightOneSpectrum (𝓞 K))}
  {Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ}
  {π : ∀ v, Representation ℂ (GL (Fin n) (v.adicCompletion K)) (V v)} {ξ : ∀ v, V v}
  {ℓ : ∀ v, Module.Dual ℂ (V v)}

theorem localIntegrand_eq_one (hS0 : ∀ v ∉ S, Φ v = integralIndicator (v.adicCompletion K) n)
    (hsph : ∀ v ∉ S, ξ v ∈ fixedVectors (π v) (integralGL (v.adicCompletion K) n) ∧ ℓ v (ξ v) = 1)
    (s : ℂ) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) {k : GL (Fin n) (v.adicCompletion K)}
    (hk : k ∈ integralGL (v.adicCompletion K) n) : localIntegrand Φ π ξ ℓ s v k = 1 := by
  rw [localIntegrand, hS0 v hv]
  exact localIntegrand_of_mem_integralGL (π v) (hsph v hv).1 (hsph v hv).2 s hk

theorem continuous_localIntegrand' (hSB : ∀ v ∈ S, IsSchwartzBruhat (Φ v))
    (hS0 : ∀ v ∉ S, Φ v = integralIndicator (v.adicCompletion K) n)
    (hξ : ∀ v, ξ v ∈ smoothVectors (π v)) (s : ℂ) (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (localIntegrand Φ π ξ ℓ s v) := by
  have hΦ : Continuous (Φ v) := by
    by_cases hv : v ∈ S
    · exact (hSB v hv).1.continuous
    · rw [hS0 v hv]
      exact isSchwartzBruhat_integralIndicator.1.continuous
  exact continuous_localIntegrand hΦ (π v) (hξ v) (ℓ v) s

theorem continuous_finIntegrand (hSB : ∀ v ∈ S, IsSchwartzBruhat (Φ v))
    (hS0 : ∀ v ∉ S, Φ v = integralIndicator (v.adicCompletion K) n)
    (hsph : ∀ v ∉ S, ξ v ∈ fixedVectors (π v) (integralGL (v.adicCompletion K) n) ∧ ℓ v (ξ v) = 1)
    (hξ : ∀ v, ξ v ∈ smoothVectors (π v)) (s : ℂ) :
    Continuous (finIntegrand Φ π ξ ℓ s) := by
  refine continuous_iff_continuousAt.2 fun y ↦ ?_
  set e := AdelicGLn.finiteRestrictedEquiv K n
  have hfin : {v : HeightOneSpectrum (𝓞 K) | e y v ∉ integralGL (v.adicCompletion K) n}.Finite :=
    Filter.eventually_cofinite.1 (e y).2
  set T := S ∪ hfin.toFinset with hT
  have hopen : IsOpen (e ⁻¹' (RestrictedHaar.box (fun v ↦ integralGL (v.adicCompletion K) n) T :
      Set (Πʳ v : HeightOneSpectrum (𝓞 K), [GL (Fin n) (v.adicCompletion K),
        (integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K)))]))) :=
    (RestrictedHaar.isOpen_box _ (fun v ↦ isOpen_integralGL _ n) T).preimage e.continuous
  have hy : y ∈ e ⁻¹' (RestrictedHaar.box (fun v ↦ integralGL (v.adicCompletion K) n) T :
      Set (Πʳ v : HeightOneSpectrum (𝓞 K), [GL (Fin n) (v.adicCompletion K),
        (integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K)))])) := by
    intro v hv
    by_contra h
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))
  have heq : ∀ z ∈ e ⁻¹' (RestrictedHaar.box (fun v ↦ integralGL (v.adicCompletion K) n) T :
      Set (Πʳ v : HeightOneSpectrum (𝓞 K), [GL (Fin n) (v.adicCompletion K),
        (integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K)))])),
      finIntegrand Φ π ξ ℓ s z = ∏ v ∈ T, localIntegrand Φ π ξ ℓ s v (e z v) := by
    intro z hz
    refine RestrictedHaar.finprod_eq_prod_of_mem_box
      (G := fun v : HeightOneSpectrum (𝓞 K) ↦ GL (Fin n) (v.adicCompletion K))
      (fun v ↦ integralGL (v.adicCompletion K) n) (F := fun v ↦ localIntegrand Φ π ξ ℓ s v)
      (fun v hv k hk ↦ ?_) hz
    exact localIntegrand_eq_one hS0 hsph s (fun h ↦ hv (Finset.mem_union_left _ h)) hk
  have hc : Continuous fun z : AdelicGLn.FiniteAdelicGL K n ↦ ∏ v ∈ T, localIntegrand Φ π ξ ℓ s v (e z v) :=
    continuous_finsetProd _ fun v _ ↦ (continuous_localIntegrand' hSB hS0 hξ s v).comp
      ((RestrictedProduct.continuous_eval v).comp e.continuous)
  refine hc.continuousAt.congr ?_
  filter_upwards [hopen.mem_nhds hy] with z hz
  exact (heq z hz).symm

theorem zetaIntegrand_eq (φ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ))
    (hS0 : ∀ v ∉ S, Φ v = integralIndicator (v.adicCompletion K) n)
    (hsph : ∀ v ∉ S, ξ v ∈ fixedVectors (π v) (integralGL (v.adicCompletion K) n) ∧ ℓ v (ξ v) = 1)
    {f : AdelicGLn.AdelicGL K n → ℂ} {fi : AdelicGLn.InfiniteAdelicGL K n → ℂ}
    (hf : ∀ g, f g = fi (archComp K n g) *
      ∏ᶠ v, Parabolic.matrixCoeff (π v) (ξ v) (ℓ v) (localComp n v g)) (s : ℂ)
    (g : AdelicGLn.AdelicGL K n) :
    GJGlobal.zetaIntegrand (matrixTensor φ Φ) f s g =
      archIntegrand φ fi s (archComp K n g) * finIntegrand Φ π ξ ℓ s (finComp K n g) := by
  set U := S ∪ (finite_setOf_not_mem g).toFinset with hU
  have hout : ∀ v ∉ U, v ∉ S ∧ localComp n v g ∈ integralGL (v.adicCompletion K) n := by
    intro v hv
    refine ⟨fun h ↦ hv (Finset.mem_union_left _ h), ?_⟩
    by_contra h
    exact hv (Finset.mem_union_right _ ((finite_setOf_not_mem g).mem_toFinset.2 h))
  have h1 : ∏ᶠ v, Φ v (localComp n v g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) =
      ∏ v ∈ U, Φ v (localComp n v g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ by
      by_contra hvU
      obtain ⟨hvS, hvK⟩ := hout v hvU
      apply hv
      dsimp only
      rw [hS0 v hvS, integralIndicator,
        Set.indicator_of_mem (mem_integralMatrixSet.2 ((mem_integralGL_iff _ n).1 hvK).1)]
      rfl
  have h2 : ∏ᶠ v, Parabolic.matrixCoeff (π v) (ξ v) (ℓ v) (localComp n v g) =
      ∏ v ∈ U, Parabolic.matrixCoeff (π v) (ξ v) (ℓ v) (localComp n v g) :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ by
      by_contra hvU
      obtain ⟨hvS, hvK⟩ := hout v hvU
      apply hv
      show (ℓ v) ((π v) (localComp n v g) (ξ v)) = 1
      rw [(hsph v hvS).1 _ hvK, (hsph v hvS).2]
  have h3 : ∏ᶠ v, detPow (localComp n v g) (s + ((n : ℂ) - 1) / 2) =
      ∏ v ∈ U, detPow (localComp n v g) (s + ((n : ℂ) - 1) / 2) :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ by
      by_contra hvU
      exact hv (detPow_of_mem_integralGL (hout v hvU).2 _)
  have h4 : finIntegrand Φ π ξ ℓ s (finComp K n g) = ∏ v ∈ U, localIntegrand Φ π ξ ℓ s v (localComp n v g) :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv ↦ by
      by_contra hvU
      exact hv (localIntegrand_eq_one hS0 hsph s (hout v hvU).1 (hout v hvU).2)
  rw [GJGlobal.zetaIntegrand, matrixTensor_coe, hf g, detPow_eq, h1, h2, h3, h4, archIntegrand]
  simp only [localIntegrand, Finset.prod_mul_distrib]
  ring

end ZetaNonvanishing₂

section Euler

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
  {V : HeightOneSpectrum (𝓞 K) → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
  {S : Finset (HeightOneSpectrum (𝓞 K))}
  {Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ}
  {π : ∀ v, Representation ℂ (GL (Fin n) (v.adicCompletion K)) (V v)} {ξ : ∀ v, V v}
  {ℓ : ∀ v, Module.Dual ℂ (V v)}

theorem continuous_archSchwartz (φ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ)) :
    Continuous fun x : AdelicGLn.InfiniteAdelicGL K n ↦
      archSchwartz φ (x : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) :=
  by
    simp_rw [archSchwartz_eq]
    exact φ.continuous.comp ((archEntries K n).continuous.comp
      (Units.continuous_val : Continuous (Units.val : AdelicGLn.InfiniteAdelicGL K n →
        Matrix (Fin n) (Fin n) (InfiniteAdeleRing K))))

theorem continuous_archIntegrand (φ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ))
    {fi : AdelicGLn.InfiniteAdelicGL K n → ℂ} (hfi : Continuous fi) (s : ℂ) :
    Continuous (archIntegrand φ fi s) :=
  ((continuous_archSchwartz φ).mul hfi).mul (continuous_archDetPow _)

theorem globalZeta_eq_euler (ν : Measure (AdelicGLn.AdelicGL K n)) [ν.IsHaarMeasure]
    (μi : Measure (AdelicGLn.InfiniteAdelicGL K n)) [μi.IsHaarMeasure]
    (φ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ))
    (hSB : ∀ v ∈ S, IsSchwartzBruhat (Φ v))
    (hS0 : ∀ v ∉ S, Φ v = integralIndicator (v.adicCompletion K) n)
    (hξ : ∀ v, ξ v ∈ smoothVectors (π v))
    (hsph : ∀ v ∉ S, ξ v ∈ fixedVectors (π v) (integralGL (v.adicCompletion K) n) ∧ ℓ v (ξ v) = 1)
    {f : AdelicGLn.AdelicGL K n → ℂ} {fi : AdelicGLn.InfiniteAdelicGL K n → ℂ} (hfi : Continuous fi)
    (hf : ∀ g, f g = fi (archComp K n g) *
      ∏ᶠ v, Parabolic.matrixCoeff (π v) (ξ v) (ℓ v) (localComp n v g))
    {s : ℂ} (hint : Integrable (GJGlobal.zetaIntegrand (matrixTensor φ Φ) f s) ν) :
    GJGlobal.globalZeta ν (matrixTensor φ Φ) f s =
        (((prodConst ν μi : ℝ) * finConst K n : ℝ) : ℂ) * archZeta μi φ fi s *
          ∏' v, zetaIntegral (localHaar n v) (Φ v) (Parabolic.matrixCoeff (π v) (ξ v) (ℓ v)) s ∧
      (¬ (archIntegrand φ fi s =ᵐ[μi] 0) →
        Integrable (finIntegrand Φ π ξ ℓ s) Measure.haar ∧
        HasProd (fun v ↦ zetaIntegral (localHaar n v) (Φ v) (Parabolic.matrixCoeff (π v) (ξ v) (ℓ v)) s)
          (∏' v, zetaIntegral (localHaar n v) (Φ v) (Parabolic.matrixCoeff (π v) (ξ v) (ℓ v)) s)) := by
  set A := archIntegrand φ fi s with hAdef
  set B := finIntegrand Φ π ξ ℓ s with hBdef
  have hA : Continuous A := continuous_archIntegrand φ hfi s
  have hB : Continuous B := continuous_finIntegrand hSB hS0 hsph hξ s
  have hH : GJGlobal.zetaIntegrand (matrixTensor φ Φ) f s =
      fun g ↦ A (archComp K n g) * B (finComp K n g) := funext (zetaIntegrand_eq φ hS0 hsph hf s)
  have hZ : GJGlobal.globalZeta ν (matrixTensor φ Φ) f s =
      ((prodConst ν μi : ℝ) : ℂ) * ((∫ x, A x ∂μi) * ∫ y, B y ∂Measure.haar) := by
    rw [GJGlobal.globalZeta, hH]
    exact integral_eq_mul ν μi A B
  have hzA : archZeta μi φ fi s = ∫ x, A x ∂μi := rfl
  by_cases h0 : A =ᵐ[μi] 0
  · have hA0 : ∫ x, A x ∂μi = 0 := by
      rw [integral_congr_ae h0]
      simp
    refine ⟨?_, fun h ↦ absurd h0 h⟩
    rw [hZ, hzA, hA0]
    simp
  · have hBint : Integrable B Measure.haar := by
      have hl := lintegral_eq_mul ν μi hA.measurable hB.measurable
      have hfin : ∫⁻ g, ‖A (archComp K n g) * B (finComp K n g)‖ₑ ∂ν < ⊤ := by
        have := hint.2
        rwa [hH] at this
      rw [hl] at hfin
      have hAne : ∫⁻ x, ‖A x‖ₑ ∂μi ≠ 0 := by
        intro h
        apply h0
        rw [lintegral_eq_zero_iff hA.measurable.enorm] at h
        filter_upwards [h] with x hx
        simpa using hx
      have hc0 : (prodConst ν μi : ℝ≥0∞) ≠ 0 := by exact_mod_cast (prodConst_pos ν μi).ne'
      refine ⟨hB.aestronglyMeasurable, ?_⟩
      have h1 := ENNReal.lt_top_of_mul_ne_top_right hfin.ne hc0
      exact ENNReal.lt_top_of_mul_ne_top_right h1.ne hAne
    have hP := hasProd_finite (fun v ↦ localIntegrand Φ π ξ ℓ s v)
      (fun v ↦ (continuous_localIntegrand' hSB hS0 hξ s v).measurable)
      (by
        filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv k hk
        exact localIntegrand_eq_one hS0 hsph s hv hk)
      (fun y ↦ rfl) hBint
    have hval := hP.tprod_eq
    refine ⟨?_, fun _ ↦ ⟨hBint, hP.multipliable.hasProd⟩⟩
    have hzv : (fun v ↦ zetaIntegral (localHaar n v) (Φ v) (Parabolic.matrixCoeff (π v) (ξ v) (ℓ v)) s) =
        fun v ↦ ∫ h, localIntegrand Φ π ξ ℓ s v h ∂localHaar n v := rfl
    rw [hZ, hzA, hzv, hval]
    have hf0 : (finConst K n : ℂ) ≠ 0 := by exact_mod_cast (finConst_pos (K := K) (n := n)).ne'
    push_cast
    field_simp
    rfl

end Euler

end GJStandardL

end

end GroundTheory.Automorphic
end

section
open MeasureTheory Filter Set Topology IsDedekindDomain NumberField NumberField.mixedEmbedding
open scoped NumberField.AdeleRing RestrictedProduct SchwartzMap Classical ENNReal NNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace GJStandardL

open GodementJacquet GLnLocal

set_option linter.unusedSectionVars false

section Continuity

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem exists_norm_le_of_cusp (hn : 0 < n) {φ : AdelicGLn.AdelicGL K n → ℂ}
    (hφ : φ ∈ AutomorphicForm.cuspForms K n)
    (hA : ∀ (t : {r : ℝ // 0 < r}) (x : AdelicGLn.AdelicGL K n), φ (Reduction.centralSection K n t * x) = φ x) :
    ∃ C : ℝ, ∀ y, ‖φ y‖ ≤ C := by
  obtain ⟨C, hC⟩ := CuspidalSpectrum.exists_norm_le_of_mem_cuspForms hφ
  refine ⟨C, fun y ↦ ?_⟩
  set p := (GJGlobal.splitEquiv (K := K) hn).symm y
  have hy : y = (p.1 : AdelicGLn.AdelicGL K n) * Reduction.centralSection K n p.2 := by
    rw [← GJGlobal.splitEquiv_apply hn p, MeasurableEquiv.apply_symm_apply]
  rw [hy, ← Reduction.centralSection_mul_comm, hA]
  exact hC _ p.1.2

theorem continuous_globalMatrixCoeff (hn : 0 < n) (μ : Measure (Reduction.normOneGL K n)) [μ.IsHaarMeasure]
    {φ₁ φ₂ : AdelicGLn.AdelicGL K n → ℂ} (h₁ : φ₁ ∈ AutomorphicForm.cuspForms K n)
    (h₂ : φ₂ ∈ AutomorphicForm.cuspForms K n)
    (hA : ∀ (t : {r : ℝ // 0 < r}) (x : AdelicGLn.AdelicGL K n), φ₁ (Reduction.centralSection K n t * x) = φ₁ x) :
    Continuous (GJGlobal.matrixCoeff μ φ₁ φ₂) := by
  obtain ⟨C₁, hC₁⟩ := exists_norm_le_of_cusp hn h₁ hA
  obtain ⟨C₂, hC₂⟩ := CuspidalSpectrum.exists_norm_le_of_mem_cuspForms h₂
  have h1c : Continuous φ₁ := h₁.1.continuous
  have h2c : Continuous φ₂ := h₂.1.continuous
  have hfin : μ (RightCosetSpace.fundamentalDomain (Reduction.rationalGLOne K n)) < ⊤ :=
    GJGlobal.measure_fundamentalDomain_rationalGLOne_lt_top μ
  have : IsFiniteMeasure (μ.restrict (RightCosetSpace.fundamentalDomain (Reduction.rationalGLOne K n))) :=
    isFiniteMeasure_restrict.2 hfin.ne
  refine continuous_of_dominated (bound := fun _ ↦ C₁ * C₂) (fun g ↦ ?_) (fun g ↦ ?_)
    (integrable_const _) (Eventually.of_forall fun x ↦ ?_)
  · exact ((h1c.comp (continuous_subtype_val.mul continuous_const)).mul
      (continuous_star.comp (h2c.comp continuous_subtype_val))).aestronglyMeasurable
  · refine Eventually.of_forall fun x ↦ ?_
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hC₁ _) (hC₂ _ x.2) (norm_nonneg _) ((norm_nonneg _).trans (hC₁ 1))
  · exact (h1c.comp (continuous_const.mul continuous_id)).mul continuous_const

end Continuity

theorem hasProd_compl_of_hasProd {ι : Type*} {f : ι → ℂ} {a : ℂ} (h : HasProd f a) (S : Finset ι)
    (hS : ∀ i ∈ S, f i ≠ 0) :
    HasProd (fun i : {i // i ∉ S} ↦ f i) (a / ∏ i ∈ S, f i) := by
  set g : ι → ℂ := (S : Set ι).mulIndicator fun i ↦ (f i)⁻¹ with hg
  have hgp : HasProd g (∏ i ∈ S, (f i)⁻¹) := by
    have : HasProd g (∏ i ∈ S, g i) := hasProd_prod_of_ne_finset_one fun i hi ↦ by
      rw [hg, Set.mulIndicator_of_notMem (by simpa using hi)]
    rwa [Finset.prod_congr rfl fun i hi ↦ by rw [hg, Set.mulIndicator_of_mem (by simpa using hi)]] at this
  have hfg := h.mul hgp
  have heq : (fun i ↦ f i * g i) = ({i | i ∉ S} : Set ι).mulIndicator f := by
    funext i
    by_cases hi : i ∈ S
    · rw [hg, Set.mulIndicator_of_mem (by simpa using hi),
        Set.mulIndicator_of_notMem (by simpa using hi), mul_inv_cancel₀ (hS i hi)]
    · rw [hg, Set.mulIndicator_of_notMem (by simpa using hi),
        Set.mulIndicator_of_mem (by simpa using hi), mul_one]
  rw [heq, Finset.prod_inv_distrib, ← div_eq_mul_inv] at hfg
  exact (hasProd_subtype_iff_mulIndicator (s := {i | i ∉ S})).2 hfg

section Partial

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}


end Partial

section Main

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem detPow_ne_zero' {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (g : GL (Fin n) F) (s : ℂ) : detPow g s ≠ 0 := by
  have hq : (LocalField.residueCard F : ℂ) ≠ 0 := Nat.cast_ne_zero.2 LocalField.residueCard_ne_zero
  rw [detPow_eq_qs_zpow, qs]
  exact zpow_ne_zero _ fun h ↦ hq ((Complex.cpow_eq_zero_iff _ _).1 h).1

theorem archComp_prodEquiv_symm (x : AdelicGLn.InfiniteAdelicGL K n) (y : AdelicGLn.FiniteAdelicGL K n) :
    archComp K n ((AdelicGLn.prodEquiv K n).symm (x, y)) = x := by
  show ((AdelicGLn.prodEquiv K n) ((AdelicGLn.prodEquiv K n).symm (x, y))).1 = x
  rw [ContinuousMulEquiv.apply_symm_apply]

theorem localComp_prodEquiv_symm (v : HeightOneSpectrum (𝓞 K)) (x : AdelicGLn.InfiniteAdelicGL K n)
    (y : AdelicGLn.FiniteAdelicGL K n) :
    localComp n v ((AdelicGLn.prodEquiv K n).symm (x, y)) = AdelicGLn.finiteRestrictedEquiv K n y v := by
  show AdelicGLn.finiteRestrictedEquiv K n
    ((AdelicGLn.prodEquiv K n) ((AdelicGLn.prodEquiv K n).symm (x, y))).2 v = _
  rw [ContinuousMulEquiv.apply_symm_apply]



end Main

end GJStandardL

end

end GroundTheory.Automorphic
end

section
open MeasureTheory Filter Set Topology IsDedekindDomain NumberField NumberField.mixedEmbedding
open scoped NumberField.AdeleRing RestrictedProduct SchwartzMap Classical ENNReal NNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace GJStandardL

open GodementJacquet GLnLocal

theorem hasProd_of_hasProd_compl {ι : Type*} {f : ι → ℂ} {b : ℂ} (S : Finset ι)
    (h : HasProd (fun i : {i // i ∉ S} ↦ f i) b) : HasProd f ((∏ i ∈ S, f i) * b) := by
  have h1 : HasProd ((S : Set ι).mulIndicator f) (∏ i ∈ S, f i) := by
    have : HasProd ((S : Set ι).mulIndicator f) (∏ i ∈ S, (S : Set ι).mulIndicator f i) :=
      hasProd_prod_of_ne_finset_one fun i hi ↦ Set.mulIndicator_of_notMem (by simpa using hi) _
    rwa [Finset.prod_congr rfl fun i hi ↦ Set.mulIndicator_of_mem (by simpa using hi) f] at this
  have h2 : HasProd (({i | i ∉ S} : Set ι).mulIndicator f) b :=
    (hasProd_subtype_iff_mulIndicator (s := {i | i ∉ S})).1 h
  have h3 := h1.mul h2
  have heq : (fun i ↦ (S : Set ι).mulIndicator f i * ({i | i ∉ S} : Set ι).mulIndicator f i) = f := by
    funext i
    by_cases hi : i ∈ S
    · rw [Set.mulIndicator_of_mem (by simpa using hi), Set.mulIndicator_of_notMem (by simpa using hi),
        mul_one]
    · rw [Set.mulIndicator_of_notMem (by simpa using hi), Set.mulIndicator_of_mem (by simpa using hi),
        one_mul]
  rwa [heq] at h3

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem exists_sphericalIntegrable (ν : Measure (AdelicGLn.AdelicGL K n)) [ν.IsHaarMeasure]
    {f : AdelicGLn.AdelicGL K n → ℂ} (hfc : Continuous f)
    (hP : ∀ Ψ ∈ GJMatrix.matrixSchwartzBruhat K n, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (GJGlobal.zetaIntegrand Ψ f s) ν)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {V : HeightOneSpectrum (𝓞 K) → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
    (π : ∀ v, Representation ℂ (GL (Fin n) (v.adicCompletion K)) (V v)) (ξ : ∀ v, V v)
    (ℓ : ∀ v, Module.Dual ℂ (V v)) (hξ : ∀ v, ξ v ∈ smoothVectors (π v))
    (hsph : ∀ v ∉ S, ξ v ∈ fixedVectors (π v) (integralGL (v.adicCompletion K) n) ∧ ℓ v (ξ v) = 1)
    (fi : AdelicGLn.InfiniteAdelicGL K n → ℂ)
    (hf : ∀ g, f g = fi (archComp K n g) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)
        (localComp n v g))
    (hf0 : ∃ g, f g ≠ 0) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      (∀ v ∉ S, Integrable (fun g : GL (Fin n) (v.adicCompletion K) ↦
        integralIndicator (v.adicCompletion K) n (g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) *
          Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) g *
            detPow g (s + ((n : ℂ) - 1) / 2)) (localHaar n v)) ∧
      Multipliable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} ↦
        zetaIntegral (localHaar n (v : HeightOneSpectrum (𝓞 K)))
          (integralIndicator ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) n)
          (Parabolic.matrixCoeff (F := (v : HeightOneSpectrum (𝓞 K)).adicCompletion K) (π v) (ξ v) (ℓ v)) s := by
  obtain ⟨g₀, hg₀⟩ := hf0
  set c₀ := ∏ᶠ v : HeightOneSpectrum (𝓞 K),
    Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) (localComp n v g₀) with hc₀
  have hsupp : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) ↦
      Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) (localComp n v g₀)).Finite := by
    refine ((finite_setOf_not_mem g₀).union S.finite_toSet).subset fun v hv ↦ ?_
    by_contra hc
    simp only [mem_union, Finset.mem_coe, not_or] at hc
    have hK : localComp n v g₀ ∈ integralGL (v.adicCompletion K) n := by
      by_contra h
      exact hc.1 h
    apply hv
    show ℓ v (π v (localComp n v g₀) (ξ v)) = 1
    rw [(hsph v hc.2).1 _ hK, (hsph v hc.2).2]
  rw [hf g₀] at hg₀
  have hfi0 : fi (archComp K n g₀) ≠ 0 := left_ne_zero_of_mul hg₀
  have hc₀0 : c₀ ≠ 0 := right_ne_zero_of_mul hg₀
  have hloc0 : ∀ v : HeightOneSpectrum (𝓞 K),
      Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) (localComp n v g₀) ≠ 0 :=
    fun v h ↦ hc₀0 (finprod_eq_zero _ v h hsupp)
  have hfic : Continuous fi := by
    have key : ∀ x, fi x = f ((AdelicGLn.prodEquiv K n).symm (x, finComp K n g₀)) / c₀ := by
      intro x
      have : f ((AdelicGLn.prodEquiv K n).symm (x, finComp K n g₀)) = fi x * c₀ := by
        rw [hf, archComp_prodEquiv_symm]
        simp_rw [localComp_prodEquiv_symm]
        rfl
      rw [this, mul_div_cancel_right₀ _ hc₀0]
    have hc : Continuous fun x ↦ f ((AdelicGLn.prodEquiv K n).symm (x, finComp K n g₀)) / c₀ :=
      (hfc.comp ((AdelicGLn.prodEquiv K n).symm.continuous.comp
        (continuous_id.prodMk continuous_const))).div_const c₀
    exact hc.congr fun x ↦ (key x).symm
  set μi : Measure (AdelicGLn.InfiniteAdelicGL K n) := Measure.haar
  obtain ⟨φ, -, hφne, -, -⟩ := exists_archBump μi hfic hfi0
  have hbump : ∀ v ∈ S, ∃ Φ : Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ, IsSchwartzBruhat Φ ∧
      ∃ a : ℂ, a ≠ 0 ∧ ∀ s : ℂ,
        Integrable (fun g : GL (Fin n) (v.adicCompletion K) ↦ Φ (g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) *
          Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) g *
            detPow g (s + ((n : ℂ) - 1) / 2)) (localHaar n v) ∧
        ∫⁻ g : GL (Fin n) (v.adicCompletion K), ‖Φ (g : Matrix (Fin n) (Fin n) (v.adicCompletion K)) *
          Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v) g *
            detPow g (s + ((n : ℂ) - 1) / 2)‖ₑ ∂localHaar n v ≠ 0 ∧
        zetaIntegral (localHaar n v) Φ (Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)) s =
          a * detPow (localComp n v g₀) (s + ((n : ℂ) - 1) / 2) :=
    fun v _ ↦ exists_localBump (localHaar n v) (π v) (hξ v) (ℓ v) (hloc0 v)
  choose Φb hΦbSB a ha hΦb using hbump
  set Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ :=
    fun v ↦ if h : v ∈ S then Φb v h else integralIndicator (v.adicCompletion K) n with hΦdef
  have hΦS : ∀ v (hv : v ∈ S), Φ v = Φb v hv := fun v hv ↦ by simp only [hΦdef, dif_pos hv]
  have hSB : ∀ v ∈ S, IsSchwartzBruhat (Φ v) := fun v hv ↦ by rw [hΦS v hv]; exact hΦbSB v hv
  have hS0 : ∀ v ∉ S, Φ v = integralIndicator (v.adicCompletion K) n :=
    fun v hv ↦ by simp only [hΦdef, dif_neg hv]
  obtain ⟨σ₀, hσ₀⟩ := hP _ (matrixTensor_mem φ S Φ hSB hS0)
  refine ⟨σ₀, fun s hs ↦ ?_⟩
  obtain ⟨-, hE2⟩ := globalZeta_eq_euler ν μi φ hSB hS0 hξ hsph hfic hf (hσ₀ s hs)
  have hAne : ¬ (archIntegrand φ fi s =ᵐ[μi] 0) := by
    intro h0
    apply hφne s
    have h0' : (fun x ↦ ‖archIntegrand φ fi s x‖ₑ) =ᵐ[μi] 0 := h0.mono fun x hx ↦ by simp [hx]
    rw [lintegral_congr_ae h0']
    simp
  obtain ⟨hBint, hP'⟩ := hE2 hAne
  have hlocint : ∀ v, Integrable (localIntegrand Φ π ξ ℓ s v) (localHaar n v) :=
    integrable_factor_finite (localIntegrand Φ π ξ ℓ s)
      (fun v ↦ (continuous_localIntegrand' hSB hS0 hξ s v).measurable)
      (by
        filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv k hk
        exact localIntegrand_eq_one hS0 hsph s hv hk)
      (fun y ↦ rfl) hBint (fun v hv ↦ by
        by_cases hvS : v ∈ S
        · have := (hΦb v hvS s).2.1
          simp only [localIntegrand, hΦS v hvS]
          exact this
        · exact absurd (fun k hk ↦ localIntegrand_eq_one hS0 hsph s hvS hk) hv)
  have hram0 : ∀ v ∈ S, zetaIntegral (localHaar n v) (Φ v)
      (Parabolic.matrixCoeff (F := v.adicCompletion K) (π v) (ξ v) (ℓ v)) s ≠ 0 := by
    intro v hv
    rw [hΦS v hv, (hΦb v hv s).2.2]
    exact mul_ne_zero (ha v hv) (detPow_ne_zero' _ _)
  refine ⟨fun v hv ↦ ?_, ?_⟩
  · refine (hlocint v).congr (Eventually.of_forall fun g ↦ ?_)
    simp only [localIntegrand, hS0 v hv]
  · refine (hasProd_compl_of_hasProd hP' S hram0).multipliable.congr fun v ↦ ?_
    rw [hS0 v v.2]

end GJStandardL

end

end GroundTheory.Automorphic
end
