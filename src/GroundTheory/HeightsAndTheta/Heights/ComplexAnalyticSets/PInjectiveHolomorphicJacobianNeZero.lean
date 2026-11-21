import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInjectiveHolomorphicJacobianNeZero
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInjectiveHolomorphicDerivNeZero
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicKernelFibre
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCriticalFlatNotInjective

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Filter Topology

theorem InjectiveHolomorphicDerivNeZero.proof : InjectiveHolomorphicDerivNeZero.Statement := by
  intro D f hD hf hinj a ha hder
  have hDa : D ∈ 𝓝 a := hD.mem_nhds ha
  set g : ℂ → ℂ := fun z ↦ f z - f a with hg
  have hga : AnalyticAt ℂ g a := (hf.analyticAt hDa).sub analyticAt_const

  have hntop : analyticOrderAt g a ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have hev : ∀ᶠ z in 𝓝[≠] a, (g z = 0 ∧ z ∈ D) ∧ z ∈ ({a}ᶜ : Set ℂ) :=
      ((htop.and (hDa : ∀ᶠ z in 𝓝 a, z ∈ D)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    obtain ⟨z, ⟨hz0, hzD⟩, hza⟩ := hev.exists
    exact hza (hinj hzD ha (sub_eq_zero.mp hz0))
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hntop
  obtain ⟨u, hu, hua, hfac⟩ := hga.analyticOrderAt_eq_natCast.mp hn.symm
  simp only [smul_eq_mul] at hfac
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := hfac.self_of_nhds
    simp [hg] at this
    exact hua this.symm
  have hn1 : n ≠ 1 := by
    rintro rfl
    have hd : HasDerivAt (fun z ↦ (z - a) ^ 1 * u z) (u a) a := by
      have := ((hasDerivAt_id' a).sub_const a).mul hu.differentiableAt.hasDerivAt
      simp only [pow_one]
      exact this.congr_deriv (by simp)
    have : deriv g a = u a :=
      (EventuallyEq.deriv_eq (hfac : g =ᶠ[𝓝 a] fun z ↦ (z - a) ^ 1 * u z)).trans hd.deriv
    rw [hg, deriv_sub_const, hder] at this
    exact hua this.symm

  set c : ℂ := u a ^ ((n : ℂ)⁻¹) with hc
  set v : ℂ → ℂ := fun z ↦ c * (u z / u a) ^ ((n : ℂ)⁻¹) with hv
  have hva : AnalyticAt ℂ v a := analyticAt_const.mul
    ((hu.div analyticAt_const hua).cpow analyticAt_const (by simp [hua, Complex.one_mem_slitPlane]))
  have hvpow : ∀ z, v z ^ n = u z := by
    intro z
    rw [hv, mul_pow, hc, Complex.cpow_nat_inv_pow _ hn0, Complex.cpow_nat_inv_pow _ hn0]
    field_simp
  have hv0 : v a ≠ 0 := by
    intro h
    have := hvpow a
    rw [h, zero_pow hn0] at this
    exact hua this.symm
  set w : ℂ → ℂ := fun z ↦ (z - a) * v z with hw
  have hwd : HasDerivAt w (v a) a := by
    have := ((hasDerivAt_id' a).sub_const a).mul hva.differentiableAt.hasDerivAt
    exact this.congr_deriv (by simp)
  have hwa : w a = 0 := by simp [hw]
  have hgw : ∀ z, g z = (z - a) ^ n * u z → g z = w z ^ n := by
    intro z hz
    rw [hz, ← hvpow z, ← mul_pow]

  have hmap : 𝓝 (w a) ≤ map w (𝓝 a) := by
    have hwan : AnalyticAt ℂ w a := (analyticAt_id.sub analyticAt_const).mul hva
    refine hwan.eventually_constant_or_nhds_le_map_nhds.resolve_left ?_
    intro hconst
    have h1 : deriv w a = 0 := by
      rw [EventuallyEq.deriv_eq (hconst : w =ᶠ[𝓝 a] fun _ ↦ w a)]
      simp
    exact hv0 (hwd.deriv.symm.trans h1)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (hmap (image_mem_map (inter_mem hDa hfac)))
  rw [hwa] at hball
  have hk : 1 < n := by omega
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with hζ
  have hprim : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0
  set t : ℂ := ((ε / 2 : ℝ) : ℂ) with ht
  have htn : ‖t‖ = ε / 2 := by rw [ht, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, norm_zero] at htn
    linarith
  obtain ⟨z₁, ⟨hz₁D, hz₁⟩, hw₁⟩ := hball (by
    rw [Metric.mem_ball, dist_zero_right, htn]; linarith)
  obtain ⟨z₂, ⟨hz₂D, hz₂⟩, hw₂⟩ := hball (show ζ * t ∈ Metric.ball 0 ε by
    rw [Metric.mem_ball, dist_zero_right, norm_mul, hprim.norm'_eq_one hn0, htn]; linarith)
  have hg₁ := hgw z₁ hz₁
  have hg₂ := hgw z₂ hz₂
  rw [hw₁] at hg₁
  rw [hw₂, mul_pow, hprim.pow_eq_one, one_mul] at hg₂
  have hf12 : f z₁ = f z₂ := by
    have : g z₁ = g z₂ := hg₁.trans hg₂.symm
    simpa [hg] using this
  have h12 := hinj hz₁D hz₂D hf12
  rw [h12, hw₂] at hw₁
  have : (ζ - 1) * t = 0 := by rw [sub_mul, one_mul, hw₁, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact hprim.ne_one hk (sub_eq_zero.mp h)
  · exact ht0 h

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

namespace InjectiveHolomorphicJacobianNeZero

theorem det_fin_one (A : (Fin 1 → ℂ) →ₗ[ℂ] Fin 1 → ℂ) : LinearMap.det A = A 1 0 := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Fin 1)), Matrix.det_unique, LinearMap.toMatrix_apply]
  simp only [Pi.basisFun_apply, Pi.basisFun_repr]
  have h1 : (Pi.single (default : Fin 1) (1 : ℂ) : Fin 1 → ℂ) = 1 := by
    funext i
    fin_cases i
    rfl
  rw [h1]
  rfl

theorem one {U : Set (Fin 1 → ℂ)} {f : (Fin 1 → ℂ) → Fin 1 → ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U) {x : Fin 1 → ℂ} (hx : x ∈ U) :
    LinearMap.det (fderiv ℂ f x : (Fin 1 → ℂ) →ₗ[ℂ] Fin 1 → ℂ) ≠ 0 := by
  set e : (Fin 1 → ℂ) ≃L[ℂ] ℂ := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ with he
  set φ : ℂ → ℂ := fun z => e (f (e.symm z)) with hφ
  have hD : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
  have hφd : DifferentiableOn ℂ φ (e.symm ⁻¹' U) :=
    e.differentiable.comp_differentiableOn (hf.comp e.symm.differentiable.differentiableOn fun _ h => h)
  have hφi : Set.InjOn φ (e.symm ⁻¹' U) := fun s hs t ht h =>
    e.symm.injective (hinj hs ht (e.injective h))
  have hxD : e x ∈ e.symm ⁻¹' U := by simpa using hx
  have hne := InjectiveHolomorphicDerivNeZero.proof _ φ hD hφd hφi (e x) hxD
  have hfx : HasFDerivAt f (fderiv ℂ f x) x := (hf.differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hφx : HasFDerivAt φ ((e : (Fin 1 → ℂ) →L[ℂ] ℂ).comp ((fderiv ℂ f x).comp
      (e.symm : ℂ →L[ℂ] Fin 1 → ℂ))) (e x) := by
    have h1 : HasFDerivAt f (fderiv ℂ f x) (e.symm (e x)) := by simpa using hfx
    exact e.hasFDerivAt.comp (e x) (h1.comp (e x) e.symm.hasFDerivAt)
  rw [hφx.hasDerivAt.deriv] at hne
  rw [det_fin_one]
  simpa [he] using hne

end InjectiveHolomorphicJacobianNeZero

theorem InjectiveHolomorphicJacobianNeZero.proof (hF : HolomorphicKernelFibre.Statement)
    (hC : CriticalFlatNotInjective.Statement) : InjectiveHolomorphicJacobianNeZero.Statement := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro U f hU hf hinj x hx hdet
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · rw [LinearMap.det_eq_one_of_subsingleton] at hdet
      exact one_ne_zero hdet
    · exact InjectiveHolomorphicJacobianNeZero.one hU hf hinj hx hdet
  · by_cases hall : ∀ b ∈ U, LinearMap.det (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) = 0 →
        fderiv ℂ f b = 0
    · exact hC k U f x hk hU hf hx hdet hall hinj
    push Not at hall
    obtain ⟨b, hb, hdb, hne⟩ := hall
    set d := Module.finrank ℂ (LinearMap.ker (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)) with hd
    have hd0 : 0 < d := by
      rw [hd, Module.finrank_pos_iff_exists_ne_zero]
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
        (LinearMap.bot_lt_ker_of_det_eq_zero hdb).ne'
      exact ⟨⟨v, hv⟩, by simpa using hv0⟩
    have hdk : d < k := by
      have hker : LinearMap.ker (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) ≠ ⊤ := by
        rw [Ne, LinearMap.ker_eq_top]
        intro h0
        exact hne (ContinuousLinearMap.coe_injective (by simpa using h0))
      simpa [Module.finrank_fin_fun] using Submodule.finrank_lt hker
    obtain ⟨V, y, γ, ℓ, hV, hy, hγ, hmaps, hγinj, hfib, hzero⟩ := hF k U f b hU hf hb d rfl
    have hhd : DifferentiableOn ℂ (fun t => ℓ (f (γ t))) V :=
      ℓ.differentiable.comp_differentiableOn (hf.comp hγ hmaps)
    have hhinj : Set.InjOn (fun t => ℓ (f (γ t))) V := fun s hs t ht h =>
      hγinj hs ht (hinj (hmaps hs) (hmaps ht) (hfib s hs t ht h))
    apply ih d hdk V _ hV hhd hhinj y hy
    rw [hzero, ContinuousLinearMap.toLinearMap_zero, LinearMap.det_zero, Module.finrank_fin_fun]
    exact zero_pow hd0.ne'

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
