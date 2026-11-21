import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSystemRegularityProperties
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConeTangentLiftInChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftB

section
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Cusp
open GroundTheory.Heights₂.Heights.LowerBoundFree (torusSmul)
open ReciprocityTheory.AnForm

namespace RootFieldNumerics.Levi

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem tangent_decomp (Ω : Type) [Field Ω] [Algebra ℚ Ω] (y : (Σ k, J k) → Ω) (e : ℕ)
    (hP : IsArithVar (mCoordIdeal y) (e + 1)) (hsm : SmoothGenericFibreM y)
    (γ : (Fin e → ℂ) → (Σ k, J k) → ℂ) (t : Fin e → ℂ) (hγ : AnalyticAt ℂ γ t)
    (hpts : ∀ᶠ t' in 𝓝 t, γ t' ∈ mcPts (mCoordIdeal y))
    (himm : ∀ u c, fderiv ℂ γ t u = torusSmul c (γ t) → u = 0) (v : (Σ k, J k) → ℂ)
    (hv : IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal y) (γ t) v) :
    ∃ (u : Fin e → ℂ) (c : K → ℂ), v = fderiv ℂ γ t u + torusSmul c (γ t) := by
  classical
  have hz := hpts.self_of_nhds
  have hdim := finrank_tanSub_pC_le Ω y _ hP hsm hz
  have hzI : ∀ f ∈ pC (mCoordIdeal y), eval (γ t) f = 0 := by
    have h := hz
    rw [mcPts_eq_pC] at h
    exact h.2
  have hPh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) :=
    isMultiHomogIdeal_pC hP.2.1.2.1
  have hcone : ∀ x, IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal y) (γ t) x →
      x ∈ tanSub (pC (mCoordIdeal y)) (γ t) := by
    intro x hx f hf
    have hle : pC (mCoordIdeal y) ≤ tanIdeal (γ t) x := by
      rw [pC, Ideal.span_le]
      rintro _ ⟨g, hg, rfl⟩
      exact ⟨hz.2 g hg, hx g hg⟩
    exact (hle hf).2
  let L₁ : (Fin e → ℂ) →ₗ[ℂ] (Σ k, J k) → ℂ := (fderiv ℂ γ t).toLinearMap
  let L₂ : (K → ℂ) →ₗ[ℂ] (Σ k, J k) → ℂ :=
    { toFun := fun c => torusSmul c (γ t)
      map_add' := fun c c' => by funext q; simp only [torusSmul, Pi.add_apply]; ring
      map_smul' := fun r c => by
        funext q; simp only [torusSmul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  let L := L₁.coprod L₂
  have hL : ∀ u c, L (u, c) = fderiv ℂ γ t u + torusSmul c (γ t) := fun _ _ => rfl
  have hrange : LinearMap.range L ≤ tanSub (pC (mCoordIdeal y)) (γ t) := by
    rintro _ ⟨⟨u, c⟩, rfl⟩
    rw [hL]
    refine Submodule.add_mem _ (hcone _ ?_) fun f hf => (le_tanIdeal_torusSmul hPh hzI c hf).2
    exact GroundTheory.Heights₂.Heights.HilbertSamuel.G1.isConeTangent_of_sheet le_rfl hγ hpts u
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨u, c⟩ h
    rw [hL] at h
    have hu : u = 0 := himm u (fun k => -c k) (by
      funext q
      have h1 := congrFun h q
      simp only [torusSmul, Pi.add_apply, Pi.zero_apply] at h1 ⊢
      linear_combination h1)
    subst hu
    have h2 : torusSmul c (γ t) = 0 := by simpa using h
    have hc : c = 0 := by
      funext k
      obtain ⟨i, hi⟩ := hz.1 k
      have h3 : c k * γ t ⟨k, i⟩ = 0 := congrFun h2 ⟨k, i⟩
      exact (mul_eq_zero.mp h3).resolve_right hi
    rw [hc]
    rfl
  have hfr : Module.finrank ℂ (LinearMap.range L) = e + Fintype.card K := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have heq := Submodule.eq_of_le_of_finrank_le hrange (by rw [hfr]; exact hdim)
  have hvr : v ∈ LinearMap.range L := heq ▸ hcone v hv
  obtain ⟨⟨u, c⟩, huc⟩ := hvr
  exact ⟨u, c, huc.symm⟩

theorem differentiableAt_affCoord (p : (k : K) → J k) (z : (Σ k, J k) → ℂ) (hp : ∀ k, z ⟨k, p k⟩ ≠ 0) :
    DifferentiableAt ℂ (affCoord p) z := by
  refine differentiableAt_pi.2 fun q => ?_
  have h1 : AnalyticAt ℂ (fun v : (Σ k, J k) → ℂ => v q) z :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) q).analyticAt z
  have h2 : AnalyticAt ℂ (fun v : (Σ k, J k) → ℂ => v ⟨q.1, p q.1⟩) z :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) ⟨q.1, p q.1⟩).analyticAt z
  exact (h1.div h2 (hp q.1)).differentiableAt

theorem affCoord_torus (p : (k : K) → J k) (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, J k) → ℂ) :
    affCoord p (torusSmul c z) = affCoord p z := by
  funext q
  simp only [affCoord, torusSmul]
  exact mul_div_mul_left _ _ (hc q.1)

theorem fderiv_affCoord_torus (p : (k : K) → J k) (z : (Σ k, J k) → ℂ) (hp : ∀ k, z ⟨k, p k⟩ ≠ 0) (b : K → ℂ) :
    fderiv ℂ (affCoord p) z (torusSmul b z) = 0 := by
  have h1 : HasDerivAt (fun s : ℂ => torusSmul (fun k => Complex.exp (s * b k)) z) (torusSmul b z) 0 := by
    refine hasDerivAt_pi.2 fun q => ?_
    have := (((hasDerivAt_id (0 : ℂ)).mul_const (b q.1)).cexp).mul_const (z q)
    simpa [torusSmul] using this
  have h0 : torusSmul (fun k => Complex.exp ((0 : ℂ) * b k)) z = z := by
    funext q; simp [torusSmul]
  have h2 : HasFDerivAt (affCoord p) (fderiv ℂ (affCoord p) z)
      (torusSmul (fun k => Complex.exp ((0 : ℂ) * b k)) z) := by
    rw [h0]; exact (differentiableAt_affCoord p z hp).hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℂ) h1
  have h4 : (affCoord p ∘ fun s : ℂ => torusSmul (fun k => Complex.exp (s * b k)) z) = fun _ => affCoord p z := by
    funext s
    exact affCoord_torus p _ (fun k => Complex.exp_ne_zero _) z
  rw [h4] at h3
  exact h3.unique (hasDerivAt_const _ _)

theorem levi_torus {e : ℕ} (φ : ((Σ k, J k) → ℂ) → ℝ) (d : K → ℝ)
    (hhom : ∀ (c : K → ℂ) (z : (Σ k, J k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      φ (torusSmul c z) = ∑ k, d k * Real.log ‖c k‖ + φ z)
    (γ : (Fin e → ℂ) → (Σ k, J k) → ℂ) (t : Fin e → ℂ) (hγ : AnalyticAt ℂ γ t)
    (hpts : ∀ᶠ t' in 𝓝 t, ∀ k, ∃ i, γ t' ⟨k, i⟩ ≠ 0) (hφ : ContDiffAt ℝ 2 φ (γ t)) (u : Fin e → ℂ) (b : K → ℂ) :
    levi φ (γ t) (fderiv ℂ γ t u + torusSmul b (γ t)) = levi (φ ∘ γ) t u := by
  let ℓ : (Unit → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj ()
  let lin : (Unit → ℂ) → Fin e → ℂ := fun s => t + ℓ s • u
  have hlin : HasFDerivAt lin (ℓ.smulRight u) 0 := by
    have := (ℓ.smulRight u).hasFDerivAt (x := 0)
    exact this.const_add t
  have hlinA : AnalyticAt ℂ lin 0 := analyticAt_const.add ((ℓ.smulRight u).analyticAt 0)
  have hl0 : lin 0 = t := by simp [lin]
  have hγ' : AnalyticAt ℂ γ (lin 0) := by rw [hl0]; exact hγ
  let Γ : (Unit → ℂ) → (Σ k, J k) → ℂ := fun s => torusSmul (fun k => Complex.exp (ℓ s * b k)) (γ (lin s))
  have hΓ0 : Γ 0 = γ t := by
    funext q; simp [Γ, torusSmul, hl0]
  have hγl : AnalyticAt ℂ (γ ∘ lin) 0 := hγ'.comp hlinA
  have hΓA : AnalyticAt ℂ Γ 0 := by
    refine analyticAt_pi_iff.2 fun q => ?_
    exact (((ℓ.analyticAt 0).mul analyticAt_const).cexp').mul (analyticAt_pi_iff.1 hγl q)
  have hΓd : fderiv ℂ Γ 0 (fun _ => 1) = fderiv ℂ γ t u + torusSmul b (γ t) := by
    have hg : HasFDerivAt (γ ∘ lin) ((fderiv ℂ γ t).comp (ℓ.smulRight u)) 0 := by
      have h1 : HasFDerivAt γ (fderiv ℂ γ t) (lin 0) := by rw [hl0]; exact hγ.differentiableAt.hasFDerivAt
      exact h1.comp 0 hlin
    funext q
    have h1 := (hasFDerivAt_pi'.1 hΓA.differentiableAt.hasFDerivAt q)
    have h2 := (((ℓ.hasFDerivAt (x := 0)).mul_const (b q.1)).cexp).mul (hasFDerivAt_pi'.1 hg q)
    have h3 := congrArg (fun L => L (fun _ => 1)) (h1.unique h2)
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.proj_apply] at h3
    rw [h3]
    simp [ℓ, hl0, torusSmul]
    ring
  have hφγ : ContDiffAt ℝ 2 (φ ∘ γ) t := hφ.comp t (hγ.restrictScalars (𝕜 := ℝ)).contDiffAt
  have e1 := levi_comp (φ := φ) (τ := Γ) (z := 0) (fun _ => 1) hΓA (by rw [hΓ0]; exact hφ)
  rw [hΓ0, hΓd] at e1
  have e2 := levi_comp (φ := φ ∘ γ) (τ := lin) (z := 0) (fun _ => 1) hlinA (by rw [hl0]; exact hφγ)
  rw [hl0, hlin.fderiv] at e2
  have e3 : (ℓ.smulRight u) (fun _ => 1) = u := by simp [ℓ]
  rw [e3] at e2
  rw [← e1, ← e2]
  let G : (Unit → ℂ) → ℂ := fun s => ∑ k, (d k : ℂ) * (ℓ s * b k)
  have hG : AnalyticAt ℂ G 0 :=
    Finset.analyticAt_fun_sum _ fun k _ => analyticAt_const.mul ((ℓ.analyticAt 0).mul analyticAt_const)
  have hev : φ ∘ Γ =ᶠ[𝓝 0] fun s => ((φ ∘ γ) ∘ lin) s + 1 * (G s).re := by
    have ht : Tendsto lin (𝓝 0) (𝓝 t) := by rw [← hl0]; exact hlinA.continuousAt
    filter_upwards [ht.eventually hpts] with s hs
    simp only [Function.comp_apply, Γ]
    rw [hhom _ _ (fun k => Complex.exp_ne_zero _) hs, add_comm, one_mul]
    congr 1
    simp only [G, Complex.re_sum, Complex.re_ofReal_mul, Complex.norm_exp, Real.log_exp]
  have hc1 : ContDiffAt ℝ 2 ((φ ∘ γ) ∘ lin) 0 :=
    ContDiffAt.comp 0 (by rw [hl0]; exact hφγ) (hlinA.restrictScalars (𝕜 := ℝ)).contDiffAt
  have hc2 : ContDiffAt ℝ 2 (fun s => (G s).re) 0 :=
    Complex.reCLM.contDiff.contDiffAt.comp 0 (hG.restrictScalars (𝕜 := ℝ)).contDiffAt
  rw [levi_congr hev, levi_add_smul 1 hc1 hc2, levi_re_analytic hG]
  simp

theorem levi_nonneg (Ω : Type) [Field Ω] [Algebra ℚ Ω] (y : (Σ k, J k) → Ω) (e : ℕ)
    (hP : IsArithVar (mCoordIdeal y) (e + 1)) (hsm : SmoothGenericFibreM y) {B : Ideal (MRing J)} (hB : B = ⊤)
    (R : AnLogRes (mCoordIdeal y) B e) (φ : ((Σ k, J k) → ℂ) → ℝ) (d : K → ℝ)
    (hhom : ∀ (c : K → ℂ) (z : (Σ k, J k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      φ (torusSmul c z) = ∑ k, d k * Real.log ‖c k‖ + φ z)
    (hφ : ∀ z : (Σ k, J k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ContDiffAt ℝ 2 φ z)
    (hpsh : ∀ x j, x ∈ (R.A.chart j).source → ∀ u,
      0 ≤ levi (fun t => φ (R.lift x ((R.A.chart j).symm t))) (R.A.chart j x) u)
    (z : (Σ k, J k) → ℂ) (hz : z ∈ mcPts (mCoordIdeal y)) (w : (Σ k, J k) → ℂ)
    (hw : IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal y) z w) : 0 ≤ leviForm φ z w := by
  classical
  have hno : ∀ z : (Σ k, J k) → ℂ, z ∉ mcPts B := fun z hz => by
    subst hB
    simpa using hz.2 1 Submodule.mem_top
  obtain ⟨x, c, hc, hx⟩ := R.surj z hz (hno z)
  obtain ⟨j, hj⟩ := R.A.cover x
  let γ₀ : (Fin e → ℂ) → (Σ k, J k) → ℂ := fun t => R.lift x ((R.A.chart j).symm t)
  let γ : (Fin e → ℂ) → (Σ k, J k) → ℂ := fun t => torusSmul (fun k => (c k)⁻¹) (γ₀ t)
  have hci : ∀ k, (c k)⁻¹ ≠ 0 := fun k => inv_ne_zero (hc k)
  have hsx : (R.A.chart j).symm (R.A.chart j x) = x := (R.A.chart j).left_inv hj
  have hmemO : R.A.chart j x ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, hsx]; exact R.mem_U x⟩
  have hO := ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds hmemO
  have hγ₀A : AnalyticAt ℂ γ₀ (R.A.chart j x) := analyticAt_pi_iff.2 fun q => R.holo x q j _ hmemO
  have hγA : AnalyticAt ℂ γ (R.A.chart j x) :=
    analyticAt_pi_iff.2 fun q => analyticAt_const.mul (analyticAt_pi_iff.1 hγ₀A q)
  have hγz : γ (R.A.chart j x) = z := by
    funext q
    simp only [γ, γ₀, torusSmul, hsx, hx]
    rw [← mul_assoc, inv_mul_cancel₀ (hc _), one_mul]
  have h0pts : ∀ᶠ t in 𝓝 (R.A.chart j x), γ₀ t ∈ mcPts (mCoordIdeal y) := by
    filter_upwards [hO] with t ht using R.mem x _ ht.2
  have hpts : ∀ᶠ t in 𝓝 (R.A.chart j x), γ t ∈ mcPts (mCoordIdeal y) := by
    filter_upwards [h0pts] with t ht
    exact mcPts_smul hP.2.1.2.1 _ hci ht
  choose p hp using hz.1
  have himm : ∀ u b, fderiv ℂ γ (R.A.chart j x) u = torusSmul b (γ (R.A.chart j x)) → u = 0 := by
    intro u b hub
    have hp' : ∀ k, R.lift x x ⟨k, p k⟩ ≠ 0 := fun k => by
      rw [hx]; exact mul_ne_zero (hc k) (hp k)
    have hk := R.immersion x (hno _) p hp' j hj
    have hfun : (fun t => affCoord p (R.lift x ((R.A.chart j).symm t))) = affCoord p ∘ γ := by
      funext t
      exact (affCoord_torus p _ hci _).symm
    rw [hfun, fderiv_comp _ (by rw [hγz]; exact differentiableAt_affCoord p z hp) hγA.differentiableAt] at hk
    have : u ∈ (⊥ : Submodule ℂ (Fin e → ℂ)) := by
      rw [← hk]
      show fderiv ℂ (affCoord p) (γ (R.A.chart j x)) (fderiv ℂ γ (R.A.chart j x) u) = 0
      rw [hub, hγz]
      exact fderiv_affCoord_torus p z hp b
    exact this
  obtain ⟨u, b, hub⟩ := tangent_decomp Ω y e hP hsm γ _ hγA hpts himm w (by rw [hγz]; exact hw)
  have h1 := levi_torus φ d hhom γ _ hγA (hpts.mono fun t ht => ht.1) (by rw [hγz]; exact hφ z hz.1) u b
  rw [← hub, hγz] at h1
  show 0 ≤ levi φ z w
  rw [h1]
  have hev : φ ∘ γ =ᶠ[𝓝 (R.A.chart j x)] fun t => φ (γ₀ t) +
      1 * ((fun _ : Fin e → ℂ => ((∑ k, d k * Real.log ‖(c k)⁻¹‖ : ℝ) : ℂ)) t).re := by
    filter_upwards [h0pts] with t ht
    simp only [Function.comp_apply, γ]
    rw [hhom _ _ hci ht.1, Complex.ofReal_re, one_mul, add_comm]
  have hc1 : ContDiffAt ℝ 2 (fun t => φ (γ₀ t)) (R.A.chart j x) :=
    (hφ _ h0pts.self_of_nhds.1).comp _ (hγ₀A.restrictScalars (𝕜 := ℝ)).contDiffAt
  rw [levi_congr hev, levi_add_smul 1 hc1 contDiffAt_const, levi_re_analytic analyticAt_const]
  simpa using hpsh x j hj u

end RootFieldNumerics.Levi
end
end

section
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.LowerBoundFree (torusSmul)

namespace RootFieldNumerics.Levi

theorem telescope (g : ℕ → ℝ) (k n : ℕ) (h : k ≤ n) :
    ∑ i ∈ Finset.range n, (if k ≤ i then g i - g (i + 1) else 0) = g k - g n := by
  induction n, h using Nat.le_induction with
  | base =>
    rw [sub_self]
    refine Finset.sum_eq_zero fun i hi => if_neg ?_
    have := Finset.mem_range.1 hi
    omega
  | succ n hn ih => rw [Finset.sum_range_succ, ih, if_pos hn]; ring

private theorem sum_gap_of_le_eq {Ψ : Type} {N : ℕ} (lam : Ψ × Fin N → ℝ) (ψ : Ψ) (j : Fin N) :
    ∑ k : Fin N, (if j ≤ k then PB.gap lam (ψ, k) else 0) = lam (ψ, j) := by
  set g : ℕ → ℝ := fun i => if h : i < N then lam (ψ, ⟨i, h⟩) else 0 with hgdef
  have hg : ∀ k : Fin N, PB.gap lam (ψ, k) = g k - g (k + 1) := by
    intro k
    simp only [PB.gap, PB.gapX, map_sub, eval_X, hgdef, dif_pos k.2]
    split_ifs with h
    · simp
    · simp
  calc ∑ k : Fin N, (if j ≤ k then PB.gap lam (ψ, k) else 0)
      = ∑ k : Fin N, (fun i : ℕ => if (j : ℕ) ≤ i then g i - g (i + 1) else 0) k := by
        apply Finset.sum_congr rfl
        intro k _
        simp only [Fin.le_iff_val_le_val, hg]
    _ = ∑ i ∈ Finset.range N, (if (j : ℕ) ≤ i then g i - g (i + 1) else 0) :=
        Fin.sum_univ_eq_sum_range (fun i : ℕ => if (j : ℕ) ≤ i then g i - g (i + 1) else 0) N
    _ = g j - g N := telescope g j N j.2.le
    _ = lam (ψ, j) := by simp [hgdef]

theorem sum_gap_mul {Ψ : Type} [Fintype Ψ] {N : ℕ} (lam f : Ψ × Fin N → ℝ) :
    ∑ p, PB.gap lam p * ∑ k ∈ Finset.Iic p.2, f (p.1, k) = ∑ p, lam p * f p := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ψ _
  have hI : ∀ k : Fin N, ∑ j ∈ Finset.Iic k, f (ψ, j) = ∑ j : Fin N, if j ≤ k then f (ψ, j) else 0 := by
    intro k
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext j
      simp
    · intro j _
      rfl
  simp only [hI, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← sum_gap_of_le_eq lam ψ j, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem log_h_torus (L : HermLine ι) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (L.h (torusSmul c z)) = ∑ k, (L.a k : ℝ) * Real.log ‖c k‖ + Real.log (L.h z) := by
  have hsm : L.h (torusSmul c z) = (∏ k, ‖c k‖ ^ L.a k) * L.h z := L.smul c z hc
  have hpos : 0 < L.h z := L.pos z hz
  have hprod : ∀ k ∈ (Finset.univ : Finset K), ‖c k‖ ^ L.a k ≠ 0 := by
    intro k _
    exact zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
  rw [hsm, Real.log_mul (Finset.prod_ne_zero_iff.mpr hprod) hpos.ne', Real.log_prod hprod]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [Real.log_zpow]

theorem contDiffAt_log_h {L : HermLine ι} (hL : IsSmoothHerm L) (z : (Σ k, ι k) → ℂ)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ContDiffAt ℝ 2 (fun z => Real.log (L.h z)) z := by
  have hopen : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    have hset : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} =
        ⋂ k, ⋃ i, {z : (Σ k, ι k) → ℂ | z ⟨k, i⟩ ≠ 0} := by
      ext w
      simp
    rw [hset]
    apply isOpen_iInter_of_finite
    intro k
    apply isOpen_iUnion
    intro i
    exact isOpen_ne_fun (continuous_apply _) continuous_const
  have hh : ContDiffAt ℝ 2 L.h z := by
    have h1 := hL.contDiffAt (hopen.mem_nhds hz)
    exact h1.of_le (WithTop.coe_le_coe.mpr le_top)
  exact hh.log (L.pos z hz).ne'

theorem log_line_lift {D : ℕ} {σ : Type} {S : PB.AnSys D σ} {P : Ideal (MRing ι)} (Re : PB.Realis S P) (a : σ) (t : ℝ)
    (ht : 0 < t) (ht' : t ≤ S.t₀) (x y : Re.R.X) (hy : y ∈ Re.R.U x) :
    Real.log ((Re.line a t).h (Re.R.lift x y)) = Real.log ((Re.ref a).h (Re.R.lift x y)) + S.phT a t (Re.π y) := by
  obtain ⟨c, hc, h⟩ := Re.R.compat x y y ⟨hy, Re.R.mem_U y⟩
  have hz := (Re.R.mem y y (Re.R.mem_U y)).1
  change Re.R.lift x y = torusSmul c _ at h
  rw [h, log_h_torus _ c _ hc hz, log_h_torus _ c _ hc hz, Re.line_eq a t ht ht', Re.line_deg]
  ring

theorem levi_chart_nonneg {D : ℕ} {σ : Type} [Fintype σ] {S : PB.AnSys D σ} {P : Ideal (MRing ι)} (Re : PB.Realis S P)
    (t : ℝ) (ht : 0 < t) (ht' : t ≤ S.t₀) (c : σ → ℝ) (hpsh : IsPsh S.A (PB.sumPot c fun a => S.potT a t))
    (x : Re.R.X) (F : Re.R.X → ℝ)
    (hF : ∀ y ∈ Re.R.U x, F y = ∑ a, c a * (Real.log ((Re.ref a).h (Re.R.lift x y)) + S.phT a t (Re.π y)))
    (j : Fin Re.R.A.n) (hj : x ∈ (Re.R.A.chart j).source) (u : Fin D → ℂ) :
    0 ≤ levi (fun v => F ((Re.R.A.chart j).symm v)) (Re.R.A.chart j x) u := by
  set χ := Re.R.A.chart j with hχ
  have hv0 : χ x ∈ χ.target := χ.map_source hj
  have hχx : χ.symm (χ x) = x := χ.left_inv hj
  obtain ⟨k, hk⟩ := S.A.cover (Re.π x)
  set ψ := S.A.chart k with hψ
  set Φ : S.X → ℝ := (PB.sumPot c fun a => S.potT a t).φ (Re.π x) with hΦd
  have hΦ : ∀ w, Φ w = ∑ a, c a * ((S.th a).φ (Re.π x) w + S.phT a t w) := fun w => rfl
  set τ : (Fin D → ℂ) → (Fin D → ℂ) := fun v => ψ (Re.π (χ.symm v)) with hτd
  have hτv0 : τ (χ x) = ψ (Re.π x) := by simp only [hτd, hχx]
  have hτ : AnalyticAt ℂ τ (χ x) := by
    apply Re.holo.2 j k
    refine ⟨hv0, ?_⟩
    show Re.π (χ.symm (χ x)) ∈ ψ.source
    rw [hχx]
    exact hk
  have hψx : ψ (Re.π x) ∈ ψ.target := ψ.map_source hk
  have hψxl : ψ.symm (ψ (Re.π x)) = Re.π x := ψ.left_inv hk
  have hΦsm : ContDiffAt ℝ 2 (Φ ∘ ψ.symm) (ψ (Re.π x)) := by
    have hfun : Φ ∘ ψ.symm = fun v => ∑ a, c a * ((S.th a).φ (Re.π x) (ψ.symm v) + S.phT a t (ψ.symm v)) := by
      funext v
      exact hΦ _
    rw [hfun]
    apply ContDiffAt.sum
    intro a _
    apply ContDiffAt.mul contDiffAt_const
    apply ContDiffAt.add
    · have h1 := (S.sing a).1.1 (Re.π x) k
      have hmem : ψ.target ∩ ψ.symm ⁻¹' (S.th a).U (Re.π x) ∈ 𝓝 (ψ (Re.π x)) := by
        apply (ψ.isOpen_inter_preimage_symm ((S.th a).isOpen_U _)).mem_nhds
        refine ⟨hψx, ?_⟩
        rw [Set.mem_preimage, hψxl]
        exact (S.th a).mem_U _
      exact (h1.contDiffAt hmem).of_le (WithTop.coe_le_coe.mpr le_top)
    · have h1 := ((S.reg a).2.2 t ht ht').1 k
      have hmem : ψ.target ∩ ψ.symm ⁻¹' Set.univ ∈ 𝓝 (ψ (Re.π x)) := by
        rw [Set.preimage_univ, Set.inter_univ]
        exact ψ.open_target.mem_nhds hψx
      exact (h1.contDiffAt hmem).of_le (WithTop.coe_le_coe.mpr le_top)
  choose V hVo hxV G hG hGeq using fun a => Re.ref_pot a x (Set.mem_univ _)
  set Gs : Re.R.X → ℂ := fun y => ∑ a, (c a : ℂ) * G a y with hGsum
  have hGsan : AnalyticAt ℂ (Gs ∘ χ.symm) (χ x) := by
    have hfun : Gs ∘ χ.symm = fun v => ∑ a, (c a : ℂ) * (G a ∘ χ.symm) v := by
      funext v
      rfl
    have hfun2 : (fun v => ∑ a, (c a : ℂ) * (G a ∘ χ.symm) v) =
        ∑ a, (fun v => (c a : ℂ) * (G a ∘ χ.symm) v) := by
      funext v
      simp [Finset.sum_apply]
    rw [hfun, hfun2]
    apply Finset.analyticAt_sum
    intro a _
    apply analyticAt_const.mul
    apply hG a j
    refine ⟨hv0, ?_⟩
    show χ.symm (χ x) ∈ V a
    rw [hχx]
    exact hxV a
  have hcont : ContinuousAt χ.symm (χ x) := χ.continuousAt_symm hv0
  have hev1 : ∀ᶠ v in 𝓝 (χ x), χ.symm v ∈ Re.R.U x := by
    apply hcont.preimage_mem_nhds
    rw [hχx]
    exact (Re.R.isOpen_U x).mem_nhds (Re.R.mem_U x)
  have hev2 : ∀ᶠ v in 𝓝 (χ x), ∀ a, χ.symm v ∈ V a := by
    rw [Filter.eventually_all]
    intro a
    apply hcont.preimage_mem_nhds
    rw [hχx]
    exact (hVo a).mem_nhds (hxV a)
  have hev3 : ∀ᶠ v in 𝓝 (χ x), Re.π (χ.symm v) ∈ ψ.source := by
    apply (Re.holo.1.continuousAt.comp hcont).preimage_mem_nhds
    show ψ.source ∈ 𝓝 (Re.π (χ.symm (χ x)))
    rw [hχx]
    exact ψ.open_source.mem_nhds hk
  have heq : (fun v => F (χ.symm v)) =ᶠ[𝓝 (χ x)]
      (fun v => ((Φ ∘ ψ.symm) ∘ τ) v + 1 * ((Gs ∘ χ.symm) v).re) := by
    filter_upwards [hev1, hev2, hev3] with v h1 h2 h3
    have hl : ψ.symm (ψ (Re.π (χ.symm v))) = Re.π (χ.symm v) := ψ.left_inv h3
    simp only [Function.comp_apply, hτd, hl, hΦ, hGsum, one_mul, Complex.re_sum, Complex.re_ofReal_mul]
    rw [hF _ h1, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    have h := hGeq a (χ.symm v) (h2 a)
    have h' : Real.log ((Re.ref a).h (Re.R.lift x (χ.symm v))) - (S.th a).φ (Re.π x) (Re.π (χ.symm v)) =
        (G a (χ.symm v)).re := h
    rw [show Real.log ((Re.ref a).h (Re.R.lift x (χ.symm v))) =
        (S.th a).φ (Re.π x) (Re.π (χ.symm v)) + (G a (χ.symm v)).re by linarith]
    ring
  have hC1 : ContDiffAt ℝ 2 ((Φ ∘ ψ.symm) ∘ τ) (χ x) := by
    apply ContDiffAt.comp (χ x) (by rw [hτv0]; exact hΦsm)
    exact hτ.contDiffAt.restrict_scalars ℝ
  have hC2 : ContDiffAt ℝ 2 (fun v => ((Gs ∘ χ.symm) v).re) (χ x) :=
    Complex.reCLM.contDiff.contDiffAt.comp (χ x) (hGsan.contDiffAt.restrict_scalars ℝ)
  have hmemP : ψ (Re.π x) ∈ ψ.target ∩ ψ.symm ⁻¹' (PB.sumPot c fun a => S.potT a t).U (Re.π x) := by
    refine ⟨hψx, ?_⟩
    rw [Set.mem_preimage, hψxl]
    exact (PB.sumPot c fun a => S.potT a t).mem_U _
  have hnn := hpsh (Re.π x) k (ψ (Re.π x)) hmemP ((fderiv ℂ τ (χ x)) u)
  rw [levi_congr heq u, levi_add_smul 1 hC1 hC2 u, levi_comp u hτ (by rw [hτv0]; exact hΦsm),
    levi_re_analytic hGsan u, hτv0]
  simpa using hnn

end RootFieldNumerics.Levi
end
end

section
noncomputable section

namespace RootFieldNumerics.A1

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M Filter Topology GlobalTheory.CompanionTheory.Ar.PB
open scoped ContDiff

variable {e : ℕ} {X : Type} [TopologicalSpace X]

def dl (A : FinHolAtlas e X) (P : LocPot X) (j : Fin A.n) (y w : Fin e → ℂ) : ℝ :=
  levi (P.φ ((A.chart j).symm y) ∘ (A.chart j).symm) y w

theorem c2 {A : FinHolAtlas e X} {P : LocPot X} (hP : IsPotential A P) (x : X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (hx : (A.chart j).symm y ∈ P.U x) :
    ContDiffAt ℝ 2 (P.φ x ∘ (A.chart j).symm) y :=
  (contDiffAt_of_isPotential A P hP x j ⟨hy, hx⟩).of_le two_le_infty

theorem levi_base {A : FinHolAtlas e X} {P : LocPot X} (hP : IsPotential A P) (x : X) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (hx : (A.chart j).symm y ∈ P.U x) (w : Fin e → ℂ) :
    levi (P.φ x ∘ (A.chart j).symm) y w = dl A P j y w := by
  set c := A.chart j with hc
  set p := c.symm y with hp
  obtain ⟨W, hWo, hqW, G, hG, hGeq⟩ := hP.2 x p p ⟨hx, P.mem_U p⟩
  have hGa : AnalyticAt ℂ (G ∘ c.symm) y := hG j y ⟨hy, hqW⟩
  have hRe : ContDiffAt ℝ 2 (fun z => ((G ∘ c.symm) z).re) y := by
    have := (Complex.reCLM.contDiff (n := 2)).contDiffAt.comp y
      (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt
    simpa [Function.comp_def] using this
  have hbase : P.φ x ∘ c.symm =ᶠ[𝓝 y]
      fun z => (P.φ p ∘ c.symm) z + 1 * ((G ∘ c.symm) z).re := by
    have hopen : IsOpen (W ∩ P.U x ∩ P.U p) := (hWo.inter (P.isOpen_U x)).inter (P.isOpen_U p)
    have : ∀ᶠ z in 𝓝 y, c.symm z ∈ W ∩ P.U x ∩ P.U p :=
      (c.continuousAt_symm hy).preimage_mem_nhds (hopen.mem_nhds ⟨⟨hqW, hx⟩, P.mem_U p⟩)
    filter_upwards [this] with z hz
    have := hGeq (c.symm z) hz
    simp only [Function.comp_apply, one_mul]
    linarith
  rw [levi_congr hbase, levi_add_smul 1 (c2 hP p j hy (P.mem_U p)) hRe, levi_re_analytic hGa]
  simp only [dl, mul_zero, add_zero]
  rfl

theorem isPsh_iff {A : FinHolAtlas e X} {P : LocPot X} (hP : IsPotential A P) :
    IsPsh A P ↔ ∀ j, ∀ y ∈ (A.chart j).target, ∀ w, 0 ≤ dl A P j y w := by
  refine ⟨fun h j y hy w => h _ j y ⟨hy, P.mem_U _⟩ w, fun h x j y hy w => ?_⟩
  rw [levi_base hP x j hy.1 hy.2]
  exact h j y hy.1 w

theorem dl_nonneg {A : FinHolAtlas e X} {P : LocPot X} (h : IsPsh A P) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (w : Fin e → ℂ) : 0 ≤ dl A P j y w :=
  h _ j y ⟨hy, P.mem_U _⟩ w

theorem dl_nonneg_of_pos {A : FinHolAtlas e X} {P : LocPot X} (h : IsPosPot A P) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (w : Fin e → ℂ) : 0 ≤ dl A P j y w := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [dl, levi_zero]
  · exact (h _ j y ⟨hy, P.mem_U _⟩ w hw).le

theorem dl_add_rsmul {A : FinHolAtlas e X} {P Q : LocPot X} (hP : IsPotential A P) (hQ : IsPotential A Q)
    (c : ℝ) (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (w : Fin e → ℂ) :
    dl A (P + Q.rsmul c) j y w = dl A P j y w + c * dl A Q j y w :=
  levi_add_smul c (c2 hP _ j hy (P.mem_U _)) (c2 hQ _ j hy (Q.mem_U _)) w

theorem levi_const {ι : Type} [Fintype ι] (a : ℝ) (z w : ι → ℂ) : levi (fun _ => a) z w = 0 := by
  simp [levi]

theorem dl_rsmul {A : FinHolAtlas e X} {Q : LocPot X} (hQ : IsPotential A Q)
    (c : ℝ) (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (w : Fin e → ℂ) :
    dl A (Q.rsmul c) j y w = c * dl A Q j y w := by
  have h := levi_add_smul (f := fun _ => (0 : ℝ)) c contDiffAt_const (c2 hQ _ j hy (Q.mem_U _)) w
  rw [levi_const] at h
  simp only [zero_add] at h
  exact h

theorem levi_sum {ι σ : Type} [Fintype ι] (s : Finset σ) (c : σ → ℝ) (f : σ → (ι → ℂ) → ℝ) {z : ι → ℂ}
    (hf : ∀ a, ContDiffAt ℝ 2 (f a) z) (w : ι → ℂ) :
    levi (fun y => ∑ a ∈ s, c a * f a y) z w = ∑ a ∈ s, c a * levi (f a) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [levi_const]
  | insert a s ha ih =>
    have h1 : ContDiffAt ℝ 2 (fun y => ∑ a ∈ s, c a * f a y) z :=
      ContDiffAt.sum fun a _ => contDiffAt_const.mul (hf a)
    have h := levi_add_smul (c a) h1 (hf a) w
    simp only [Finset.sum_insert ha]
    rw [← ih, add_comm (c a * _), ← h]
    simp only [add_comm]

theorem dl_sumPot {A : FinHolAtlas e X} {σ : Type} [Fintype σ] (c : σ → ℝ) {P : σ → LocPot X}
    (hP : ∀ a, IsPotential A (P a)) (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target)
    (w : Fin e → ℂ) : dl A (sumPot c P) j y w = ∑ a, c a * dl A (P a) j y w :=
  levi_sum Finset.univ c (fun a => (P a).φ ((A.chart j).symm y) ∘ (A.chart j).symm)
    (fun a => c2 (hP a) _ j hy ((P a).mem_U _)) w

theorem isPotential_sumPot {A : FinHolAtlas e X} {σ : Type} [Fintype σ] (c : σ → ℝ) {P : σ → LocPot X}
    (hP : ∀ a, IsPotential A (P a)) : IsPotential A (sumPot c P) := by
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · have : ContDiffOn ℝ ∞ (fun z => ∑ a, c a * ((P a).φ x ∘ (A.chart j).symm) z)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (sumPot c P).U x) :=
      ContDiffOn.sum fun a _ => contDiffOn_const.mul
        (((hP a).1 x j).mono fun z hz => ⟨hz.1, Set.mem_iInter.1 hz.2 a⟩)
    exact this
  · have h := fun a => (hP a).2 x x' y ⟨Set.mem_iInter.1 hy.1 a, Set.mem_iInter.1 hy.2 a⟩
    choose W hWo hyW G hG hGe using h
    refine ⟨⋂ a, W a, isOpen_iInter_of_finite hWo, Set.mem_iInter.2 hyW, fun z => ∑ a, (c a : ℂ) * G a z,
      fun j z hz => ?_, fun z hz => ?_⟩
    · have : AnalyticAt ℂ (fun z => ∑ a, (c a : ℂ) * (G a ∘ (A.chart j).symm) z) z :=
        Finset.analyticAt_fun_sum _ fun a _ =>
          analyticAt_const.mul (hG a j z ⟨hz.1, Set.mem_iInter.1 hz.2 a⟩)
      exact this
    · simp only [sumPot, Complex.re_sum, Complex.re_ofReal_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← hGe a z ⟨⟨Set.mem_iInter.1 hz.1.1 a, Set.mem_iInter.1 hz.1.2 a⟩, Set.mem_iInter.1 hz.2 a⟩]
      ring

theorem dl_chart {A : FinHolAtlas e X} {P : LocPot X} (hP : IsPotential A P) (j k : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart k).target) (hq : (A.chart k).symm y ∈ (A.chart j).source) (v : Fin e → ℂ) :
    dl A P k y v = dl A P j (A.chart j ((A.chart k).symm y))
      (fderiv ℂ (A.chart j ∘ (A.chart k).symm) y v) := by
  set q := (A.chart k).symm y with hqd
  set c := A.chart j with hc
  have hcqt : c q ∈ c.target := c.map_source hq
  have hsc : c.symm (c q) = q := c.left_inv hq
  set τ := c ∘ (A.chart k).symm with hτd
  have hτ : AnalyticAt ℂ τ y := A.holo k j y ⟨hy, hq⟩
  have hτy : τ y = c q := rfl
  have hgerm : P.φ q ∘ (A.chart k).symm =ᶠ[𝓝 y] (P.φ q ∘ c.symm) ∘ τ := by
    have : ∀ᶠ y' in 𝓝 y, (A.chart k).symm y' ∈ c.source :=
      ((A.chart k).continuousAt_symm hy).preimage_mem_nhds (c.open_source.mem_nhds hq)
    filter_upwards [this] with y' hy'
    simp only [Function.comp_apply, τ, c.left_inv hy']
  have hU : c.symm (c q) ∈ P.U q := by rw [hsc]; exact P.mem_U q
  have h2 := c2 hP q j hcqt hU
  change levi (P.φ q ∘ (A.chart k).symm) y v = _
  rw [levi_congr hgerm, levi_comp v hτ (by rw [hτy]; exact h2), hτy]
  exact levi_base hP q j hcqt hU _

theorem compare_local {A : FinHolAtlas e X} {Ω Q : LocPot X} (hΩ : IsPotential A Ω)
    (hpos : IsPosPot A Ω) (hQ : IsPotential A Q) (p : X) (j : Fin A.n)
    (hp : p ∈ (A.chart j).source) :
    ∃ r > 0, ∃ m : ℝ, ∀ y ∈ Metric.ball (A.chart j p) r, y ∈ (A.chart j).target → ∀ u : Fin e → ℂ,
        dl A Q j y u ≤ m * dl A Ω j y u := by
  set c := A.chart j with hc
  set O := c.target ∩ c.symm ⁻¹' (Ω.U p ∩ Q.U p) with hO
  have hOo : IsOpen O :=
    c.continuousOn_symm.isOpen_inter_preimage c.open_target ((Ω.isOpen_U p).inter (Q.isOpen_U p))
  have hpO : c p ∈ O := ⟨c.map_source hp, by
    simp only [Set.mem_preimage, c.left_inv hp]; exact ⟨Ω.mem_U p, Q.mem_U p⟩⟩
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 hOo _ hpO
  have hcb : Metric.closedBall (c p) (r / 2) ⊆ O :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrO
  have hΩs : ContDiffOn ℝ 2 (Ω.φ p ∘ c.symm) O :=
    ((hΩ.1 p j).mono (fun y hy => ⟨hy.1, hy.2.1⟩)).of_le two_le_infty
  have hws : ContDiffOn ℝ 2 (Q.φ p ∘ c.symm) O :=
    ((hQ.1 p j).mono (fun y hy => ⟨hy.1, hy.2.2⟩)).of_le two_le_infty
  set K := Metric.closedBall (c p) (r / 2) ×ˢ Metric.sphere (0 : Fin e → ℂ) 1 with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hKO : K ⊆ O ×ˢ Set.univ := Set.prod_mono hcb (Set.subset_univ _)
  have hpos' : ∀ q ∈ K, 0 < levi (Ω.φ p ∘ c.symm) q.1 q.2 := by
    rintro ⟨y, u⟩ ⟨hy, hu⟩
    refine hpos p j y ⟨(hcb hy).1, (hcb hy).2.1⟩ u ?_
    rintro rfl
    simp at hu
  have hcont : ContinuousOn (fun q : (Fin e → ℂ) × (Fin e → ℂ) =>
      levi (Q.φ p ∘ c.symm) q.1 q.2 / levi (Ω.φ p ∘ c.symm) q.1 q.2) K :=
    ((continuousOn_levi hOo hws).mono hKO).div ((continuousOn_levi hOo hΩs).mono hKO)
      (fun q hq => (hpos' q hq).ne')
  obtain ⟨m, hm⟩ := hKc.bddAbove_image hcont
  refine ⟨r / 2, by linarith, m, fun y hy' hyt u => ?_⟩
  have hy := Metric.ball_subset_closedBall hy'
  rw [← levi_base hΩ p j hyt (hcb hy).2.1, ← levi_base hQ p j hyt (hcb hy).2.2]
  rcases eq_or_ne u 0 with rfl | hu
  · simp [levi_zero]
  · have hn : 0 < ‖u‖ := norm_pos_iff.2 hu
    obtain ⟨v, hv'⟩ : ∃ v : Fin e → ℂ, v = ‖u‖⁻¹ • u := ⟨_, rfl⟩
    have hv : v ∈ Metric.sphere (0 : Fin e → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, hv', norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have hq : (y, v) ∈ K := ⟨hy, hv⟩
    have h1 : levi (Q.φ p ∘ c.symm) y v / levi (Ω.φ p ∘ c.symm) y v ≤ m := hm ⟨(y, v), hq, rfl⟩
    have h2 := hpos' _ hq
    have h3 : levi (Q.φ p ∘ c.symm) y v ≤ m * levi (Ω.φ p ∘ c.symm) y v := by
      rwa [div_le_iff₀ h2] at h1
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ‖u‖ := ⟨_, rfl⟩
    have huv : u = s • v := by
      rw [hs, hv', smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    rw [huv, levi_smul_dir, levi_smul_dir]
    have : 0 ≤ s ^ 2 := by positivity
    nlinarith

theorem compare_global [CompactSpace X] {A : FinHolAtlas e X} {Ω Q : LocPot X} (hΩ : IsPotential A Ω)
    (hpos : IsPosPot A Ω) (hQ : IsPotential A Q) :
    ∃ c₀ > (0 : ℝ), ∀ k, ∀ y ∈ (A.chart k).target, ∀ v, c₀ * dl A Q k y v ≤ dl A Ω k y v := by
  classical
  have hsrc : ∀ p, p ∈ (A.chart (chartIdx A p)).source := fun p => Classical.choose_spec (A.cover p)
  have key := fun p => compare_local hΩ hpos hQ p (chartIdx A p) (hsrc p)
  choose r hr m hbd using key
  let V : X → Set X := fun p => (A.chart (chartIdx A p)).source ∩
    (A.chart (chartIdx A p)) ⁻¹' Metric.ball (A.chart (chartIdx A p) p) (r p)
  have hVo : ∀ p, IsOpen (V p) := fun p =>
    (A.chart _).continuousOn.isOpen_inter_preimage (A.chart _).open_source Metric.isOpen_ball
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hVo
    (fun p _ => Set.mem_iUnion.2 ⟨p, hsrc p, Metric.mem_ball_self (hr p)⟩)
  have hC0 : 0 ≤ ∑ p ∈ t, |m p| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨(1 + ∑ p ∈ t, |m p|)⁻¹, by positivity, fun k y hy v => ?_⟩
  obtain ⟨p, hpt, hqV⟩ : ∃ p ∈ t, (A.chart k).symm y ∈ V p := by
    simpa using ht (Set.mem_univ ((A.chart k).symm y))
  rw [dl_chart hΩ _ k hy hqV.1, dl_chart hQ _ k hy hqV.1]
  have ht' := (A.chart _).map_source hqV.1
  have hb := hbd p _ hqV.2 ht' (fderiv ℂ (A.chart (chartIdx A p) ∘ (A.chart k).symm) y v)
  have h0 := dl_nonneg_of_pos hpos _ ht' (fderiv ℂ (A.chart (chartIdx A p) ∘ (A.chart k).symm) y v)
  have hCm : m p ≤ ∑ p ∈ t, |m p| :=
    (le_abs_self (m p)).trans (Finset.single_le_sum (fun i _ => abs_nonneg (m i)) hpt)
  rw [inv_mul_le_iff₀ (by positivity)]
  nlinarith

end RootFieldNumerics.A1
end
end

section
noncomputable section

namespace RootFieldNumerics.A1

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology GlobalTheory.CompanionTheory.Ar.PB

theorem scale_le {s : ℝ} (hs : 0 < s) (h1 : s ≤ 1) : Real.exp (-(s ^ 2)⁻¹) ≤ s := by
  have h := Real.one_sub_inv_le_log_of_pos hs
  have hu : 0 < s⁻¹ := inv_pos.2 hs
  have e : (s ^ 2)⁻¹ = s⁻¹ ^ 2 := by rw [inv_pow]
  have hl : -(s ^ 2)⁻¹ ≤ Real.log s := by
    rw [e]
    nlinarith [sq_nonneg (s⁻¹ - 1 / 2)]
  calc Real.exp (-(s ^ 2)⁻¹) ≤ Real.exp (Real.log s) := Real.exp_le_exp.2 hl
    _ = s := Real.exp_log hs

theorem epsT_scale (C : ℝ) {s : ℝ} (hs : 0 < s) :
    epsT C (Real.exp (-(s ^ 2)⁻¹)) = -(2 * C) * (s * Real.log s) * s := by
  have h1 : Real.log (1 / Real.exp (-(s ^ 2)⁻¹)) = (s ^ 2)⁻¹ := by
    rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  have h2 : Real.log ((s ^ 2)⁻¹) = -(2 * Real.log s) := by
    rw [Real.log_inv, Real.log_pow]
    push_cast
    ring
  unfold epsT
  rw [h1, h2]
  have hs2 : s ^ 2 ≠ 0 := by positivity
  field_simp

theorem epsT_small (C ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ > (0 : ℝ), ∀ s, 0 < s → s ≤ s₀ → |epsT C (Real.exp (-(s ^ 2)⁻¹))| ≤ ε * s := by
  have hc : ContinuousAt (fun x : ℝ => -(2 * C) * (x * Real.log x)) 0 :=
    (continuous_const.mul Real.continuous_mul_log).continuousAt
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 hc ε hε
  refine ⟨δ / 2, by positivity, fun s hs hsδ => ?_⟩
  have := h (x := s) (by rw [Real.dist_eq, sub_zero, abs_of_pos hs]; linarith)
  simp only [Real.dist_eq, zero_mul, mul_zero, sub_zero] at this
  rw [epsT_scale C hs, abs_mul, abs_of_pos hs]
  exact mul_le_mul_of_nonneg_right this.le hs.le

theorem potT_potential {e : ℕ} {σ : Type} (S : AnSys e σ) (a : σ) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ S.t₀) :
    IsPotential S.A (S.potT a t) :=
  isPotentialAdd _ _ _ (S.sing a).1 (isPotential_ofFun _ _ ((S.reg a).2.2 t h0 h1).1)

theorem psh_sum_potentials_small_parameter : ∀ (e : ℕ) (σ : Type) [Fintype σ] (S : AnSys e σ) (Fl : Set σ) (a' : σ) (c₀ abelian₂ : ℝ), 0 < c₀ → (∀ a ∈ Fl, ∀ t, IsPsh S.A ((S.potT a t).rsmul (-1)) ∧ IsPsh S.A (S.potT a t)) → (∀ t, IsPsh S.A (S.potT a' t + S.Θ.rsmul (-c₀))) → a' ∉ Fl → ∃ s₀ > (0 : ℝ), ∀ s, 0 < s → s ≤ s₀ → Real.exp (-(s ^ 2)⁻¹) ≤ S.t₀ ∧ ∀ c : σ → ℝ, c a' = s → ∑ a, |c a| ≤ abelian₂ → (∀ a ∉ Fl, 0 ≤ c a) → IsPsh S.A (sumPot c (fun a => S.potT a (Real.exp (-(s ^ 2)⁻¹))) + S.Θ.rsmul (-(s * c₀ / 2))) := by
  classical
  intro e σ _ S Fl a' c₀ abelian₂ hc₀ hFl ha' hna'
  have ht0 : 0 < S.t₀ := (S.reg a').1
  have hεp : 0 < c₀ / (2 * (|abelian₂| + 1)) := by positivity
  obtain ⟨s₁, hs₁, heps⟩ := epsT_small S.C (c₀ / (2 * (|abelian₂| + 1))) hεp
  refine ⟨min s₁ (min 1 S.t₀), lt_min hs₁ (lt_min one_pos ht0), fun s hs hss => ?_⟩
  have hs1 : s ≤ 1 := le_trans hss (le_trans (min_le_right _ _) (min_le_left _ _))
  have hst : s ≤ S.t₀ := le_trans hss (le_trans (min_le_right _ _) (min_le_right _ _))
  have hss₁ : s ≤ s₁ := le_trans hss (min_le_left _ _)
  have htt : Real.exp (-(s ^ 2)⁻¹) ≤ S.t₀ := (scale_le hs hs1).trans hst
  refine ⟨htt, fun c hca' hsum hpos => ?_⟩
  set t := Real.exp (-(s ^ 2)⁻¹) with ht
  have htp : 0 < t := Real.exp_pos _
  have hpot : ∀ a, IsPotential S.A (S.potT a t) := fun a => potT_potential S a htp htt
  have hE : |epsT S.C t| ≤ c₀ / (2 * (|abelian₂| + 1)) * s := heps s hs hss₁
  rw [isPsh_iff (isPotentialAdd S.A _ _ (isPotential_sumPot c hpot)
    (isPotentialRsmul S.A _ S.Θ S.potΘ))]
  intro j y hy w
  rw [dl_add_rsmul (isPotential_sumPot c hpot) S.potΘ _ j hy w, dl_sumPot c hpot j hy w]
  have hθ : 0 ≤ dl S.A S.Θ j y w := dl_nonneg_of_pos S.posΘ j hy w
  set θ := dl S.A S.Θ j y w with hθdef
  set E := |epsT S.C t| with hEdef
  have hE0 : 0 ≤ E := abs_nonneg _
  have hterm : ∀ a, -(|c a| * E * θ) ≤ c a * dl S.A (S.potT a t) j y w := by
    intro a
    by_cases hF : a ∈ Fl
    · have hp := hFl a hF t
      have n1 := dl_nonneg hp.1 j hy w
      rw [dl_rsmul (hpot a) (-1) j hy w] at n1
      have n2 := dl_nonneg hp.2 j hy w
      have hz : dl S.A (S.potT a t) j y w = 0 := by linarith
      rw [hz, mul_zero]
      have := mul_nonneg (mul_nonneg (abs_nonneg (c a)) hE0) hθ
      linarith
    · have hca : 0 ≤ c a := hpos a hF
      have hr : IsPsh S.A (S.potT a t + LocPot.rsmul (epsT S.C t) S.Θ) :=
        ((S.reg a).2.2 t htp htt).2.2.2.2.1
      have n1 := dl_nonneg hr j hy w
      rw [dl_add_rsmul (hpot a) S.potΘ _ j hy w] at n1
      have n3 : epsT S.C t * θ ≤ E * θ := mul_le_mul_of_nonneg_right (le_abs_self _) hθ
      have n4 : -(E * θ) ≤ dl S.A (S.potT a t) j y w := by linarith
      rw [abs_of_nonneg hca]
      have := mul_le_mul_of_nonneg_left n4 hca
      linarith
  have ha'l : c₀ * θ ≤ dl S.A (S.potT a' t) j y w := by
    have n1 := dl_nonneg (ha' t) j hy w
    rw [dl_add_rsmul (hpot a') S.potΘ _ j hy w] at n1
    linarith
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a')]
  have hrest : -(∑ a, |c a|) * E * θ ≤
      ∑ a ∈ Finset.univ.erase a', c a * dl S.A (S.potT a t) j y w := by
    calc -(∑ a, |c a|) * E * θ = -(∑ a, |c a| * E * θ) := by
          rw [neg_mul, neg_mul, Finset.sum_mul, Finset.sum_mul]
      _ ≤ -(∑ a ∈ Finset.univ.erase a', |c a| * E * θ) := by
          refine neg_le_neg (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_)
          intro a _ _
          exact mul_nonneg (mul_nonneg (abs_nonneg _) hE0) hθ
      _ = ∑ a ∈ Finset.univ.erase a', -(|c a| * E * θ) := by rw [Finset.sum_neg_distrib]
      _ ≤ _ := Finset.sum_le_sum fun a _ => hterm a
  have hA : c a' * dl S.A (S.potT a' t) j y w ≥ s * (c₀ * θ) := by
    rw [hca']
    exact mul_le_mul_of_nonneg_left ha'l hs.le
  have hLE : (∑ a, |c a|) * E ≤ s * c₀ / 2 := by
    have hL0 : 0 ≤ ∑ a, |c a| := Finset.sum_nonneg fun a _ => abs_nonneg _
    have h1 : (∑ a, |c a|) * E ≤ |abelian₂| * (c₀ / (2 * (|abelian₂| + 1)) * s) :=
      mul_le_mul (hsum.trans (le_abs_self _)) hE hE0 (abs_nonneg _)
    have h2 : |abelian₂| * (c₀ / (2 * (|abelian₂| + 1)) * s) ≤ s * c₀ / 2 := by
      have hL1 : 0 < |abelian₂| + 1 := by positivity
      rw [show |abelian₂| * (c₀ / (2 * (|abelian₂| + 1)) * s) = (s * c₀ / 2) * (|abelian₂| / (|abelian₂| + 1)) by
        field_simp]
      have hq : |abelian₂| / (|abelian₂| + 1) ≤ 1 := by
        rw [div_le_one hL1]; linarith
      have : 0 ≤ s * c₀ / 2 := by positivity
      nlinarith
    linarith
  have hfin : 0 ≤ ((s * c₀ / 2) - (∑ a, |c a|) * E) * θ := mul_nonneg (by linarith) hθ
  nlinarith

end RootFieldNumerics.A1
end
end

section
noncomputable section

namespace RootFieldNumerics.A1

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem gap_eq (lam : Ψ × Fin N → ℝ) (p : Ψ × Fin N) :
    PB.gap lam p = lam p - if h : (p.2 : ℕ) + 1 < N then lam (p.1, ⟨(p.2 : ℕ) + 1, h⟩) else 0 := by
  unfold PB.gap PB.gapX
  split_ifs <;> simp

theorem abs_le_l1_norm (lam : Wt Ψ N) (τ : Ψ) (i : Fin N) : |lam τ i| ≤ l1 lam := by
  unfold l1
  calc |lam τ i| ≤ ∑ j : Fin N, |lam τ j| :=
        Finset.single_le_sum (f := fun j => |lam τ j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    _ ≤ ∑ σ : Ψ, ∑ j : Fin N, |lam σ j| :=
        Finset.single_le_sum (f := fun σ => ∑ j : Fin N, |lam σ j|)
          (fun σ _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ τ)

theorem abs_gap_le (mu : Wt Ψ N) (b : ℝ) (hb : ∀ τ i, |mu τ i| ≤ b) (p : Ψ × Fin N) :
    |PB.gap (fun x => mu x.1 x.2) p| ≤ 2 * b := by
  rw [gap_eq]
  have h0 : 0 ≤ b := le_trans (abs_nonneg _) (hb p.1 p.2)
  refine le_trans (abs_sub _ _) ?_
  have h1 : |mu p.1 p.2| ≤ b := hb p.1 p.2
  split_ifs with h
  · have h2 := hb p.1 ⟨(p.2 : ℕ) + 1, h⟩
    simp only at h1 h2 ⊢
    linarith
  · simp only [abs_zero] at h1 ⊢
    linarith

theorem comp_psh {D : ℕ} (S : PB.AnSys D (Option (Ψ × Fin N))) (k : ℕ) (hk : 0 < k) (b : ℝ)
    (h0 : ∀ t x, S.phT none t x = 0)
    (hfl : ∀ τ (i : Fin N), (i : ℕ) + 1 = N → ∀ t, IsPsh S.A ((S.potT (some (τ, i)) t).rsmul (-1)) ∧
      IsPsh S.A (S.potT (some (τ, i)) t))
    (hpos : IsPosPot S.A (S.th none)) :
    ∃ s₀ > (0 : ℝ), ∀ s, 0 < s → s ≤ s₀ → scale s ≤ S.t₀ ∧ ∀ mu : Wt Ψ N, (∀ τ i, |mu τ i| ≤ b) → Dominant mu →
      IsPsh S.A (PB.sumPot (PB.gapS (fun x => mu x.1 x.2) (s / k)) fun a => S.potT a (scale s)) := by
  have hth : IsPotential S.A (S.th none) := (S.sing none).1
  obtain ⟨c₀, hc₀, hcmp⟩ := compare_global hth hpos S.potΘ
  have hpotb : IsPotential S.A (S.th none + LocPot.rsmul (-c₀) S.Θ) :=
    isPotentialAdd S.A _ _ hth (isPotentialRsmul S.A (-c₀) S.Θ S.potΘ)
  have hbase : IsPsh S.A (S.th none + LocPot.rsmul (-c₀) S.Θ) := by
    rw [isPsh_iff hpotb]
    intro j y hy w
    rw [dl_add_rsmul hth S.potΘ (-c₀) j hy w]
    have := hcmp j y hy w
    linarith
  have ha' : ∀ t, IsPsh S.A (S.potT none t + LocPot.rsmul (-c₀) S.Θ) := by
    intro t x j y hy w
    have hy' : y ∈ (S.A.chart j).target ∩ ↑(S.A.chart j).symm ⁻¹'
        (S.th none + LocPot.rsmul (-c₀) S.Θ).U x := by
      refine ⟨hy.1, ?_⟩
      have h2 := hy.2
      simp only [Set.mem_preimage] at h2 ⊢
      exact ⟨h2.1.1, h2.2⟩
    have h3 := hbase x j y hy' w
    convert h3 using 2
    funext z
    simp only [Function.comp_apply]
    show (S.th none).φ x _ + S.phT none t _ + -c₀ * S.Θ.φ x _ =
      (S.th none).φ x _ + -c₀ * S.Θ.φ x _
    rw [h0]
    ring
  let Fl : Set (Option (Ψ × Fin N)) := {a | ∃ p : Ψ × Fin N, a = some p ∧ (p.2 : ℕ) + 1 = N}
  have hFl : ∀ a ∈ Fl, ∀ t, IsPsh S.A (LocPot.rsmul (-1) (S.potT a t)) ∧ IsPsh S.A (S.potT a t) := by
    rintro a ⟨p, rfl, hp⟩ t
    exact hfl p.1 p.2 hp t
  have hnone : (none : Option (Ψ × Fin N)) ∉ Fl := by
    rintro ⟨p, hp, -⟩
    cases hp
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set abelian₂ : ℝ := 1 + ∑ _p : Ψ × Fin N, (k : ℝ) * (2 * b) with hLam
  obtain ⟨s₁, hs₁, hall⟩ := psh_sum_potentials_small_parameter D _ S Fl none c₀ abelian₂ hc₀ hFl ha' hnone
  refine ⟨min s₁ 1, lt_min hs₁ one_pos, fun s hs hss => ?_⟩
  obtain ⟨hsc, hmain⟩ := hall s hs (le_trans hss (min_le_left _ _))
  have hs1 : s ≤ 1 := le_trans hss (min_le_right _ _)
  refine ⟨hsc, fun mu hmu hdom => ?_⟩
  have hpot : ∀ a, IsPotential S.A (S.potT a (scale s)) :=
    fun a => potT_potential S a (Real.exp_pos _) hsc
  set c : Option (Ψ × Fin N) → ℝ := PB.gapS (fun x => mu x.1 x.2) (s / k) with hc
  have hcn : c none = s / k := rfl
  have hcs : ∀ p, c (some p) = PB.gap (fun x => mu x.1 x.2) p := fun p => rfl
  let c' : Option (Ψ × Fin N) → ℝ := fun a => (k : ℝ) * c a
  have h1 : c' none = s := by
    show (k : ℝ) * c none = s
    rw [hcn]
    field_simp
  have h2 : ∑ a, |c' a| ≤ abelian₂ := by
    rw [Fintype.sum_option, hLam]
    have e1 : |c' none| ≤ 1 := by rw [h1, abs_of_pos hs]; exact hs1
    have e2 : ∑ p : Ψ × Fin N, |c' (some p)| ≤ ∑ _p : Ψ × Fin N, (k : ℝ) * (2 * b) := by
      refine Finset.sum_le_sum fun p _ => ?_
      show |(k : ℝ) * c (some p)| ≤ _
      rw [abs_mul, abs_of_pos hkR, hcs]
      exact mul_le_mul_of_nonneg_left (abs_gap_le mu b hmu p) hkR.le
    linarith
  have h3 : ∀ a ∉ Fl, 0 ≤ c' a := by
    intro a ha
    cases a with
    | none => rw [h1]; exact hs.le
    | some p =>
      show 0 ≤ (k : ℝ) * c (some p)
      refine mul_nonneg hkR.le ?_
      rw [hcs, gap_eq]
      have hlt : (p.2 : ℕ) + 1 < N := by
        have hne : (p.2 : ℕ) + 1 ≠ N := fun h => ha ⟨p, rfl, h⟩
        have := p.2.isLt
        omega
      rw [dif_pos hlt]
      have := hdom p.1 p.2 ⟨(p.2 : ℕ) + 1, hlt⟩ (by
        show (p.2 : ℕ) ≤ (p.2 : ℕ) + 1
        omega)
      simp only
      linarith
  have hP : IsPsh S.A (PB.sumPot c' (fun a => S.potT a (scale s)) +
      LocPot.rsmul (-(s * c₀ / 2)) S.Θ) := hmain c' h1 h2 h3
  rw [isPsh_iff (isPotential_sumPot c hpot)]
  intro j y hy w
  have hq := dl_nonneg hP j hy w
  rw [dl_add_rsmul (isPotential_sumPot c' hpot) S.potΘ _ j hy w, dl_sumPot c' hpot j hy w] at hq
  rw [dl_sumPot c hpot j hy w]
  have hΘ := dl_nonneg_of_pos S.posΘ j hy w
  have hsum : ∑ a, c' a * dl S.A (S.potT a (scale s)) j y w =
      (k : ℝ) * ∑ a, c a * dl S.A (S.potT a (scale s)) j y w := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    show (k : ℝ) * c a * _ = _
    ring
  rw [hsum] at hq
  have hsc0 : 0 ≤ s * c₀ / 2 * dl S.A S.Θ j y w := mul_nonneg (by positivity) hΘ
  have hk2 : 0 ≤ (k : ℝ) * ∑ a, c a * dl S.A (S.potT a (scale s)) j y w := by linarith
  exact (mul_nonneg_iff_of_pos_left hkR).mp hk2

end RootFieldNumerics.A1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

theorem RootFieldNumerics.real_tower_mean_slope_condition : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (R : RealTower T), R.Smooth → R.Flat → R.Pos → T.A1 := by
  intro _hin II _hII Ψ _ _ N T R hSm hFl hPos
  haveI := T.finC
  haveI := T.neC
  intro abelian₂
  set b : ℝ := abelian₂ + l1 T.nu with hb
  have hex : ∀ c : T.Comp, ∃ s₀ > (0 : ℝ), ∀ s, 0 < s → s ≤ s₀ → scale s ≤ (R.Sys c).t₀ ∧
      ∀ mu : Wt Ψ N, (∀ τ i, |mu τ i| ≤ b) → Dominant mu →
        ReciprocityTheory.AnForm.M.IsPsh (R.Sys c).A (PB.sumPot (PB.gapS (fun x => mu x.1 x.2)
          (s / ((T.M 2 c).kA : ℕ))) fun a => (R.Sys c).potT a (scale s)) := by
    intro c
    exact RootFieldNumerics.A1.comp_psh (R.Sys c) (T.M 2 c).kA (T.M 2 c).kA_pos b ((R.tie 2 c).phT_none)
      (hFl c) (hPos c)
  choose f hfpos hf using hex
  refine ⟨min 1 (Finset.univ.inf' Finset.univ_nonempty f),
    lt_min one_pos ((Finset.lt_inf'_iff _).2 fun c _ => hfpos c), ?_⟩
  intro B _hB c lam s hlam hs hss hdom
  have hs1 : s ≤ 1 := le_trans hss (min_le_left _ _)
  have hsf : s ≤ f c :=
    le_trans hss (le_trans (min_le_right _ _) (Finset.inf'_le f (Finset.mem_univ c)))
  obtain ⟨hsc, hmain⟩ := hf c s hs hsf
  set mu := T.lamS lam s with hmu
  have hbd : ∀ τ i, |mu τ i| ≤ b := by
    intro τ i
    have e1 := RootFieldNumerics.A1.abs_le_l1_norm lam τ i
    have e2 := RootFieldNumerics.A1.abs_le_l1_norm T.nu τ i
    have e0 : mu τ i = lam τ i - s * T.nu τ i := rfl
    rw [e0]
    have e3 : |s * T.nu τ i| ≤ |T.nu τ i| := by
      rw [abs_mul, abs_of_pos hs]
      exact mul_le_of_le_one_left (abs_nonneg _) hs1
    calc |lam τ i - s * T.nu τ i| ≤ |lam τ i| + |s * T.nu τ i| := abs_sub _ _
      _ ≤ b := by rw [hb]; linarith
  have hpsh := hmain mu hbd hdom
  have hk : ((T.M B c).kA : ℝ) = ((T.M 2 c).kA : ℕ) := by rw [R.kA_eq B 2 c]
  obtain ⟨hJ, alg, hsmooth⟩ := hSm B c
  letI := alg
  have ht0 : 0 < scale s := Real.exp_pos _
  intro z hz w hw
  refine RootFieldNumerics.Levi.levi_nonneg (T.M B c).Ω (T.M B c).y (dimFl Ψ N) (T.M B c).arith hsmooth hJ
    (R.tie B c).Re.R ((T.M B c).weight (scale s) mu s)
    (fun k => ∑ j, (T.M B c).coef mu s j * (((T.M B c).line (scale s) j).a k : ℝ)) ?_ ?_ ?_ z hz w hw
  · intro cc zz hcc hzz
    simp only [RootModel.weight, RootFieldNumerics.Levi.log_h_torus _ cc zz hcc hzz]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  · intro zz hzz
    have hsm : ∀ j, IsSmoothHerm ((T.M B c).line (scale s) j) := by
      intro j
      cases j with
      | none => exact (T.M B c).A_smooth
      | some r => exact (T.M B c).x_smooth (scale s) r
    show ContDiffAt ℝ 2
      (fun z => ∑ j, (T.M B c).coef mu s j * Real.log (((T.M B c).line (scale s) j).h z)) zz
    exact ContDiffAt.sum fun j _ =>
      contDiffAt_const.mul (RootFieldNumerics.Levi.contDiffAt_log_h (hsm j) zz hzz)
  · intro x j hx u
    refine RootFieldNumerics.Levi.levi_chart_nonneg (R.tie B c).Re (scale s) ht0 hsc _ hpsh x
      (fun y => (T.M B c).weight (scale s) mu s ((R.tie B c).Re.R.lift x y)) ?_ j hx u
    intro y hy
    have hzm : (R.tie B c).Re.R.lift x y ∈ mcPts (T.M B c).P := (R.tie B c).Re.R.mem x y hy
    have hl : ∀ a, Real.log (((R.tie B c).Re.ref a).h ((R.tie B c).Re.R.lift x y)) +
        (R.Sys c).phT a (scale s) ((R.tie B c).Re.π y) =
        Real.log (((R.tie B c).Re.line a (scale s)).h ((R.tie B c).Re.R.lift x y)) :=
      fun a => (RootFieldNumerics.Levi.log_line_lift (R.tie B c).Re a (scale s) ht0 hsc x y hy).symm
    simp only [hl]
    have hnone : Real.log (((R.tie B c).Re.line none (scale s)).h ((R.tie B c).Re.R.lift x y)) =
        Real.log ((T.M B c).A.h ((R.tie B c).Re.R.lift x y)) := by
      rw [← hl none, (R.tie B c).phT_none, add_zero, (R.tie B c).ref_none.2 _ hzm]
    have hsome : ∀ p : Ψ × Fin N,
        Real.log (((R.tie B c).Re.line (some p) (scale s)).h ((R.tie B c).Re.R.lift x y)) =
        -∑ k ≤ p.2, Real.log (((T.M B c).x (scale s) (p.1, k)).h ((R.tie B c).Re.R.lift x y)) :=
      fun p => (R.tie B c).fund_reg p.1 p.2 (scale s) ht0 hsc _ hzm
    rw [Fintype.sum_option, hnone]
    simp only [hsome]
    have hsg := RootFieldNumerics.Levi.sum_gap_mul (fun x => mu x.1 x.2)
      (fun r => Real.log (((T.M B c).x (scale s) r).h ((R.tie B c).Re.R.lift x y)))
    simp only [RootModel.weight, Fintype.sum_option, RootModel.coef, RootModel.line, PB.gapS,
      Option.elim, mul_neg, Finset.sum_neg_distrib, neg_mul, hsg]
    rw [hk]
end
end
