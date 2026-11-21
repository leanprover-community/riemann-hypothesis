import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.HasCompactSupportDTw
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.HalfSumNormSubSq
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.WIbpLeft

section
namespace ReciprocityTheory.L2DbarEstimates.E

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

private lemma chart_symm_eventuallyEq_of_isChart {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e e' : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (he' : IsChart n z e')
    (p : M) (hp : p ∈ e.source) (hp' : p ∈ e'.source) :
    e.symm =ᶠ[nhds (z p)] e'.symm := by
  have he0 : Set.EqOn z e e.source := he
  have he0' : Set.EqOn z e' e'.source := he'
  have hzp : z p = e' p := he0' hp'
  have h2 : e'.target ∩ e'.symm ⁻¹' e.source ∈ nhds (z p) := by
    rw [hzp]
    refine (e'.isOpen_inter_preimage_symm e.open_source).mem_nhds ⟨e'.map_source hp', ?_⟩
    rw [Set.mem_preimage, e'.left_inv hp']
    exact hp
  filter_upwards [h2] with y hy
  have hs : e'.symm y ∈ e'.source := e'.map_target hy.1
  have h3 : e (e'.symm y) = y := by
    rw [← he0 hy.2, he0' hs, e'.right_inv hy.1]
  calc e.symm y = e.symm (e (e'.symm y)) := by rw [h3]
    _ = e'.symm y := e.left_inv hy.2

private lemma db_eq_wdb_comp_chart_symm {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e0 : OpenPartialHomeomorph M (V n)) (he0 : IsChart n z e0) (k : Fin n) (g : M → ℂ)
    (p : M) (hp : p ∈ e0.source) : db n z k g p = wdb n k (g ∘ e0.symm) (z p) := by
  have hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ p ∈ e.source := ⟨e0, he0, hp⟩
  have hspec := Classical.choose_spec hex
  have hE : (g ∘ (Classical.choose hex).symm) =ᶠ[nhds (z p)] (g ∘ e0.symm) :=
    (chart_symm_eventuallyEq_of_isChart z _ e0 hspec.1 he0 p hspec.2 hp).fun_comp g
  rw [db, dif_pos hex]
  unfold wdb
  rw [hE.fderiv_eq]

private lemma d_apply_eq_wd_of_mem_source {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e0 : OpenPartialHomeomorph M (V n)) (he0 : IsChart n z e0) (k : Fin n) (g : M → ℂ)
    (p : M) (hp : p ∈ e0.source) : d n z k g p = wd n k (g ∘ e0.symm) (z p) := by
  have hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ p ∈ e.source := ⟨e0, he0, hp⟩
  have hspec := Classical.choose_spec hex
  have hE : (g ∘ (Classical.choose hex).symm) =ᶠ[nhds (z p)] (g ∘ e0.symm) :=
    (chart_symm_eventuallyEq_of_isChart z _ e0 hspec.1 he0 p hspec.2 hp).fun_comp g
  rw [d, dif_pos hex]
  unfold wd
  rw [hE.fderiv_eq]

private lemma differentiableAt_wdb_and_fderiv_wdb_eq {n : ℕ} (k : Fin n) (h : V n → ℂ) (y0 : V n)
    (hd : DifferentiableAt ℝ (fderiv ℝ h) y0) :
    DifferentiableAt ℝ (wdb n k h) y0 ∧ ∀ v : V n, fderiv ℝ (wdb n k h) y0 v =
      (fderiv ℝ (fderiv ℝ h) y0 v (bas n k) +
        Complex.I * fderiv ℝ (fderiv ℝ h) y0 v (Complex.I • bas n k)) / 2 := by
  have hA := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (bas n k) y0)
  have hB := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Complex.I • bas n k) y0)
  have hW := HasFDerivAt.const_mul (HasFDerivAt.add hA (HasFDerivAt.const_mul hB Complex.I))
    ((2 : ℂ)⁻¹)
  have heq : wdb n k h = fun y =>
      (2 : ℂ)⁻¹ * (fderiv ℝ h y (bas n k) + Complex.I * fderiv ℝ h y (Complex.I • bas n k)) := by
    funext y
    rw [wdb, div_eq_inv_mul]
  have hW' : HasFDerivAt (wdb n k h) ((2 : ℂ)⁻¹ •
      ((fderiv ℝ h y0).comp (0 : V n →L[ℝ] V n) + (fderiv ℝ (fderiv ℝ h) y0).flip (bas n k) +
        Complex.I • ((fderiv ℝ h y0).comp (0 : V n →L[ℝ] V n) +
          (fderiv ℝ (fderiv ℝ h) y0).flip (Complex.I • bas n k)))) y0 := by
    rw [heq]
    exact hW
  refine ⟨HasFDerivAt.differentiableAt hW', fun v => ?_⟩
  rw [HasFDerivAt.fderiv hW']
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, map_zero, zero_add,
    ContinuousLinearMap.flip_apply, smul_eq_mul]
  ring

private lemma differentiableAt_wd_and_fderiv_wd_eq {n : ℕ} (k : Fin n) (h : V n → ℂ) (y0 : V n)
    (hd : DifferentiableAt ℝ (fderiv ℝ h) y0) :
    DifferentiableAt ℝ (wd n k h) y0 ∧ ∀ v : V n, fderiv ℝ (wd n k h) y0 v =
      (fderiv ℝ (fderiv ℝ h) y0 v (bas n k) -
        Complex.I * fderiv ℝ (fderiv ℝ h) y0 v (Complex.I • bas n k)) / 2 := by
  have hA := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (bas n k) y0)
  have hB := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Complex.I • bas n k) y0)
  have hW := HasFDerivAt.const_mul (HasFDerivAt.sub hA (HasFDerivAt.const_mul hB Complex.I))
    ((2 : ℂ)⁻¹)
  have heq : wd n k h = fun y =>
      (2 : ℂ)⁻¹ * (fderiv ℝ h y (bas n k) - Complex.I * fderiv ℝ h y (Complex.I • bas n k)) := by
    funext y
    rw [wd, div_eq_inv_mul]
  have hW' : HasFDerivAt (wd n k h) ((2 : ℂ)⁻¹ •
      ((fderiv ℝ h y0).comp (0 : V n →L[ℝ] V n) + (fderiv ℝ (fderiv ℝ h) y0).flip (bas n k) -
        Complex.I • ((fderiv ℝ h y0).comp (0 : V n →L[ℝ] V n) +
          (fderiv ℝ (fderiv ℝ h) y0).flip (Complex.I • bas n k)))) y0 := by
    rw [heq]
    exact hW
  refine ⟨HasFDerivAt.differentiableAt hW', fun v => ?_⟩
  rw [HasFDerivAt.fderiv hW']
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply,
    smul_eq_mul]
  ring

theorem comm (n : ℕ) (M : Type*) [TopologicalSpace M] : CommStatement n M := by
  intro z hz ph j k u x hph hu
  obtain ⟨e0, hx0, hze⟩ := hz x
  have he0 : IsChart n z e0 := by
    intro y _
    rw [hze]
  have he0' : Set.EqOn z e0 e0.source := he0
  have hy0 : z x ∈ e0.target := by
    rw [he0' hx0]
    exact e0.map_source hx0
  have hnb : e0.target ∈ nhds (z x) := e0.open_target.mem_nhds hy0
  have hcH : ContDiffAt ℝ 2 (u ∘ e0.symm) (z x) := by
    have := (hu e0 he0).contDiffAt hnb
    simpa using this
  have hcP : ContDiffAt ℝ 2 ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm) (z x) := by
    have := (hph e0 he0).contDiffAt hnb
    simpa using this
  have hdH : DifferentiableAt ℝ (fderiv ℝ (u ∘ e0.symm)) (z x) :=
    (hcH.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdP : DifferentiableAt ℝ (fderiv ℝ ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm)) (z x) :=
    (hcP.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hH : DifferentiableAt ℝ (u ∘ e0.symm) (z x) := hcH.differentiableAt (by norm_num)
  have hsymH : ∀ v w : V n, fderiv ℝ (fderiv ℝ (u ∘ e0.symm)) (z x) v w =
      fderiv ℝ (fderiv ℝ (u ∘ e0.symm)) (z x) w v := by
    intro v w
    first
      | exact hcH.isSymmSndFDerivAt (by simp) v w
      | exact hcH.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) v w
  have hsymP : ∀ v w : V n, fderiv ℝ (fderiv ℝ ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm)) (z x) v w =
      fderiv ℝ (fderiv ℝ ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm)) (z x) w v := by
    intro v w
    first
      | exact hcP.isSymmSndFDerivAt (by simp) v w
      | exact hcP.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) v w
  have hloc1 : ((db n z j u) ∘ e0.symm) =ᶠ[nhds (z x)] wdb n j (u ∘ e0.symm) := by
    filter_upwards [hnb] with y hy
    rw [Function.comp_apply, db_eq_wdb_comp_chart_symm z e0 he0 j u _ (e0.map_target hy),
      he0' (e0.map_target hy), e0.right_inv hy]
  have hloc2 : ((db n z j (fun y => ((ph y : ℝ) : ℂ))) ∘ e0.symm) =ᶠ[nhds (z x)] wdb n j ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm) := by
    filter_upwards [hnb] with y hy
    rw [Function.comp_apply, db_eq_wdb_comp_chart_symm z e0 he0 j _ _ (e0.map_target hy),
      he0' (e0.map_target hy), e0.right_inv hy]
  have hloc3 : ((fun y => d n z k u y - u y * d n z k (fun y => ((ph y : ℝ) : ℂ)) y) ∘ e0.symm) =ᶠ[nhds (z x)]
      (fun y => wd n k (u ∘ e0.symm) y - (u ∘ e0.symm) y * wd n k ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm) y) := by
    filter_upwards [hnb] with y hy
    have hp := e0.map_target hy
    rw [Function.comp_apply, d_apply_eq_wd_of_mem_source z e0 he0 k u _ hp, d_apply_eq_wd_of_mem_source z e0 he0 k _ _ hp,
      he0' hp, e0.right_inv hy]
    rfl
  have hux : u x = (u ∘ e0.symm) (z x) := by
    rw [Function.comp_apply, he0' hx0, e0.left_inv hx0]
  have hW1 := (differentiableAt_wdb_and_fderiv_wdb_eq j _ _ hdH).2
  have hW2 := differentiableAt_wd_and_fderiv_wd_eq k _ _ hdH
  have hW3 := differentiableAt_wd_and_fderiv_wd_eq k _ _ hdP
  have hW4 := (differentiableAt_wdb_and_fderiv_wdb_eq j _ _ hdP).2
  have hFG : fderiv ℝ (fun y => wd n k (u ∘ e0.symm) y - (u ∘ e0.symm) y * wd n k ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm) y) (z x) =
      fderiv ℝ (wd n k (u ∘ e0.symm)) (z x) - ((u ∘ e0.symm) (z x) • fderiv ℝ (wd n k ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm)) (z x) +
        wd n k ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm) (z x) • fderiv ℝ (u ∘ e0.symm) (z x)) := by
    have h1 := HasFDerivAt.sub (DifferentiableAt.hasFDerivAt hW2.1)
      (HasFDerivAt.mul (DifferentiableAt.hasFDerivAt hH) (DifferentiableAt.hasFDerivAt hW3.1))
    exact HasFDerivAt.fderiv h1
  show (d n z k (db n z j u) x - db n z j u x * d n z k (fun y => ((ph y : ℝ) : ℂ)) x) -
      db n z j (fun y => d n z k u y - u y * d n z k (fun y => ((ph y : ℝ) : ℂ)) y) x =
    d n z k (db n z j (fun y => ((ph y : ℝ) : ℂ))) x * u x
  rw [d_apply_eq_wd_of_mem_source z e0 he0 k (db n z j u) x hx0, db_eq_wdb_comp_chart_symm z e0 he0 j u x hx0,
    d_apply_eq_wd_of_mem_source z e0 he0 k (fun y => ((ph y : ℝ) : ℂ)) x hx0, db_eq_wdb_comp_chart_symm z e0 he0 j _ x hx0,
    d_apply_eq_wd_of_mem_source z e0 he0 k (db n z j (fun y => ((ph y : ℝ) : ℂ))) x hx0, hux]
  unfold wd wdb
  rw [hloc1.fderiv_eq, hloc2.fderiv_eq, hloc3.fderiv_eq, hFG]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hW1 (bas n k), hW1 (Complex.I • bas n k), hW2.2 (bas n j), hW2.2 (Complex.I • bas n j),
    hW3.2 (bas n j), hW3.2 (Complex.I • bas n j), hW4 (bas n k), hW4 (Complex.I • bas n k)]
  unfold wd
  rw [hsymH (bas n k) (bas n j), hsymH (bas n k) (Complex.I • bas n j),
    hsymH (Complex.I • bas n k) (bas n j), hsymH (Complex.I • bas n k) (Complex.I • bas n j),
    hsymP (bas n k) (bas n j), hsymP (bas n k) (Complex.I • bas n j),
    hsymP (Complex.I • bas n k) (bas n j), hsymP (Complex.I • bas n k) (Complex.I • bas n j)]
  ring

end

end ReciprocityTheory.L2DbarEstimates.E
end

section
namespace ReciprocityTheory.L2DbarEstimates.E

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

theorem pair (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (hph : CkR n z 2 ph) (a b : M → ℂ) (ha : Ck n z 2 a) (_hac : HasCompactSupport a)
    (hb : Ck n z 2 b) (hbc : HasCompactSupport b) (j k : Fin n) :
    (∫ x, dTw n z ph j a x * conj (dTw n z ph k b x) * (Real.exp (-ph x) : ℂ) ∂vol n z) =
      (∫ x, d n z j (db n z k (fun y => (ph y : ℂ))) x * a x * conj (b x) *
          (Real.exp (-ph x) : ℂ) ∂vol n z) +
        ∫ x, db n z k a x * conj (db n z j b x) * (Real.exp (-ph x) : ℂ) ∂vol n z := by
  have hph1 : CkR n z 1 ph := Ck.mono n z 1 2 (by norm_num) _ hph
  have ha1 : Ck n z 1 a := Ck.mono n z 1 2 (by norm_num) a ha
  have hb1 : Ck n z 1 b := Ck.mono n z 1 2 (by norm_num) b hb
  have hE := ck_expNeg n z 1 ph hph1
  have hdTa : Ck n z 1 (dTw n z ph j a) := ck_dTw n z 1 ph j a hph ha
  have hdba : Ck n z 1 (db n z k a) := Ck.db n z 1 k a ha
  have s1 := wIbp_left n z hz ph k (dTw n z ph j a) b hph1 hdTa hb1 (Or.inr hbc)
  have s3 := ((wIbp n M) z hz ph j (db n z k a) b hph1 hdba hb1 (Or.inr hbc)).2
  have hcomm : ∀ x, db n z k (dTw n z ph j a) x = dTw n z ph j (db n z k a) x -
      d n z j (db n z k (fun y => (ph y : ℂ))) x * a x := by
    intro x
    have := comm n M z hz ph k j a x hph ha
    linear_combination -this
  have hcb : Continuous (fun x => conj (b x)) := Ck.continuous n z hz 1 _ (Ck.conj n z 1 b hb1)
  have hcE : Continuous (fun x => (Real.exp (-ph x) : ℂ)) := Ck.continuous n z hz 1 _ hE
  have hint1 : Integrable (fun x => dTw n z ph j (db n z k a) x * conj (b x) *
      (Real.exp (-ph x) : ℂ)) (vol n z) := by
    apply integrable_of_continuous n z hz
    · exact ((Ck.continuous n z hz 0 _ (ck_dTw n z 0 ph j (db n z k a) hph1 hdba)).mul hcb).mul hcE
    · apply HasCompactSupport.mono' hbc
      intro x hx
      apply subset_tsupport
      intro h0
      apply hx
      simp [h0]
  have hint2 : Integrable (fun x => d n z j (db n z k (fun y => (ph y : ℂ))) x * a x *
      conj (b x) * (Real.exp (-ph x) : ℂ)) (vol n z) := by
    apply integrable_of_continuous n z hz
    · exact (((Ck.continuous n z hz 0 _ (Ck.d n z 0 j _ (Ck.db n z 1 k _ hph))).mul
        (Ck.continuous n z hz 1 _ ha1)).mul hcb).mul hcE
    · apply HasCompactSupport.mono' hbc
      intro x hx
      apply subset_tsupport
      intro h0
      apply hx
      simp [h0]
  have e2 : ∫ x, db n z k (dTw n z ph j a) x * conj (b x) * (Real.exp (-ph x) : ℂ) ∂vol n z =
      (∫ x, dTw n z ph j (db n z k a) x * conj (b x) * (Real.exp (-ph x) : ℂ) ∂vol n z) -
        ∫ x, d n z j (db n z k (fun y => (ph y : ℂ))) x * a x * conj (b x) *
          (Real.exp (-ph x) : ℂ) ∂vol n z := by
    rw [← integral_sub hint1 hint2]
    congr 1
    funext x
    rw [hcomm x]
    ring
  rw [e2, s3] at s1
  linear_combination s1

end

end ReciprocityTheory.L2DbarEstimates.E
end

section
namespace ReciprocityTheory.L2DbarEstimates.E

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

theorem integral_re_double_sum {M : Type*} [MeasurableSpace M] (μ : Measure M) (n : ℕ)
    (h : Fin n → Fin n → M → ℂ) (hi : ∀ j k, Integrable (h j k) μ) :
    ∫ x, (∑ j, ∑ k, h j k x).re ∂μ = (∑ j, ∑ k, ∫ x, h j k x ∂μ).re := by
  have hint : Integrable (fun x => ∑ j, ∑ k, h j k x) μ :=
    integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ => hi j k
  have h1 := integral_re (𝕜 := ℂ) hint
  simp only [RCLike.re_to_complex] at h1
  rw [h1, integral_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ => hi j k]
  congr 1
  exact Finset.sum_congr rfl fun j _ => integral_finset_sum _ fun k _ => hi j k

theorem hasCompactSupport_of_vanish {M : Type*} [TopologicalSpace M] (u F : M → ℂ)
    (hu : HasCompactSupport u) (h : ∀ x, u x = 0 → F x = 0) : HasCompactSupport F :=
  hu.mono' fun x hx => subset_tsupport u (mt (h x) hx)

theorem basicIdentity (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] :
    BasicIdentityStatement n M := by
  intro z hz ph f hph hf
  have hph1 : CkR n z 1 ph := Ck.mono n z 1 2 (by norm_num) _ hph
  have hE : Ck n z 1 (fun x => (Real.exp (-ph x) : ℂ)) := ck_expNeg n z 1 ph hph1
  have hEc : Continuous (fun x => (Real.exp (-ph x) : ℂ)) := Ck.continuous n z hz 1 _ hE
  have hFc : ∀ j, Continuous (fun y => f y j) := fun j => Ck.continuous n z hz 2 _ (hf j).1
  have hTc : ∀ j, Continuous (dTw n z ph j (fun y => f y j)) :=
    fun j => Ck.continuous n z hz 1 _ (ck_dTw n z 1 ph j _ hph (hf j).1)
  have hDc : ∀ j k, Continuous (db n z k (fun y => f y j)) :=
    fun j k => Ck.continuous n z hz 1 _ (Ck.db n z 1 k _ (hf j).1)
  have hLc : ∀ j k, Continuous (d n z j (db n z k (fun y => (ph y : ℂ)))) :=
    fun j k => Ck.continuous n z hz 0 _ (Ck.d n z 0 j _ (Ck.db n z 1 k _ hph))
  have hcc : ∀ {g : M → ℂ}, Continuous g → Continuous (fun x => conj (g x)) :=
    fun hg => Complex.continuous_conj.comp hg

  set D : Fin n → Fin n → M → ℂ := fun j k x => dTw n z ph j (fun y => f y j) x *
    conj (dTw n z ph k (fun y => f y k) x) * (Real.exp (-ph x) : ℂ) with hD
  set L : Fin n → Fin n → M → ℂ := fun j k x => d n z j (db n z k (fun y => (ph y : ℂ))) x *
    f x j * conj (f x k) * (Real.exp (-ph x) : ℂ) with hL
  set C : Fin n → Fin n → M → ℂ := fun j k x => db n z k (fun y => f y j) x *
    conj (db n z j (fun y => f y k) x) * (Real.exp (-ph x) : ℂ) with hC
  set Q : Fin n → Fin n → M → ℂ := fun j k x => db n z k (fun y => f y j) x *
    conj (db n z k (fun y => f y j) x) * (Real.exp (-ph x) : ℂ) with hQ
  have iD : ∀ j k, Integrable (D j k) (vol n z) := by
    intro j k
    apply integrable_of_continuous n z hz
    · exact ((hTc j).mul (hcc (hTc k))).mul hEc
    · exact hasCompactSupport_of_vanish _ _
        (hasCompactSupport_dTw n z ph j _ (hf j).2) (fun x h0 => by simp [hD, h0])
  have iL : ∀ j k, Integrable (L j k) (vol n z) := by
    intro j k
    apply integrable_of_continuous n z hz
    · exact (((hLc j k).mul (hFc j)).mul (hcc (hFc k))).mul hEc
    · exact hasCompactSupport_of_vanish _ _ (hf j).2 (fun x h0 => by simp [hL, h0])
  have iC : ∀ j k, Integrable (C j k) (vol n z) := by
    intro j k
    apply integrable_of_continuous n z hz
    · exact ((hDc j k).mul (hcc (hDc k j))).mul hEc
    · exact hasCompactSupport_of_vanish _ _
        (hasCompactSupport_db n z k _ (hf j).2) (fun x h0 => by simp [hC, h0])
  have iQ : ∀ j k, Integrable (Q j k) (vol n z) := by
    intro j k
    apply integrable_of_continuous n z hz
    · exact ((hDc j k).mul (hcc (hDc j k))).mul hEc
    · exact hasCompactSupport_of_vanish _ _
        (hasCompactSupport_db n z k _ (hf j).2) (fun x h0 => by simp [hQ, h0])
  have iQC : ∀ j k, Integrable (fun x => Q j k x - C j k x) (vol n z) :=
    fun j k => (iQ j k).sub (iC j k)

  have pA : ∀ x, ‖∑ j, dTw n z ph j (fun y => f y j) x‖ ^ 2 * Real.exp (-ph x) =
      (∑ j, ∑ k, D j k x).re := by
    intro x
    rw [norm_sum_sq_eq]
    simp only [hD, Complex.re_sum, Complex.re_mul_ofReal, Finset.sum_mul]
  have pL : ∀ x, (Levi n z ph x (fun j => f x j)).re * Real.exp (-ph x) =
      (∑ j, ∑ k, L j k x).re := by
    intro x
    simp only [Levi, hL, Complex.re_sum, Complex.re_mul_ofReal, Finset.sum_mul]
  have hnq : ∀ w : ℂ, ‖w‖ ^ 2 = (w * conj w).re := by
    intro w
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have pQ : ∀ x, (∑ j, ∑ k, ‖db n z k (fun y => f y j) x‖ ^ 2) * Real.exp (-ph x) =
      (∑ j, ∑ k, Q j k x).re := by
    intro x
    simp only [hQ, hnq, Complex.re_sum, Complex.re_mul_ofReal, Finset.sum_mul]
  have pS : ∀ x, sq2 n (sbar n z f x) * Real.exp (-ph x) =
      (∑ j, ∑ k, (Q j k x - C j k x)).re := by
    intro x
    have h := half_sum_norm_sub_sq (fun j k => db n z j (fun y => f y k) x)
    simp only at h
    unfold sq2 sbar
    rw [h]
    simp only [hQ, hC, hnq, Complex.re_sum, Complex.sub_re, Complex.re_mul_ofReal,
      Finset.sum_sub_distrib, sub_mul, Finset.sum_mul]
  have hA := integral_re_double_sum (vol n z) n D iD
  have hLi := integral_re_double_sum (vol n z) n L iL
  have hQi := integral_re_double_sum (vol n z) n Q iQ
  have hSi := integral_re_double_sum (vol n z) n (fun j k x => Q j k x - C j k x) iQC
  have hpair : ∀ j k, ∫ x, D j k x ∂vol n z = (∫ x, L j k x ∂vol n z) + ∫ x, C j k x ∂vol n z :=
    fun j k => pair n z hz ph hph (fun y => f y j) (fun y => f y k) (hf j).1 (hf j).2
      (hf k).1 (hf k).2 j k
  have hsub : ∀ j k, ∫ x, (Q j k x - C j k x) ∂vol n z =
      (∫ x, Q j k x ∂vol n z) - ∫ x, C j k x ∂vol n z :=
    fun j k => integral_sub (iQ j k) (iC j k)
  rw [integral_congr_ae (Filter.Eventually.of_forall pA), integral_congr_ae (Filter.Eventually.of_forall pS),
    integral_congr_ae (Filter.Eventually.of_forall pL), integral_congr_ae (Filter.Eventually.of_forall pQ),
    hA, hLi, hQi, hSi]
  simp only [hpair, hsub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Complex.add_re,
    Complex.sub_re]
  ring

end

end ReciprocityTheory.L2DbarEstimates.E
end
