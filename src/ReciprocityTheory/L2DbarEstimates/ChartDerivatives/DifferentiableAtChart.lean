import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq

namespace ReciprocityTheory.L2DbarEstimates

namespace ChartWirtingerDerivatives

open Filter Topology Set
open scoped ContDiff

noncomputable section



theorem chart_mem_target {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (x : M) (hx : x ∈ e.source) :
    z x ∈ e.target := by
  rw [he hx]
  exact e.map_source hx


theorem Ck.differentiableAt_chart {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (f : M → ℂ) (hf : Ck n z 1 f) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e)
    (x : M) (hx : x ∈ e.source) :
    DifferentiableAt ℝ (f ∘ e.symm) (z x) :=
  ((hf e he).contDiffAt (e.open_target.mem_nhds (chart_mem_target n z e he x hx))).differentiableAt
    (by simp)





theorem wd_mul' (n : ℕ) (j : Fin n) (g h : V n → ℂ) (y : V n) (hg : DifferentiableAt ℝ g y)
    (hh : DifferentiableAt ℝ h y) :
    wd n j (fun w => g w * h w) y = wd n j g y * h y + g y * wd n j h y := by
  simp only [wd, fderiv_fun_mul hg hh, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring




theorem fderiv_conj' (n : ℕ) (g : V n → ℂ) (y : V n) (v : V n) :
    fderiv ℝ (fun w => (starRingEnd ℂ) (g w)) y v = (starRingEnd ℂ) (fderiv ℝ g y v) := by
  have h : (fun w => (starRingEnd ℂ) (g w)) = Complex.conjLIE ∘ g := by
    funext w
    simp [Complex.conjLIE_apply]
  rw [h, LinearIsometryEquiv.comp_fderiv]
  simp

theorem wdb_conj' (n : ℕ) (j : Fin n) (g : V n → ℂ) (y : V n) :
    wdb n j (fun w => (starRingEnd ℂ) (g w)) y = (starRingEnd ℂ) (wd n j g y) := by
  simp only [wdb, wd, fderiv_conj', map_div₀, map_sub, map_mul, Complex.conj_I, map_ofNat]
  ring

theorem wd_conj' (n : ℕ) (j : Fin n) (g : V n → ℂ) (y : V n) :
    wd n j (fun w => (starRingEnd ℂ) (g w)) y = (starRingEnd ℂ) (wdb n j g y) := by
  simp only [wdb, wd, fderiv_conj', map_div₀, map_add, map_mul, Complex.conj_I, map_ofNat]
  ring



theorem CkR.differentiableAt_chart {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (ph : M → ℝ) (hph : CkR n z 1 ph) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e)
    (x : M) (hx : x ∈ e.source) :
    DifferentiableAt ℝ (fun w => ph (e.symm w)) (z x) := by
  have h := (Complex.reCLM.differentiable.differentiableAt).comp (z x)
    (Ck.differentiableAt_chart n z _ hph e he x hx)
  have e1 : (fun w => ph (e.symm w)) = ⇑Complex.reCLM ∘ (fun x => (ph x : ℂ)) ∘ e.symm := by
    funext w; simp
  rw [e1]
  exact h



end

end ChartWirtingerDerivatives

end ReciprocityTheory.L2DbarEstimates
