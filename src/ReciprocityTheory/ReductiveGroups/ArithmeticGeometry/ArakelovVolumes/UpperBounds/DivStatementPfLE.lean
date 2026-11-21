import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStatementPfLB

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Asymptotics ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem nmat_zero' (τ : X.Ψ) : mat (nmat X (0 : V (nd X))) τ = 1 := by
  ext a b
  by_cases h : b < a
  · have hab : a ≠ b := by rintro rfl; exact lt_irrefl _ h
    simp [mat, nmat, h, hab, Matrix.one_apply]
    rfl
  · by_cases hab : a = b
    · subst hab; simp [mat, nmat]
    · simp [mat, nmat, h, hab, Matrix.one_apply]

theorem cpt_zero' (x0 : Frame X.Ψ r) : cpt X x0 0 = x0 := by
  funext τ
  show mat x0 τ * mat (nmat X (0 : V (nd X))) τ = x0 τ
  rw [nmat_zero', mul_one]
  rfl

theorem nmat_zero_mem : nmat X (0 : V (nd X)) ∈ Bor X.Ψ r := by
  simp only [Bor, Set.mem_setOf_eq]
  intro τ
  refine ⟨?_, fun a c hca => ?_⟩
  · rw [nmat_zero']; simp
  · simp [nmat, hca]
    rfl

theorem lact_one' (y : Frame X.Ψ r) : lact (1 : GL (Fin r) E) y = y := by
  funext τ
  simp only [lact, Units.val_one]
  rw [Matrix.map_one _ (map_zero _) (map_one _), one_mul]
  rfl

theorem s_xs_zero {Xa : ArchInM X} (Fl : FlatM X Xa) (j : Fin Fl.δ) (k : Fin (nd X)) :
    Fl.s k (Fl.xs j) = 0 := by
  have he : Fl.xs j = lact (1 : GL (Fin r) E) (rmul (Fl.xs j) (nmat X 0)) := by
    rw [lact_one']
    exact (cpt_zero' X (Fl.xs j)).symm
  exact (Fl.S_eq (Fl.xs j) (Fl.xs_mem j)).mpr ⟨j, 1, X.Γ.one_mem, nmat X 0, nmat_zero_mem X, he⟩ k

theorem anal_loc {P : Frame X.Ψ r → ℂ} (hP : DifferentiableOn ℂ P X.dom) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) : AnalyticAt ℂ (fun z => P (cpt X x z)) 0 := by
  have hc := OntoB.cd_cpt X x
  have hU : IsOpen {z : V (nd X) | cpt X x z ∈ X.dom} :=
    (FourierCoefficientDomain.isOpen_dom X).preimage hc.continuous
  refine DivLA.analyticAt_of_diffOn hU ?_ (by simpa [cpt_zero'] using hx)
  exact hP.comp (hc.differentiable (by simp)).differentiableOn (fun z hz => hz)


end

end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Asymptotics

noncomputable section

variable {n : ℕ}

theorem comp_O (L : V n ≃L[ℂ] V n) (k : Fin n) :
    (fun z : V n => (L z) k) =O[𝓝 0] fun z => ‖z‖ := by
  have h1 : (fun z : V n => L z) =O[𝓝 0] fun z => z := (L : V n →L[ℂ] V n).isBigO_id _
  have h2 : (fun z : V n => (L z) k) =O[𝓝 0] fun z => L z := by
    refine IsBigO.of_bound 1 (Filter.Eventually.of_forall fun z => ?_)
    rw [one_mul]
    first
      | exact norm_le_pi_norm (L z) k
      | exact PiLp.norm_apply_le (L z) k
      | simpa using norm_le_pi_norm (L z) k
  exact (h2.trans h1).trans (isBigO_norm_right.mpr (isBigO_refl _ _))

theorem sub_val_O {g : V n → ℂ} (hg : AnalyticAt ℂ g 0) :
    (fun z => g 0 - g z) =O[𝓝 0] fun z => ‖z‖ ^ 1 := by
  have h := hg.differentiableAt.hasFDerivAt.isBigO_sub
  simp only [sub_zero] at h
  have h2 := h.neg_left
  simp only [neg_sub] at h2
  simp only [pow_one]
  exact h2.trans (isBigO_norm_right.mpr (isBigO_refl _ _))

theorem local_step {δ T d : ℕ} (hd : d ≤ T) (W : V n → ℂ) (S : Fin n → V n → ℂ)
    (Tt : Fin δ → V n → ℂ) (L : V n ≃L[ℂ] V n)
    (hW : AnalyticAt ℂ W 0) (hW0 : W 0 ≠ 0) (hS : ∀ k, AnalyticAt ℂ (S k) 0) (hS0 : ∀ k, S k 0 = 0)
    (hT : ∀ k, AnalyticAt ℂ (Tt k) 0)
    (hL : ∀ k z, (L z) k = fderiv ℂ (fun y => S k y / W y) 0 z)
    (G : V n → ℂ) (hG : AnalyticAt ℂ G 0) (hGO : G =O[𝓝 0] fun z => ‖z‖ ^ d) :
    ∃ a : (Fin n → ℕ) → ℂ, ∀ c : (Fin n → ℕ) → Fin δ → ℂ,
      (∀ α ∈ Finset.Nat.antidiagonalTuple n d, ∑ k, c α k * Tt k 0 * W 0 ^ T = a α) →
      (fun z => G z - ∑ α ∈ Finset.Nat.antidiagonalTuple n d,
        ∑ k, c α k * (∏ i, S i z ^ α i) * W z ^ (T - d) * Tt k z) =O[𝓝 0]
        fun z => ‖z‖ ^ (d + 1) := by
  obtain ⟨q, hq⟩ := taylor_step hG hGO
  obtain ⟨a, ha⟩ := multilinear_expand q L
  refine ⟨a, fun c hc => ?_⟩
  have hWev : ∀ᶠ z in 𝓝 (0 : V n), W z ≠ 0 := hW.continuousAt.eventually_ne hW0
  have hφan : ∀ i, AnalyticAt ℂ (fun y => S i y / W y) 0 := fun i => (hS i).div hW hW0
  have hφℓ : ∀ i, (fun z => S i z / W z - (L z) i) =O[𝓝 0] fun z => ‖z‖ ^ 2 := by
    intro i
    exact (taylor2 (hφan i)).congr' (Filter.Eventually.of_forall fun z => by
      simp only [hS0 i, zero_div, sub_zero, ← hL i z]) Filter.EventuallyEq.rfl
  have hℓO : ∀ i, (fun z => (L z) i) =O[𝓝 0] fun z => ‖z‖ := fun i => comp_O L i
  have hφO : ∀ i, (fun z => S i z / W z) =O[𝓝 0] fun z => ‖z‖ := by
    intro i
    have h2 : (fun z => S i z / W z - (L z) i) =O[𝓝 0] fun z => ‖z‖ :=
      ((hφℓ i).trans (isBigO_norm_pow_of_le (F := V n) (by norm_num : 1 ≤ 2))).congr'
        Filter.EventuallyEq.rfl (Filter.Eventually.of_forall fun z => pow_one _)
    exact (h2.add (hℓO i)).congr' (Filter.Eventually.of_forall fun z => sub_add_cancel _ _)
      Filter.EventuallyEq.rfl
  have hprodO : ∀ u : Fin n → V n → ℂ, (∀ i, u i =O[𝓝 0] fun z => ‖z‖) →
      ∀ (e : Fin n → ℕ) (s : Finset (Fin n)),
        (fun z => ∏ i ∈ s, u i z ^ e i) =O[𝓝 0] fun z => ‖z‖ ^ (∑ i ∈ s, e i) := by
    intro u hu e s
    induction s using Finset.induction_on with
    | empty =>
      exact (isBigO_const_const (1 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0) (𝓝 (0 : V n))).congr'
        (Filter.Eventually.of_forall fun z => by simp) (Filter.Eventually.of_forall fun z => by simp)
    | insert a s ha ih =>
      refine (((hu a).pow (e a)).mul ih).congr' (Filter.Eventually.of_forall fun z => ?_)
        (Filter.Eventually.of_forall fun z => ?_)
      · simp only [Finset.prod_insert ha]
      · simp only [Finset.sum_insert ha, pow_add]
  have hsplit : (fun z => G z - ∑ α ∈ Finset.Nat.antidiagonalTuple n d,
        ∑ k, c α k * (∏ i, S i z ^ α i) * W z ^ (T - d) * Tt k z) =
      fun z => (G z - q (fun _ => z)) + ∑ α ∈ Finset.Nat.antidiagonalTuple n d,
        (a α * ∏ k, (L z) k ^ α k - ∑ k, c α k * (∏ i, S i z ^ α i) * W z ^ (T - d) * Tt k z) := by
    funext z
    rw [Finset.sum_sub_distrib, ← ha z]
    ring
  have hsum : ∀ α ∈ Finset.Nat.antidiagonalTuple n d,
      (fun z => a α * ∏ k, (L z) k ^ α k -
        ∑ k, c α k * (∏ i, S i z ^ α i) * W z ^ (T - d) * Tt k z) =O[𝓝 0]
        fun z => ‖z‖ ^ (d + 1) := by
    intro α hα
    have hsumα : ∑ i, α i = d := Finset.Nat.mem_antidiagonalTuple.mp hα
    have hsumAn : AnalyticAt ℂ (fun z => ∑ k, c α k * Tt k z) 0 := by
      have hfun : (fun z => ∑ k, c α k * Tt k z) = ∑ k, fun z => c α k * Tt k z := by
        funext z
        simp [Finset.sum_apply]
      rw [hfun]
      exact Finset.analyticAt_sum Finset.univ fun k _ => analyticAt_const.mul (hT k)
    have hH : AnalyticAt ℂ (fun z => W z ^ T * ∑ k, c α k * Tt k z) 0 := by
      exact (hW.pow T).mul hsumAn
    have hH0 : W 0 ^ T * ∑ k, c α k * Tt k 0 = a α := by
      rw [← hc α hα, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hdiffH := sub_val_O hH
    have hP := prod_pow_sub Finset.univ (fun i z => (L z) i) (fun i z => S i z / W z) α hℓO hφO
      (fun i => (hφℓ i).neg_left.congr' (Filter.Eventually.of_forall fun z => by
        first
        | ring
        | (simp only []; ring)) Filter.EventuallyEq.rfl)
    have hφα := hprodO (fun i z => S i z / W z) hφO α Finset.univ
    have hmain : (fun z => a α * (∏ i, (L z) i ^ α i - ∏ i, (S i z / W z) ^ α i) +
        (∏ i, (S i z / W z) ^ α i) *
          (W 0 ^ T * ∑ k, c α k * Tt k 0 - W z ^ T * ∑ k, c α k * Tt k z)) =O[𝓝 0]
        fun z => ‖z‖ ^ (d + 1) := by
      refine IsBigO.add ?_ ?_
      · exact (hP.const_mul_left (a α)).congr' (Filter.Eventually.of_forall fun z => rfl)
          (Filter.Eventually.of_forall fun z => by simp only [hsumα])
      · exact (hφα.mul hdiffH).congr' (Filter.Eventually.of_forall fun z => rfl)
          (Filter.Eventually.of_forall fun z => by
            simp only [pow_one]
            rw [← pow_succ, hsumα])
    refine hmain.congr' (hWev.mono fun z hz => ?_) Filter.EventuallyEq.rfl
    have hSz : ∏ i, S i z ^ α i = (∏ i, (S i z / W z) ^ α i) * W z ^ d := by
      rw [← hsumα, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← mul_pow, div_mul_cancel₀ _ hz]
    have hWT : W z ^ T = W z ^ d * W z ^ (T - d) := by
      rw [← pow_add, Nat.add_sub_cancel' hd]
    have hsumk : ∑ k, c α k * ((∏ i, (S i z / W z) ^ α i) * W z ^ d) * W z ^ (T - d) * Tt k z =
        (∏ i, (S i z / W z) ^ α i) * (W z ^ T * ∑ k, c α k * Tt k z) := by
      rw [hWT, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    beta_reduce
    rw [hH0, hSz, hsumk]
    ring
  rw [hsplit]
  exact hq.add ((IsBigO.sum hsum).congr'
    (Filter.Eventually.of_forall fun z => by simp only [Finset.sum_apply]) Filter.EventuallyEq.rfl)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
end

section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
  Asymptotics ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ContDiff ENNReal Matrix

noncomputable section

theorem coordL {n : ℕ} (W : V n → ℂ) (S : Fin n → V n → ℂ) (hW : AnalyticAt ℂ W 0) (hW0 : W 0 ≠ 0)
    (hS : ∀ k, AnalyticAt ℂ (S k) 0) (hS0 : ∀ k, S k 0 = 0)
    (hdet : (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => S k z / W z : V n)) 0).det ≠ 0) :
    ∃ L : V n ≃L[ℂ] V n, (∀ k z, (L z) k = fderiv ℂ (fun y => S k y / W y) 0 z) ∧
      (fun z => (WithLp.toLp 2 fun k => S k z / W z : V n) - L z) =o[𝓝 0] fun z => z := by
  classical
  let F : V n → V n := fun z => (WithLp.toLp 2 fun k => S k z / W z : V n)
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)
  have hcomp : ∀ k, DifferentiableAt ℂ (fun y => S k y / W y) 0 :=
    fun k => ((hS k).div hW hW0).differentiableAt
  have hG : DifferentiableAt ℂ (fun z k => S k z / W z) 0 := differentiableAt_pi.2 hcomp
  have hFd : DifferentiableAt ℂ F 0 := e.symm.differentiableAt.comp 0 hG
  have hdet' : LinearMap.det (fderiv ℂ F 0 : V n →ₗ[ℂ] V n) ≠ 0 := hdet
  let L : V n ≃L[ℂ] V n :=
    (LinearMap.equivOfDetNeZero (fderiv ℂ F 0 : V n →ₗ[ℂ] V n) hdet').toContinuousLinearEquiv
  have hL : ∀ z, L z = fderiv ℂ F 0 z := fun z => rfl
  refine ⟨L, fun k z => ?_, ?_⟩
  · rw [hL]
    have h1' := ((PiLp.proj 2 (fun _ : Fin n => ℂ) k).hasFDerivAt (x := F 0)).comp (0 : V n) hFd.hasFDerivAt
    have h1 : HasFDerivAt (fun y => S k y / W y)
        ((PiLp.proj 2 (fun _ : Fin n => ℂ) k).comp (fderiv ℂ F 0)) 0 := h1'
    rw [h1.fderiv]
    rfl
  · have h2 := hFd.hasFDerivAt.isLittleO
    have hF0 : F 0 = 0 := by
      apply PiLp.ext
      intro k
      simp [F, hS0]
    simp only [hF0, sub_zero] at h2
    exact h2

variable {E : Type} [Field E] [NumberField E] [IsCMField E]




end

end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLC
end
