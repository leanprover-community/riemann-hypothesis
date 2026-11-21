import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyAlt
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.InvariantPolynomialEqAevalPairings
import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TotalDegreeLinear
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.Imports
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.Assembly
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.CycAvg
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.SecLine

section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.FFTSteps

theorem stable_eval_sub {ι A B : Type} [Fintype ι] (g h : Matrix ι ι ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) (p : PV ι A B) :
    eval z (sub g h p) = eval (Sum.elim (fun x : ι × A => ∑ j, g x.1 j * z (Sum.inl (j, x.2)))
      (fun y : ι × B => ∑ j, h y.1 j * z (Sum.inr (j, y.2)))) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [sub]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, sub, aeval_X, eval_X]
    congr 1
    rcases v with x | y <;> simp [map_sum]

theorem stable : Stable := by
  intro ι A B _ _ _ _ hA hB p hp
  classical
  set n := Fintype.card ι
  let eι : ι ≃ Fin n := Fintype.equivFin ι
  let eA : A ↪ Fin n := (Fintype.equivFin A).toEmbedding.trans (Fin.castLEEmb hA)
  let eB : B ↪ Fin n := (Fintype.equivFin B).toEmbedding.trans (Fin.castLEEmb hB)
  let f : (ι × A) ⊕ (ι × B) → Unit × Bool × Fin n × Fin n :=
    Sum.elim (fun x => ((), true, eι x.1, eA x.2)) (fun y => ((), false, eι y.1, eB y.2))
  set q : MvPolynomial (Unit × Bool × Fin n × Fin n) ℂ := rename f p with hq
  have hinv : ∀ u : Unit → Matrix (Fin n) (Fin n) ℂ, (∀ t, u t ∈ Matrix.unitaryGroup (Fin n) ℂ) →
      ∀ z : Unit × Bool × Fin n × Fin n → ℂ, eval (fun v => ∑ l, (if v.2.1 then u v.1 v.2.2.1 l
        else (starRingEnd ℂ) (u v.1 v.2.2.1 l)) * z (v.1, v.2.1, l, v.2.2.2)) q = eval z q := by
    intro u hu z
    let u' : Matrix ι ι ℂ := (u ()).submatrix eι eι
    have hu' : u' ∈ Matrix.unitaryGroup ι ℂ := by
      rw [Matrix.mem_unitaryGroup_iff]
      have h1 := Matrix.mem_unitaryGroup_iff.1 (hu ())
      simp only [u', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix]
      rw [Matrix.submatrix_mul_equiv, ← Matrix.star_eq_conjTranspose, h1, Matrix.submatrix_one_equiv]
    rw [hq, eval_rename, eval_rename]
    have := congrArg (eval (z ∘ f)) (hp u' hu')
    rw [stable_eval_sub] at this
    rw [← this]
    refine congrArg (fun w => eval w p) ?_
    funext v
    rcases v with ⟨i, a⟩ | ⟨i, b⟩
    · simp only [Function.comp, f, Sum.elim_inl, if_true, u', Matrix.submatrix_apply]
      exact (Equiv.sum_comp eι (fun l => u () (eι i) l * z ((), true, l, eA a))).symm
    · simp only [Function.comp, f, Sum.elim_inr, Bool.false_eq_true, if_false, u', Matrix.submatrix_apply,
        Matrix.map_apply]
      exact (Equiv.sum_comp eι (fun l => (starRingEnd ℂ) (u () (eι i) l) * z ((), false, l, eB b))).symm
  obtain ⟨s, hs⟩ := GlobalTheory.invariant_polynomial_eq_aeval_pairings Unit n n le_rfl q hinv
  let ψF : Unit × Bool × Fin n × Fin n → PV ι A B := fun v =>
    if v.2.1 then (if h : ∃ a, eA a = v.2.2.2 then X (Sum.inl (eι.symm v.2.2.1, h.choose)) else 0)
    else (if h : ∃ b, eB b = v.2.2.2 then X (Sum.inr (eι.symm v.2.2.1, h.choose)) else 0)
  have hψf : ∀ w, ψF (f w) = X w := by
    rintro (⟨i, a⟩ | ⟨i, b⟩)
    · have h : ∃ a', eA a' = eA a := ⟨a, rfl⟩
      simp only [f, Sum.elim_inl, ψF, if_true, dif_pos h, Equiv.symm_apply_apply]
      rw [eA.injective h.choose_spec]
    · have h : ∃ b', eB b' = eB b := ⟨b, rfl⟩
      simp only [f, Sum.elim_inr, ψF, Bool.false_eq_true, if_false, dif_pos h, Equiv.symm_apply_apply]
      rw [eB.injective h.choose_spec]
  have hp' : p = aeval ψF q := by
    rw [hq, aeval_rename]
    have : (ψF ∘ f) = X := funext hψf
    rw [this, aeval_X_left_apply]
  have hgen : ∀ v : Unit × Fin n × Fin n, aeval ψF (∑ k, (X (v.1, false, k, v.2.1) * X (v.1, true, k, v.2.2) :
      MvPolynomial (Unit × Bool × Fin n × Fin n) ℂ)) ∈ pairAlg ι A B := by
    rintro ⟨t, a', b'⟩
    simp only [map_sum, map_mul, aeval_X, ψF, Bool.false_eq_true, if_false, if_true]
    by_cases hb : ∃ b, eB b = a'
    · by_cases ha : ∃ a, eA a = b'
      · simp only [dif_pos hb, dif_pos ha]
        have : (∑ k : Fin n, (X (Sum.inr (eι.symm k, hb.choose)) : PV ι A B) * X (Sum.inl (eι.symm k, ha.choose))) =
            ∑ i, (X (Sum.inl (i, ha.choose)) : PV ι A B) * X (Sum.inr (i, hb.choose)) := by
          rw [← Equiv.sum_comp eι]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Equiv.symm_apply_apply, mul_comm]
        rw [this]
        exact Algebra.subset_adjoin ⟨(ha.choose, hb.choose), rfl⟩
      · simp only [dif_neg ha, mul_zero, Finset.sum_const_zero]
        exact Subalgebra.zero_mem _
    · simp only [dif_neg hb, zero_mul, Finset.sum_const_zero]
      exact Subalgebra.zero_mem _
  rw [hp', hs, ← AlgHom.comp_apply, comp_aeval]
  clear hs hp'
  induction s using MvPolynomial.induction_on with
  | C a => simp only [aeval_C]; exact Subalgebra.algebraMap_mem _ a
  | add x y hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  | mul_X x v hx => rw [map_mul, aeval_X]; exact Subalgebra.mul_mem _ hx (hgen v)

end PositivityTheory.Rg.Sw.FFTSteps
end
end

section
noncomputable section

open MvPolynomial Matrix Complex Filter Topology
open scoped ComplexConjugate ComplexOrder

namespace PositivityTheory.Rg.Sw.FFTSteps

variable {ι A B : Type} [Fintype ι] [DecidableEq ι]

theorem exists_unitary_diagonal_unitary' (g : Matrix ι ι ℂ) (hg : IsUnit g) :
    ∃ (u₁ u₂ : Matrix ι ι ℂ) (a : ι → ℝ), u₁ ∈ Matrix.unitaryGroup ι ℂ ∧
      u₂ ∈ Matrix.unitaryGroup ι ℂ ∧ g = u₁ * diagonal (fun i => cexp (a i)) * u₂ := by
  classical
  have hinj : Function.Injective g.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hg
  have hM : (gᴴ * g).PosDef := Matrix.PosDef.conjTranspose_mul_self g hinj
  have hspec : gᴴ * g = (hM.1.eigenvectorUnitary : Matrix ι ι ℂ) *
      diagonal (fun i => (hM.1.eigenvalues i : ℂ)) * star (hM.1.eigenvectorUnitary : Matrix ι ι ℂ) := by
    have h := hM.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hVmem : (hM.1.eigenvectorUnitary : Matrix ι ι ℂ) ∈ Matrix.unitaryGroup ι ℂ :=
    hM.1.eigenvectorUnitary.2
  generalize (hM.1.eigenvectorUnitary : Matrix ι ι ℂ) = V at hspec hVmem
  have hV1 : star V * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hVmem
  have hV2 : V * star V = 1 := Matrix.mem_unitaryGroup_iff.mp hVmem
  have hlpos : ∀ i, 0 < hM.1.eigenvalues i := fun i => hM.eigenvalues_pos i
  generalize hM.1.eigenvalues = l at hspec hlpos
  set a : ι → ℝ := fun i => Real.log (l i) / 2 with ha
  have hDD : diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)) * diagonal (fun i => cexp (a i)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    simp
  have hDs : star (diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ))) =
      diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)) := by
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    exact Complex.conj_ofReal _
  have hreal : ∀ i, Real.exp (-(a i)) * l i * Real.exp (-(a i)) = 1 := by
    intro i
    have h2 : Real.exp (-(a i)) * Real.exp (-(a i)) = (l i)⁻¹ := by
      rw [← Real.exp_add, show -(a i) + -(a i) = -Real.log (l i) by simp only [ha]; ring,
        Real.exp_neg, Real.exp_log (hlpos i)]
    calc Real.exp (-(a i)) * l i * Real.exp (-(a i))
        = (Real.exp (-(a i)) * Real.exp (-(a i))) * l i := by ring
      _ = 1 := by rw [h2, inv_mul_cancel₀ (hlpos i).ne']
  refine ⟨g * V * diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)), star V, a, ?_, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    calc star (g * V * diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ))) *
          (g * V * diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)))
        = diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)) * (star V * (gᴴ * g) * V) *
            diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)) := by
          rw [star_mul, star_mul, hDs, Matrix.star_eq_conjTranspose g]
          simp only [mul_assoc]
      _ = diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)) * diagonal (fun i => (l i : ℂ)) *
            diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)) := by
          rw [hspec, show star V * (V * diagonal (fun i => (l i : ℂ)) * star V) * V
              = diagonal (fun i => (l i : ℂ)) by
            simp only [← mul_assoc, hV1, one_mul]
            rw [mul_assoc, hV1, mul_one]]
      _ = 1 := by
          rw [diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
          congr 1
          funext i
          exact_mod_cast hreal i
  · exact Unitary.star_mem hVmem
  · rw [mul_assoc (g * V), hDD, mul_one, mul_assoc, hV2, mul_one]

def actZ (g h : Matrix ι ι ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) : (ι × A) ⊕ (ι × B) → ℂ :=
  Sum.elim (fun x => ∑ j, g x.1 j * z (Sum.inl (j, x.2))) (fun y => ∑ j, h y.1 j * z (Sum.inr (j, y.2)))

theorem eval_sub (g h : Matrix ι ι ℂ) (p : PV ι A B) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    eval z (sub g h p) = eval (actZ g h z) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [sub]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    congr 1
    rcases v with x | y
    · simp [sub, actZ]
    · simp [sub, actZ]

omit [DecidableEq ι] in
theorem actZ_mul (g h g' h' : Matrix ι ι ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    actZ (g * g') (h * h') z = actZ g h (actZ g' h' z) := by
  funext v
  rcases v with x | y
  · simp only [actZ, Sum.elim_inl, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  · simp only [actZ, Sum.elim_inr, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm

theorem actZ_diagonal (a b : ι → ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    actZ (diagonal a) (diagonal b) z = Sum.elim (fun x => a x.1 * z (Sum.inl x)) (fun y => b y.1 * z (Sum.inr y)) := by
  funext v
  rcases v with x | y
  · simp [actZ, diagonal_apply]
  · simp [actZ, diagonal_apply]

theorem differentiable_eval' {σ : Type} (p : MvPolynomial σ ℂ) (f : ℂ → σ → ℂ)
    (hf : ∀ v, Differentiable ℂ (fun c => f c v)) :
    Differentiable ℂ (fun c => MvPolynomial.eval (f c) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p v hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (hf v)

theorem eval_inv (p : PV ι A B) (hp : IsInv p) (u : Matrix ι ι ℂ) (hu : u ∈ Matrix.unitaryGroup ι ℂ)
    (z : (ι × A) ⊕ (ι × B) → ℂ) : eval (actZ u (u.map star) z) p = eval z p := by
  rw [← eval_sub, hp u hu]

theorem eval_diag (p : PV ι A B) (hp : IsInv p) (a : ι → ℝ) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    eval (actZ (diagonal fun i => cexp (a i)) (diagonal fun i => cexp (-(a i : ℂ))) z) p = eval z p := by
  set F : ℂ → ℂ := fun c => eval (actZ (diagonal fun i => cexp (c * a i))
    (diagonal fun i => cexp (-(c * a i))) z) p with hF
  have hdiff : Differentiable ℂ F := by
    have hF' : F = fun c => eval (Sum.elim (fun x : ι × A => cexp (c * a x.1) * z (Sum.inl x))
        (fun y : ι × B => cexp (-(c * a y.1)) * z (Sum.inr y))) p := by
      funext c
      simp only [hF, actZ_diagonal]
    rw [hF']
    apply differentiable_eval'
    intro v
    rcases v with x | y
    · simp only [Sum.elim_inl]
      fun_prop
    · simp only [Sum.elim_inr]
      fun_prop
  have himag : ∀ t : ℝ, F (I * t) = eval z p := by
    intro t
    have hs : ∀ i, star (cexp (I * t * a i)) = cexp (-(I * t * a i)) := by
      intro i
      rw [show star (cexp (I * t * a i)) = conj (cexp (I * t * a i)) from rfl, ← Complex.exp_conj]
      congr 1
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    have hu : (diagonal fun i => cexp (I * t * a i)) ∈ Matrix.unitaryGroup ι ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      rw [Pi.star_apply, hs i, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    have hmap : (diagonal fun i => cexp (I * t * a i)).map star =
        diagonal fun i => cexp (-(I * t * a i)) := by
      rw [Matrix.diagonal_map (star_zero _)]
      congr 1
      funext i
      exact hs i
    show eval (actZ (diagonal fun i => cexp (I * t * a i)) (diagonal fun i => cexp (-(I * t * a i))) z) p
      = eval z p
    rw [← hmap]
    exact eval_inv p hp _ hu z
  have hconst : F 1 = eval z p := by
    have han : AnalyticOnNhd ℂ F Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hdiff
    have hg : AnalyticOnNhd ℂ (fun _ : ℂ => eval z p) Set.univ := analyticOnNhd_const
    have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), F w = eval z p := by
      have ht : Tendsto (fun t : ℝ => I * (t : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · have hc : Continuous (fun t : ℝ => I * (t : ℂ)) := by fun_prop
          have h0 : Tendsto (fun t : ℝ => I * (t : ℂ)) (𝓝 0) (𝓝 0) := by simpa using hc.tendsto 0
          exact h0.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with t ht
          simpa [Complex.I_ne_zero] using ht
      exact ht.frequently (Filter.Eventually.frequently (Filter.Eventually.of_forall fun t => himag t))
    exact han.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_univ (Set.mem_univ 0) hfreq
      (Set.mem_univ 1)
  simpa [hF] using hconst

theorem ext : Ext := by
  intro ι A B _ _ _ _ p hp g h hgh
  apply MvPolynomial.funext
  intro z
  have hg : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).mpr (Matrix.isUnit_det_of_right_inverse hgh)
  obtain ⟨u₁, u₂, a, hu₁, hu₂, hfac⟩ := exists_unitary_diagonal_unitary' g hg
  have hcancel : ∀ {P Q : Matrix ι ι ℂ} (X : Matrix ι ι ℂ), P * Q = 1 → P * (Q * X) = X := by
    intro P Q X hPQ
    rw [← mul_assoc, hPQ, one_mul]
  have hu1s : u₁ * u₁ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hu₁
  have hu2s : u₂ * u₂ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hu₂
  have hDD : diagonal (fun i => cexp (a i)) * diagonal (fun i => cexp (-(a i : ℂ))) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hK : g * (u₂ᴴ * diagonal (fun i => cexp (-(a i : ℂ))) * u₁ᴴ) = 1 := by
    rw [hfac]
    simp only [mul_assoc]
    rw [hcancel _ hu2s, hcancel _ hDD, hu1s]
  have hT : hᵀ = u₂ᴴ * diagonal (fun i => cexp (-(a i : ℂ))) * u₁ᴴ := by
    have h1 : hᵀ * g = 1 := _root_.mul_eq_one_comm.mp hgh
    calc hᵀ = hᵀ * (g * (u₂ᴴ * diagonal (fun i => cexp (-(a i : ℂ))) * u₁ᴴ)) := by rw [hK, mul_one]
      _ = _ := by rw [← mul_assoc, h1, one_mul]
  have hct : ∀ M : Matrix ι ι ℂ, Mᴴᵀ = M.map star := by
    intro M
    ext i j
    simp
  have hh : h = u₁.map star * diagonal (fun i => cexp (-(a i : ℂ))) * u₂.map star := by
    rw [← Matrix.transpose_transpose h, hT, Matrix.transpose_mul, Matrix.transpose_mul, hct, hct,
      Matrix.diagonal_transpose, mul_assoc]
  rw [eval_sub, hfac, hh, actZ_mul, actZ_mul, eval_inv p hp u₁ hu₁, eval_diag p hp a,
    eval_inv p hp u₂ hu₂]

end PositivityTheory.Rg.Sw.FFTSteps
end
end

section
noncomputable section

open MeasureTheory MvPolynomial

namespace PositivityTheory.Rg.Sw.FFTSteps

namespace AvgPf

section
variable {ι A B : Type} [Fintype ι]

def actP (g h : Matrix ι ι ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) : (ι × A) ⊕ (ι × B) → ℂ :=
  Sum.elim (fun x => ∑ j, g x.1 j * z (Sum.inl (j, x.2))) (fun y => ∑ j, h y.1 j * z (Sum.inr (j, y.2)))

theorem eval_sub (g h : Matrix ι ι ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) (p : PV ι A B) :
    eval z (sub g h p) = eval (actP g h z) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [sub]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p s hp =>
    rw [map_mul, map_mul, map_mul, hp]
    congr 1
    rcases s with x | y
    · simp [sub, actP, map_sum]
    · simp [sub, actP, map_sum]

theorem actP_actP (g h g' h' : Matrix ι ι ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    actP g h (actP g' h' z) = actP (g * g') (h * h') z := by
  funext s
  rcases s with x | y
  · simp only [actP, Sum.elim_inl, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · simp only [actP, Sum.elim_inr, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    ring

theorem totalDegree_sub_le (g h : Matrix ι ι ℂ) (p : PV ι A B) : (sub g h p).totalDegree ≤ p.totalDegree :=
  _root_.UpperTheory.Reformulated.B.TotalDegreeLinear.main g h p

theorem continuous_coeff_sub {K : Type} [TopologicalSpace K] (g h : K → Matrix ι ι ℂ) (hg : Continuous g)
    (hh : Continuous h) (p : PV ι A B) : ∀ m, Continuous fun k => coeff m (sub (g k) (h k) p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => intro m; simp only [sub, aeval_C, algebraMap_eq]; exact continuous_const
  | add p q hp hq => intro m; simp only [map_add, coeff_add]; exact (hp m).add (hq m)
  | mul_X p s hp =>
    intro m
    rcases s with x | y
    · have e : ∀ k, coeff m (sub (g k) (h k) (p * X (Sum.inl x))) =
          ∑ j, g k x.1 j * coeff m (sub (g k) (h k) p * X (Sum.inl (j, x.2))) := by
        intro k
        simp only [map_mul, sub, aeval_X, Sum.elim_inl, Finset.mul_sum, coeff_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_left_comm, coeff_C_mul]
      simp only [e, coeff_mul_X']
      refine continuous_finsetSum _ fun j _ => ?_
      refine (((continuous_apply j).comp ((continuous_apply x.1).comp hg))).mul ?_
      split_ifs
      · exact hp _
      · exact continuous_const
    · have e : ∀ k, coeff m (sub (g k) (h k) (p * X (Sum.inr y))) =
          ∑ j, h k y.1 j * coeff m (sub (g k) (h k) p * X (Sum.inr (j, y.2))) := by
        intro k
        simp only [map_mul, sub, aeval_X, Sum.elim_inr, Finset.mul_sum, coeff_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_left_comm, coeff_C_mul]
      simp only [e, coeff_mul_X']
      refine continuous_finsetSum _ fun j _ => ?_
      refine (((continuous_apply j).comp ((continuous_apply y.1).comp hh))).mul ?_
      split_ifs
      · exact hp _
      · exact continuous_const

end

abbrev εT (N : ℕ) : Fin N → Bool := fun _ => true

theorem continuous_toMK (N : ℕ) : Continuous fun k : Formalism.REAL.KG (εT N) => Formalism.REAL.toMK k :=
  (Units.continuous_val.comp continuous_subtype_val).comp continuous_subtype_val

theorem toMK_mul (N : ℕ) (k k' : Formalism.REAL.KG (εT N)) :
    Formalism.REAL.toMK (k * k') = Formalism.REAL.toMK k * Formalism.REAL.toMK k' := rfl

theorem map_star_mul {N : ℕ} (a b : Matrix (Fin N) (Fin N) ℂ) : (a * b).map star = a.map star * b.map star := by
  ext i j
  simp [Matrix.mul_apply]

theorem exists_toMK (N : ℕ) (u : Matrix (Fin N) (Fin N) ℂ) (hu : u ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    ∃ k : Formalism.REAL.KG (εT N), Formalism.REAL.toMK k = u := by
  have hJ : Formalism.REAL.Jm (εT N) = 1 := by
    simp [Formalism.REAL.Jm, εT, Matrix.diagonal_one]
  have : u ∈ Formalism.REAL.Kset (εT N) := ⟨hu, by rw [hJ, Matrix.mul_one, Matrix.one_mul]⟩
  rw [← Formalism.REAL.range_toMK] at this
  exact this

theorem isEmbedding_toMK (N : ℕ) : Topology.IsEmbedding (fun k : Formalism.REAL.KG (εT N) => Formalism.REAL.toMK k) :=
  (Formalism.REAL.isClosedEmbeddingMatrix N (εT N)).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal

instance instSCKG (N : ℕ) : SecondCountableTopology (Formalism.REAL.KG (εT N)) := by
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → ℂ))
  exact (isEmbedding_toMK N).isInducing.secondCountableTopology

theorem muK_univ (N : ℕ) : Formalism.REAL.muK (εT N) Set.univ = 1 := by
  have := Measure.haarMeasure_self (G := Formalism.REAL.KG (εT N)) (K₀ := ⊤)
  rw [TopologicalSpace.PositiveCompacts.coe_top] at this
  exact this

theorem map_mul_right_muK (N : ℕ) (g : Formalism.REAL.KG (εT N)) :
    Measure.map (fun x => x * g) (Formalism.REAL.muK (εT N)) = Formalism.REAL.muK (εT N) := by
  have : (Measure.map (fun x => x * g) (Formalism.REAL.muK (εT N))).IsHaarMeasure :=
    Measure.isHaarMeasure_map_mul_right (Formalism.REAL.muK (εT N)) g
  have h := Measure.haarMeasure_unique (Measure.map (fun x => x * g) (Formalism.REAL.muK (εT N))) ⊤
  rw [h, TopologicalSpace.PositiveCompacts.coe_top, Measure.map_apply (measurable_mul_const g) MeasurableSet.univ,
    Set.preimage_univ, muK_univ, one_smul]
  rfl

instance (N : ℕ) : (Formalism.REAL.muK (εT N)).IsMulRightInvariant := ⟨fun g => map_mul_right_muK N g⟩

end AvgPf

open AvgPf in
theorem avg : Avg := by
  classical
  intro N A B _ _ p
  set μ := Formalism.REAL.muK (εT N)
  let F : Formalism.REAL.KG (εT N) → PV (Fin N) A B := fun k =>
    sub (Formalism.REAL.toMK k) ((Formalism.REAL.toMK k).map star) p
  set d := p.totalDegree
  let S : Finset ((Fin N × A) ⊕ (Fin N × B) →₀ ℕ) :=
    ((Finset.univ : Finset ((Fin N × A) ⊕ (Fin N × B) → Fin (d + 1))).image
      (fun f => Finsupp.equivFunOnFinite.symm (fun s => (f s : ℕ)))).filter (fun m => (m.sum fun _ e => e) ≤ d)
  have hsupp : ∀ k, (F k).support ⊆ S := by
    intro k m hm
    have hdeg : (m.sum fun _ e => e) ≤ d := (le_totalDegree hm).trans (totalDegree_sub_le _ _ _)
    refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨fun s => ⟨m s, Nat.lt_succ_of_le ?_⟩, Finset.mem_univ _, ?_⟩, hdeg⟩
    · exact (Finsupp.le_degree ..).trans hdeg
    · ext s; simp
  have hcont : ∀ m, Continuous fun k => coeff m (F k) := fun m =>
    continuous_coeff_sub _ _ (continuous_toMK N)
      (continuous_pi fun i => continuous_pi fun j => continuous_star.comp
        ((continuous_apply j).comp ((continuous_apply i).comp (continuous_toMK N)))) p m
  have hint : ∀ m, Integrable (fun k => coeff m (F k)) μ := fun m =>
    integrableOn_univ.1 ((hcont m).continuousOn.integrableOn_compact isCompact_univ)
  let P : PV (Fin N) A B := ∑ m ∈ S, monomial m (∫ k, coeff m (F k) ∂μ)
  have hF : ∀ k, F k = ∑ m ∈ S, monomial m (coeff m (F k)) := by
    intro k
    conv_lhs => rw [(F k).as_sum]
    exact Finset.sum_subset (hsupp k) fun m _ hm => by rw [notMem_support_iff.1 hm, monomial_zero]
  have heval : ∀ z, eval z P = ∫ k, eval z (F k) ∂μ := by
    intro z
    have e : ∀ k, eval z (F k) = ∑ m ∈ S, coeff m (F k) * (m.prod fun n e => z n ^ e) := by
      intro k
      conv_lhs => rw [hF k]
      simp only [map_sum, eval_monomial]
    rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_finsetSum _ (fun m _ => (hint m).mul_const _)]
    simp only [P, map_sum, eval_monomial, integral_mul_const]
  refine ⟨P, ?_, ?_, heval⟩
  · intro u hu
    obtain ⟨ku, hku⟩ := exists_toMK N u hu
    refine MvPolynomial.funext fun z => ?_
    rw [AvgPf.eval_sub, heval, heval]
    have e2 : ∀ k, eval (actP u (u.map star) z) (F k) = eval z (F (k * ku)) := by
      intro k
      simp only [F]
      rw [AvgPf.eval_sub, actP_actP, ← AvgPf.eval_sub, toMK_mul, hku, map_star_mul]
    simp only [e2]
    exact integral_mul_right_eq_self (fun k => eval z (F k)) ku
  · refine totalDegree_finsetSum_le fun m hm => (totalDegree_monomial_le _ _).trans ?_
    exact (Finset.mem_filter.1 hm).2

end PositivityTheory.Rg.Sw.FFTSteps
end
end

section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.FFTSteps.CycF

variable {m n : ℕ} (ε : Fin m → Bool)

abbrev VV (ι : Type) (n : ℕ) := (ι × Fin n) ⊕ (ι × Fin n)

abbrev Rw (β : Bool) := {a : Fin m // ε a = β}

def jv (β : Bool) : VV (Rw ε β) n → Fin m × Fin n × Bool :=
  Sum.elim (fun x => (x.1.1, x.2, false)) (fun x => (x.1.1, x.2, true))

def emb (β : Bool) : PV (Rw ε β) (Fin n) (Fin n) →ₐ[ℂ] PX m n := rename (jv ε β)

def act (u : Matrix (Fin m) (Fin m) ℂ) : PX m n →ₐ[ℂ] PX m n :=
  aeval (fun k : Fin m × Fin n × Bool => if k.2.2 then ∑ b, C (star (u k.1 b)) * X (b, k.2.1, true)
    else ∑ b, C (u k.1 b) * X (b, k.2.1, false))

def blk (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) : Matrix (Fin m) (Fin m) ℂ := fun a b =>
  if ha : ε a = β then (if hb : ε b = β then v ⟨a, ha⟩ ⟨b, hb⟩ else 0) else (if a = b then 1 else 0)

variable {ε}

theorem sum_rw {R : Type*} [AddCommMonoid R] (β : Bool) (F : Rw ε β → R) :
    ∑ b : Fin m, (if h : ε b = β then F ⟨b, h⟩ else 0) = ∑ b : Rw ε β, F b := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun b : Fin m => ε b = β)]
  have h2 : ∑ b : {b : Fin m // ¬ ε b = β}, (if h : ε b.1 = β then F ⟨b.1, h⟩ else 0) = 0 :=
    Finset.sum_eq_zero (fun b _ => dif_neg b.2)
  rw [h2, add_zero]
  exact Finset.sum_congr rfl (fun b _ => by rw [dif_pos b.2])

theorem blk_block (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) (a b : Fin m) (h : ε a ≠ ε b) : blk ε β v a b = 0 := by
  unfold blk
  by_cases ha : ε a = β
  · rw [dif_pos ha, dif_neg (fun hb => h (ha.trans hb.symm))]
  · rw [dif_neg ha, if_neg (fun e : a = b => h (congrArg ε e))]

theorem blk_of (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) {a : Fin m} (ha : ε a = β) (b : Fin m) :
    blk ε β v a b = if hb : ε b = β then v ⟨a, ha⟩ ⟨b, hb⟩ else 0 := by
  unfold blk; rw [dif_pos ha]

theorem blk_of_not (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) {a : Fin m} (ha : ¬ ε a = β) (b : Fin m) :
    blk ε β v a b = if a = b then 1 else 0 := by
  unfold blk; rw [dif_neg ha]

theorem blk_unitary (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) (hv : v ∈ Matrix.unitaryGroup (Rw ε β) ℂ) :
    blk ε β v ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hv ⊢
  ext a c
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.star_apply]
  by_cases ha : ε a = β
  · by_cases hc : ε c = β
    · have key := congrFun (congrFun hv ⟨a, ha⟩) ⟨c, hc⟩
      rw [Matrix.mul_apply, Matrix.one_apply] at key
      simp only [Matrix.star_apply] at key
      have e1 : ∀ b, blk ε β v a b * star (blk ε β v c b) =
          if h : ε b = β then v ⟨a, ha⟩ ⟨b, h⟩ * star (v ⟨c, hc⟩ ⟨b, h⟩) else 0 := by
        intro b
        rw [blk_of β v ha, blk_of β v hc]
        by_cases hb : ε b = β
        · rw [dif_pos hb, dif_pos hb, dif_pos hb]
        · rw [dif_neg hb, dif_neg hb, dif_neg hb, zero_mul]
      rw [Finset.sum_congr rfl (fun b _ => e1 b), sum_rw β (fun j => v ⟨a, ha⟩ j * star (v ⟨c, hc⟩ j)), key]
      by_cases hac : a = c
      · subst hac; simp
      · rw [if_neg (fun h => hac (congrArg Subtype.val h)), if_neg hac]
    · have e1 : ∀ b, blk ε β v a b * star (blk ε β v c b) = if c = b then blk ε β v a b else 0 := by
        intro b
        rw [blk_of_not β v hc b]
        by_cases hcb : c = b
        · rw [if_pos hcb, if_pos hcb, star_one, mul_one]
        · rw [if_neg hcb, if_neg hcb, star_zero, mul_zero]
      rw [Finset.sum_congr rfl (fun b _ => e1 b), Finset.sum_ite_eq]
      simp only [Finset.mem_univ, if_true]
      rw [blk_block β v a c (by rw [ha]; exact fun h => hc h.symm), if_neg (by rintro rfl; exact hc ha)]
  · have e1 : ∀ b, blk ε β v a b * star (blk ε β v c b) = if a = b then star (blk ε β v c b) else 0 := by
      intro b
      rw [blk_of_not β v ha b]
      by_cases hab : a = b
      · rw [if_pos hab, if_pos hab, one_mul]
      · rw [if_neg hab, if_neg hab, zero_mul]
    rw [Finset.sum_congr rfl (fun b _ => e1 b), Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    by_cases hc : ε c = β
    · rw [blk_block β v c a (by rw [hc]; exact fun h => ha h.symm), star_zero,
        if_neg (by rintro rfl; exact ha hc)]
    · rw [blk_of_not β v hc a]
      by_cases hca : c = a
      · subst hca; simp
      · rw [if_neg hca, star_zero, if_neg (fun h => hca h.symm)]

end PositivityTheory.Rg.Sw.FFTSteps.CycF
end
end

section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.FFTSteps.CycF

variable {m n : ℕ} {ε : Fin m → Bool}

theorem sum_blk (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) (a : Rw ε β) (i : Fin n) (t : Bool) :
    ∑ b, C (blk ε β v a.1 b) * (X (b, i, t) : PX m n) = ∑ j : Rw ε β, C (v a j) * X (j.1, i, t) := by
  rw [← sum_rw β (fun j => C (v a j) * (X (j.1, i, t) : PX m n))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [blk_of β v a.2]
  split_ifs <;> simp

theorem sum_blk_star (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) (a : Rw ε β) (i : Fin n) (t : Bool) :
    ∑ b, C (star (blk ε β v a.1 b)) * (X (b, i, t) : PX m n) = ∑ j : Rw ε β, C (star (v a j)) * X (j.1, i, t) := by
  rw [← sum_rw β (fun j => C (star (v a j)) * (X (j.1, i, t) : PX m n))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [blk_of β v a.2]
  split_ifs <;> simp

theorem sum_blk_other (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) {a : Fin m} (ha : ¬ ε a = β) (i : Fin n)
    (t : Bool) (st : Bool) :
    ∑ b, C (if st then star (blk ε β v a b) else blk ε β v a b) * (X (b, i, t) : PX m n) = X (a, i, t) := by
  simp only [blk_of_not β v ha]
  cases st <;> simp [apply_ite star, ite_mul]

theorem act_emb_same (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) :
    (act (n := n) (blk ε β v)).comp (emb ε β) = (emb ε β).comp (sub v (v.map star)) := by
  refine MvPolynomial.algHom_ext fun x => ?_
  rcases x with ⟨i, a⟩ | ⟨i, a⟩
  · simp [act, emb, sub, jv, sum_blk, map_sum]
  · simpa [act, emb, sub, jv, map_sum] using sum_blk_star (n := n) β v i a true

theorem act_emb_other (β β' : Bool) (hne : β' ≠ β) (v : Matrix (Rw ε β) (Rw ε β) ℂ) :
    (act (n := n) (blk ε β v)).comp (emb ε β') = emb ε β' := by
  refine MvPolynomial.algHom_ext fun x => ?_
  rcases x with ⟨i, a⟩ | ⟨i, a⟩
  · have hi : ¬ ε i.1 = β := fun h => hne (i.2.symm.trans h)
    have := sum_blk_other (n := n) β v hi a false false
    simp only [Bool.false_eq_true, if_false] at this
    simp [act, emb, jv, this]
  · have hi : ¬ ε i.1 = β := fun h => hne (i.2.symm.trans h)
    have := sum_blk_other (n := n) β v hi a true true
    simp only [if_true] at this
    simpa [act, emb, jv] using this

theorem emb_pair (β : Bool) (a b : Fin n) :
    emb ε β (∑ i : Rw ε β, (X (Sum.inl (i, a)) : PV (Rw ε β) (Fin n) (Fin n)) * X (Sum.inr (i, b))) = Qb ε β b a := by
  simp only [map_sum, map_mul, emb, rename_X, jv, Sum.elim_inl, Sum.elim_inr, Qb]
  rw [Finset.sum_subtype (Finset.univ.filter (fun x : Fin m => ε x = β)) (p := fun x => ε x = β) (by simp)]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem emb_pairAlg (β : Bool) {p : PV (Rw ε β) (Fin n) (Fin n)} (hp : p ∈ pairAlg (Rw ε β) (Fin n) (Fin n)) :
    emb ε β p ∈ Algebra.adjoin ℂ (Set.range fun k : Bool × Fin n × Fin n => (Qb ε k.1 k.2.1 k.2.2 : PX m n)) := by
  have h1 : emb ε β p ∈ (pairAlg (Rw ε β) (Fin n) (Fin n)).map (emb ε β) := Subalgebra.mem_map.2 ⟨p, hp, rfl⟩
  rw [pairAlg, AlgHom.map_adjoin] at h1
  refine Algebra.adjoin_mono ?_ h1
  rintro _ ⟨_, ⟨⟨a, b⟩, rfl⟩, rfl⟩
  exact ⟨(β, b, a), (emb_pair β a b).symm⟩

end PositivityTheory.Rg.Sw.FFTSteps.CycF
end
end

section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.FFTSteps.CycF

variable {m n : ℕ} (ε : Fin m → Bool)

def eqv : Fin m × Fin n × Bool ≃ VV (Rw ε false) n ⊕ VV (Rw ε true) n where
  toFun k := if h : ε k.1 = true then Sum.inr (if k.2.2 then Sum.inr (⟨k.1, h⟩, k.2.1) else Sum.inl (⟨k.1, h⟩, k.2.1))
    else Sum.inl (if k.2.2 then Sum.inr (⟨k.1, by simpa using h⟩, k.2.1) else Sum.inl (⟨k.1, by simpa using h⟩, k.2.1))
  invFun := Sum.elim (jv ε false) (jv ε true)
  left_inv k := by
    obtain ⟨a, i, t⟩ := k
    by_cases h : ε a = true <;> cases t <;> simp [h, jv]
  right_inv x := by
    rcases x with (⟨⟨a, ha⟩, i⟩ | ⟨⟨a, ha⟩, i⟩) | (⟨⟨a, ha⟩, i⟩ | ⟨⟨a, ha⟩, i⟩) <;> simp [jv, ha]

def Th : PX m n ≃ₐ[ℂ] MvPolynomial (VV (Rw ε false) n) (PV (Rw ε true) (Fin n) (Fin n)) :=
  (renameEquiv ℂ (eqv ε)).trans (sumAlgEquiv ℂ _ _)

variable {ε}

theorem th_X (k : Fin m × Fin n × Bool) : Th ε (X k) = sumAlgEquiv ℂ _ _ (X (eqv ε k)) := by
  simp [Th]

theorem th_embT (c : PV (Rw ε true) (Fin n) (Fin n)) : Th ε (emb ε true c) = C c := by
  induction c using MvPolynomial.induction_on with
  | C a =>
    simp [emb, Th]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    have e : eqv ε (jv ε true v) = Sum.inr v := (eqv ε).apply_symm_apply (Sum.inr v)
    have hx : Th ε (emb ε true (X v)) = C (X v) := by
      simp only [emb, rename_X]
      rw [th_X, e]
      exact sumRingEquiv_X_inr ℂ _ _ v
    rw [map_mul, map_mul, hp, hx, C_mul]

theorem th_embF (t : PV (Rw ε false) (Fin n) (Fin n)) :
    Th ε (emb ε false t) = map (algebraMap ℂ (PV (Rw ε true) (Fin n) (Fin n))) t := by
  induction t using MvPolynomial.induction_on with
  | C a =>
    simp [emb, Th]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    have e : eqv ε (jv ε false v) = Sum.inl v := (eqv ε).apply_symm_apply (Sum.inl v)
    have hx : Th ε (emb ε false (X v)) = X v := by
      simp only [emb, rename_X]
      rw [th_X, e]
      exact sumRingEquiv_X_inl ℂ _ _ v
    rw [map_mul, map_mul, hp, hx, map_mul, map_X]

theorem th_prod (c : PV (Rw ε true) (Fin n) (Fin n)) (μ : VV (Rw ε false) n →₀ ℕ) :
    Th ε (emb ε true c * emb ε false (monomial μ 1)) = monomial μ c := by
  rw [map_mul, th_embT, th_embF, map_monomial, map_one, C_mul_monomial, mul_one]

theorem decomp (Q : PX m n) :
    Q = ∑ μ ∈ (Th ε Q).support, emb ε true ((Th ε Q).coeff μ) * emb ε false (monomial μ 1) := by
  apply (Th ε).injective
  rw [map_sum]
  simp_rw [th_prod]
  exact (Th ε Q).as_sum

theorem coeff_sum_monomial {σ R : Type*} [CommSemiring R] [DecidableEq σ] (S : Finset (σ →₀ ℕ)) (f : (σ →₀ ℕ) → R) (μ : σ →₀ ℕ) :
    coeff μ (∑ ν ∈ S, monomial ν (f ν)) = if μ ∈ S then f μ else 0 := by
  rw [coeff_sum]
  simp only [coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single μ]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h'
      exact absurd h h'
  · apply Finset.sum_eq_zero
    intro b hb
    have : b ≠ μ := fun e => h (e ▸ hb)
    simp [this]

theorem indep {J : Type} [Fintype J] (b : J → PV (Rw ε true) (Fin n) (Fin n)) (hb : LinearIndependent ℂ b)
    (t : J → PV (Rw ε false) (Fin n) (Fin n)) (h : ∑ j, emb ε true (b j) * emb ε false (t j) = 0) : ∀ j, t j = 0 := by
  have h2 := congrArg (Th ε) h
  rw [map_sum, map_zero] at h2
  simp_rw [map_mul, th_embT, th_embF] at h2
  intro j
  ext μ
  have h3 := congrArg (coeff μ) h2
  rw [coeff_sum, coeff_zero] at h3
  simp_rw [coeff_C_mul, coeff_map] at h3
  have h4 : ∑ i, (coeff μ (t i)) • b i = 0 := by
    rw [← h3]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Algebra.smul_def, mul_comm]
  have := Fintype.linearIndependent_iff.1 hb _ h4 j
  simpa using this

end PositivityTheory.Rg.Sw.FFTSteps.CycF
end
end

section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.FFTSteps.CycF

variable {m n : ℕ} {ε : Fin m → Bool}

theorem coeff_inv (v : Matrix (Rw ε true) (Rw ε true) ℂ) (Q : PX m n) (hQ : act (blk ε true v) Q = Q)
    (μ : VV (Rw ε false) n →₀ ℕ) : sub v (v.map star) ((Th ε Q).coeff μ) = (Th ε Q).coeff μ := by
  classical
  have h1 : act (blk ε true v) Q = ∑ ν ∈ (Th ε Q).support,
      emb ε true (sub v (v.map star) ((Th ε Q).coeff ν)) * emb ε false (monomial ν 1) := by
    conv_lhs => rw [decomp (ε := ε) Q]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun ν _ => ?_)
    rw [map_mul]
    congr 1
    · exact DFunLike.congr_fun (act_emb_same true v) _
    · exact DFunLike.congr_fun (act_emb_other true false (by decide) v) _
  rw [hQ] at h1
  have h2 := congrArg (fun P => coeff μ (Th ε P)) h1
  simp only [map_sum, th_prod, coeff_sum_monomial] at h2
  by_cases hμ : μ ∈ (Th ε Q).support
  · rw [if_pos hμ] at h2
    exact h2.symm
  · have : coeff μ (Th ε Q) = 0 := notMem_support_iff.1 hμ
    rw [this, map_zero]

end PositivityTheory.Rg.Sw.FFTSteps.CycF

namespace PositivityTheory.Rg.Sw.FFTSteps

open CycF

theorem cycFFT : CycFFT := by
  classical
  intro hF m n ε Q hQ
  have hact : ∀ u : Matrix (Fin m) (Fin m) ℂ, u ∈ Matrix.unitaryGroup (Fin m) ℂ → (∀ a b, ε a ≠ ε b → u a b = 0) →
      act (n := n) u Q = Q := hQ
  have hc : ∀ μ, (Th ε Q).coeff μ ∈ pairAlg (Rw ε true) (Fin n) (Fin n) := fun μ =>
    hF _ _ _ ((Th ε Q).coeff μ) (fun u hu => coeff_inv u Q (hact _ (blk_unitary true u hu) (blk_block true u)) μ)
  obtain ⟨bs, hbs, hspan, hli⟩ := exists_linearIndependent ℂ
    ((fun μ => (Th ε Q).coeff μ) '' ((Th ε Q).support : Set _))
  have hfin : bs.Finite := (((Th ε Q).support.finite_toSet).image _).subset hbs
  letI : Fintype bs := hfin.fintype
  have hmem : ∀ μ ∈ (Th ε Q).support, (Th ε Q).coeff μ ∈
      Submodule.span ℂ (Set.range (fun j : bs => (j : PV (Rw ε true) (Fin n) (Fin n)))) := by
    intro μ hμ
    rw [Subtype.range_coe, hspan]
    exact Submodule.subset_span ⟨μ, hμ, rfl⟩
  have hrep : ∀ μ : (Th ε Q).support, ∃ a : bs → ℂ,
      ∑ j, a j • (j : PV (Rw ε true) (Fin n) (Fin n)) = (Th ε Q).coeff μ.1 := fun μ =>
    (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hmem μ.1 μ.2)
  choose a ha using hrep
  let r : bs → PV (Rw ε false) (Fin n) (Fin n) := fun j => ∑ μ : (Th ε Q).support, a μ j • monomial μ.1 1
  have hQ' : Q = ∑ j : bs, emb ε true (j : PV (Rw ε true) (Fin n) (Fin n)) * emb ε false (r j) := by
    conv_lhs => rw [decomp (ε := ε) Q]
    rw [← Finset.sum_coe_sort (Th ε Q).support]
    simp_rw [← ha]
    simp only [r, map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
    exact Finset.sum_comm
  have hr : ∀ j, r j ∈ pairAlg (Rw ε false) (Fin n) (Fin n) := by
    intro j
    refine hF _ _ _ (r j) (fun u hu => ?_)
    have h1 := hact _ (blk_unitary false u hu) (blk_block false u)
    rw [hQ', map_sum] at h1
    have h2 : ∀ i : bs, act (blk ε false u) (emb ε true (i : PV (Rw ε true) (Fin n) (Fin n)) * emb ε false (r i)) =
        emb ε true (i : PV (Rw ε true) (Fin n) (Fin n)) * emb ε false (sub u (u.map star) (r i)) := by
      intro i
      rw [map_mul]
      congr 1
      · exact DFunLike.congr_fun (act_emb_other false true (by decide) u) _
      · exact DFunLike.congr_fun (act_emb_same false u) _
    simp_rw [h2] at h1
    have h3 : ∑ i : bs, emb ε true (i : PV (Rw ε true) (Fin n) (Fin n)) *
        emb ε false (sub u (u.map star) (r i) - r i) = 0 := by
      simp only [map_sub, mul_sub, Finset.sum_sub_distrib]
      rw [h1, sub_self]
    have := indep (fun i : bs => (i : PV (Rw ε true) (Fin n) (Fin n))) hli _ h3 j
    exact sub_eq_zero.1 this
  rw [hQ']
  refine Subalgebra.sum_mem _ (fun j _ => Subalgebra.mul_mem _ ?_ ?_)
  · obtain ⟨μ, hμ, hj⟩ := hbs j.2
    apply emb_pairAlg true
    rw [← hj]
    exact hc μ
  · exact emb_pairAlg false (hr j)

end PositivityTheory.Rg.Sw.FFTSteps
end
end

section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.FFTSteps

namespace PowSpanB

variable {m n : ℕ} (ε : Fin m → Bool)

def lf (b : Matrix (Fin n) (Fin n) ℂ) : PX m n := ∑ i, ∑ j, b i j • (Qp ε j i : PX m n)

theorem lf_eq (b : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) = lf ε b := by
  simp only [lf, C_mul']

theorem lf_add (b c : Matrix (Fin n) (Fin n) ℂ) : lf ε (b + c) = lf ε b + lf ε c := by
  simp only [lf, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem lf_smul (z : ℂ) (b : Matrix (Fin n) (Fin n) ℂ) : lf ε (z • b) = z • lf ε b := by
  simp only [lf, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem lf_single (a b : Fin n) : lf ε (Matrix.single b a (1 : ℂ)) = (Qp ε a b : PX m n) := by
  simp [lf, Matrix.single_apply, ite_smul, ite_and]

def W : Set (PX m n) := {w | ∃ h : Matrix (Fin n) (Fin n) ℂ, h.IsHermitian ∧ w = lf ε h}

def S : Submodule ℂ (PX m n) :=
  Submodule.span ℂ {R | ∃ (b : Matrix (Fin n) (Fin n) ℂ) (k : ℕ), b.IsHermitian ∧
    R = (∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) ^ k}

theorem pow_mem {w : PX m n} (hw : w ∈ W ε) (k : ℕ) : w ^ k ∈ S ε := by
  obtain ⟨h, hh, rfl⟩ := hw
  exact Submodule.subset_span ⟨h, k, hh, by rw [lf_eq]⟩

theorem zero_mem_W : (0 : PX m n) ∈ W ε :=
  ⟨0, Matrix.isHermitian_zero, by simp [lf]⟩

theorem natCast_smul_add_mem_W {w v : PX m n} (hw : w ∈ W ε) (hv : v ∈ W ε) (t : ℕ) : (t : ℂ) • v + w ∈ W ε := by
  obtain ⟨h1, hh1, rfl⟩ := hw
  obtain ⟨h2, hh2, rfl⟩ := hv
  refine ⟨(t : ℂ) • h2 + h1, ?_, by rw [lf_add, lf_smul]⟩
  show Matrix.conjTranspose ((t : ℂ) • h2 + h1) = _
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hh2.eq, hh1.eq]
  simp

theorem herm_decomp (b : Matrix (Fin n) (Fin n) ℂ) : ∃ H1 H2 : Matrix (Fin n) (Fin n) ℂ,
    H1.IsHermitian ∧ H2.IsHermitian ∧ b = H1 + Complex.I • H2 := by
  refine ⟨(1 / 2 : ℂ) • (b + Matrix.conjTranspose b), (-Complex.I / 2) • (b - Matrix.conjTranspose b), ?_, ?_, ?_⟩
  · show Matrix.conjTranspose ((1 / 2 : ℂ) • (b + Matrix.conjTranspose b)) = _
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.smul_apply]
    ring
  · show Matrix.conjTranspose ((-Complex.I / 2) • (b - Matrix.conjTranspose b)) = _
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.smul_apply]
    ring
  · ext i j
    simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
    ring_nf
    rw [Complex.I_sq]
    ring

private theorem coeff_mem_of_forall_natCast_poly_sum_mem {M : Type*} [AddCommGroup M] [Module ℂ M] (T : Submodule ℂ M) (N : ℕ)
    (c : ℕ → M) (h : ∀ t : ℕ, ∑ j ∈ Finset.range (N + 1), ((t : ℂ) ^ j) • c j ∈ T)
    (k : ℕ) (hk : k < N + 1) : c k ∈ T := by
  let V : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ := Matrix.vandermonde (fun t : Fin (N + 1) => ((t : ℕ) : ℂ))
  have hV : IsUnit V.det := by
    refine isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr ?_)
    intro a b hab
    exact Fin.ext (Nat.cast_injective hab)
  have key : ∑ t : Fin (N + 1), (V⁻¹ ⟨k, hk⟩ t) • (∑ j ∈ Finset.range (N + 1), (((t : ℕ) : ℂ) ^ j) • c j) = c k := by
    have e : ∀ t : Fin (N + 1), (∑ j ∈ Finset.range (N + 1), (((t : ℕ) : ℂ) ^ j) • c j)
        = ∑ j : Fin (N + 1), V t j • c j := by
      intro t
      rw [← Fin.sum_univ_eq_sum_range (fun j => (((t : ℕ) : ℂ) ^ j) • c j)]
      simp [V, Matrix.vandermonde_apply]
    simp_rw [e, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have hm : ∀ j : Fin (N + 1), ∑ t : Fin (N + 1), V⁻¹ ⟨k, hk⟩ t * V t j = (V⁻¹ * V) ⟨k, hk⟩ j := by
      intro j
      rw [Matrix.mul_apply]
    simp_rw [hm, Matrix.nonsing_inv_mul _ hV, Matrix.one_apply, ite_smul, one_smul, zero_smul]
    simp
  rw [← key]
  exact Submodule.sum_mem _ (fun t _ => T.smul_mem _ (h t))

theorem core : ∀ l : List (PX m n), (∀ v ∈ l, v ∈ W ε) → ∀ w ∈ W ε, ∀ r : ℕ, l.prod * w ^ r ∈ S ε := by
  intro l
  induction l with
  | nil =>
    intro _ w hw r
    simpa using pow_mem ε hw r
  | cons v l ih =>
    intro hl w hw r
    have hv : v ∈ W ε := hl v (by simp)
    have ih' := ih (fun u hu => hl u (by simp [hu]))
    have h1 : ∀ t : ℕ, ∑ j ∈ Finset.range (r + 1 + 1), ((t : ℂ) ^ j) •
        (l.prod * (v ^ j * w ^ (r + 1 - j) * (((r + 1).choose j : ℕ) : PX m n))) ∈ S ε := by
      intro t
      have := ih' _ (natCast_smul_add_mem_W ε hw hv t) (r + 1)
      convert this using 1
      rw [add_pow, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [smul_pow, smul_mul_assoc, smul_mul_assoc, mul_smul_comm]
    have h2 := coeff_mem_of_forall_natCast_poly_sum_mem (S ε) (r + 1) _ h1 1 (by omega)
    have e : (v :: l).prod * w ^ r = ((r + 1 : ℕ) : ℂ)⁻¹ •
        (l.prod * (v ^ 1 * w ^ (r + 1 - 1) * (((r + 1).choose 1 : ℕ) : PX m n))) := by
      rw [Nat.choose_one_right, pow_one, Nat.add_sub_cancel, List.prod_cons]
      rw [show (((r + 1 : ℕ)) : PX m n) = ((r + 1 : ℕ) : ℂ) • (1 : PX m n) by
        rw [Nat.cast_smul_eq_nsmul, nsmul_one]]
      rw [mul_smul_comm, mul_smul_comm, smul_smul,
        inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero r)), one_smul]
      ring
    rw [e]
    exact (S ε).smul_mem _ h2

private theorem list_prod_mul_span_prod_mem_S : ∀ l : List (PX m n), (∀ x ∈ l, x ∈ Submodule.span ℂ (W ε)) →
    ∀ q : List (PX m n), (∀ v ∈ q, v ∈ W ε) → q.prod * l.prod ∈ S ε := by
  intro l
  induction l with
  | nil =>
    intro _ q hq
    simpa using core ε q hq 0 (zero_mem_W ε) 0
  | cons x l ih =>
    intro hl q hq
    have hx : x ∈ Submodule.span ℂ (W ε) := hl x (by simp)
    have hl' : ∀ y ∈ l, y ∈ Submodule.span ℂ (W ε) := fun y hy => hl y (by simp [hy])
    clear hl
    rw [List.prod_cons]
    induction hx using Submodule.span_induction with
    | mem y hy =>
      have := ih hl' (y :: q) (by
        intro v hv
        rcases List.mem_cons.mp hv with h | h
        · exact h ▸ hy
        · exact hq v h)
      rw [List.prod_cons] at this
      rw [← mul_assoc, mul_comm q.prod y]
      exact this
    | zero => simp
    | add a b _ _ ha hb =>
      rw [add_mul, mul_add]
      exact add_mem ha hb
    | smul z a _ ha =>
      rw [smul_mul_assoc, mul_smul_comm]
      exact (S ε).smul_mem z ha

theorem span_eq :
    (Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => (Qp ε ij.1 ij.2 : PX m n))).toSubmodule = S ε := by
  apply le_antisymm
  · rw [Algebra.adjoin_eq_span]
    refine Submodule.span_le.mpr ?_
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Submonoid.exists_list_of_mem_closure hx
    have := list_prod_mul_span_prod_mem_S ε l (by
      intro y hy
      obtain ⟨⟨a, b⟩, rfl⟩ := hl y hy
      obtain ⟨H1, H2, h1, h2, hb⟩ := herm_decomp (Matrix.single b a (1 : ℂ))
      have e : (Qp ε a b : PX m n) = lf ε H1 + Complex.I • lf ε H2 := by
        rw [← lf_single, hb, lf_add, lf_smul]
      show (Qp ε a b : PX m n) ∈ _
      rw [e]
      exact add_mem (Submodule.subset_span ⟨H1, h1, rfl⟩)
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨H2, h2, rfl⟩))) [] (by simp)
    simpa using this
  · refine Submodule.span_le.mpr ?_
    rintro R ⟨b, k, _, rfl⟩
    show _ ∈ Algebra.adjoin ℂ _
    refine Subalgebra.pow_mem _ (Subalgebra.sum_mem _ (fun i _ => Subalgebra.sum_mem _ (fun j _ => ?_))) k
    refine Subalgebra.mul_mem _ ?_ (Algebra.subset_adjoin ⟨(j, i), rfl⟩)
    rw [← MvPolynomial.algebraMap_eq]
    exact Subalgebra.algebraMap_mem _ _

end PowSpanB

theorem powSpan : PowSpan := fun _ _ ε => PowSpanB.span_eq ε

end PositivityTheory.Rg.Sw.FFTSteps
end
end

section
noncomputable section

open MeasureTheory MvPolynomial Filter Topology

namespace PositivityTheory.Rg.Sw.FFTSteps

variable {m n : ℕ}

theorem gs_eq (c : ℝ) (x : Fin m → Fin n → ℂ) :
    gs c x = ((Real.exp (-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2)) : ℝ) : ℂ) := by
  unfold gs
  rw [Complex.ofReal_exp, Complex.ofReal_neg]

theorem continuous_gs (c : ℝ) : Continuous fun x : Fin m → Fin n → ℂ => gs c x := by
  simp_rw [gs_eq]
  fun_prop

theorem norm_gs (c : ℝ) (x : Fin m → Fin n → ℂ) :
    ‖gs c x‖ = Real.exp (-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2)) := by
  rw [gs_eq, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

theorem gs_half (c : ℝ) (x : Fin m → Fin n → ℂ) : gs c x = gs (c / 2) x * gs (c / 2) x := by
  simp only [gs, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem integrable_gauss1 {c : ℝ} (hc : 0 < c) : Integrable (fun z : ℂ => Real.exp (-(c * ‖z‖ ^ 2))) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (c : ℂ)) (by simpa using hc) 0 0
  refine h.norm.congr (ae_of_all _ fun z => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  norm_cast
  rw [neg_mul]

theorem exp_sum_sum (c : ℝ) (x : Fin m → Fin n → ℂ) :
    Real.exp (-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2)) = ∏ a, ∏ i, Real.exp (-(c * ‖x a i‖ ^ 2)) := by
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]

theorem integrable_gs_row {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : Fin n → ℂ => ∏ i, Real.exp (-(c * ‖y i‖ ^ 2))) := by
  exact Integrable.fintype_prod (f := fun _ z => Real.exp (-(c * ‖z‖ ^ 2))) (fun _ => integrable_gauss1 hc)

set_option maxHeartbeats 1000000 in
theorem integrable_gs_prod {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Fin m → Fin n → ℂ => ∏ a, ∏ i, Real.exp (-(c * ‖x a i‖ ^ 2))) := by
  have h := Integrable.fintype_prod (ι := Fin m) (E := Fin n → ℂ) (μ := fun _ => (volume : Measure (Fin n → ℂ)))
    (f := fun _ y => ∏ i, Real.exp (-(c * ‖y i‖ ^ 2))) (fun _ => integrable_gs_row hc)
  exact h

theorem integrable_gs_re {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Fin m → Fin n → ℂ => Real.exp (-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2))) := by
  exact (integrable_gs_prod hc).congr (ae_of_all _ fun x => (exp_sum_sum c x).symm)

theorem integrable_gs {c : ℝ} (hc : 0 < c) : Integrable (fun x : Fin m → Fin n → ℂ => gs c x) := by
  exact (integrable_gs_re hc).ofReal.congr (ae_of_all _ fun x => (gs_eq c x).symm)

theorem bound_aux {a r S : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (hS : r ^ 2 ≤ S) :
    r * Real.exp (-(a * S)) ≤ 1 + 1 / a := by
  have hS0 : 0 ≤ S := le_trans (sq_nonneg r) hS
  have h1 : 1 + a * S ≤ Real.exp (a * S) := by
    have := Real.add_one_le_exp (a * S)
    linarith
  have hinv : 0 ≤ 1 / a := by positivity
  have haS : 0 ≤ a * S := mul_nonneg ha.le hS0
  have hprod : (1 + 1 / a) * (1 + a * S) = 1 + a * S + 1 / a + S := by
    field_simp
    ring
  have h2 : r ≤ (1 + 1 / a) * (1 + a * S) := by
    rw [hprod]
    nlinarith [sq_nonneg (r - 1)]
  have h3 : r ≤ (1 + 1 / a) * Real.exp (a * S) := by
    have : 0 ≤ 1 + 1 / a := by positivity
    nlinarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  exact h3

theorem sq_le_sum_sum (x : Fin m → Fin n → ℂ) (a : Fin m) (i : Fin n) :
    ‖x a i‖ ^ 2 ≤ ∑ a, ∑ i, ‖x a i‖ ^ 2 := by
  have h1 : ‖x a i‖ ^ 2 ≤ ∑ j, ‖x a j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖x a j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : ∑ j, ‖x a j‖ ^ 2 ≤ ∑ b, ∑ j, ‖x b j‖ ^ 2 :=
    Finset.single_le_sum (f := fun b => ∑ j, ‖x b j‖ ^ 2)
      (fun b _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)) (Finset.mem_univ a)
  exact h1.trans h2

theorem integrable_evX_gs (P : PX m n) : ∀ {c : ℝ}, 0 < c → Integrable (fun x => evX P x * gs c x) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro c hc
    have e : (fun x => evX (C a : PX m n) x * gs c x) = fun x => a * gs c x := by
      funext x
      simp [evX]
    rw [e]
    exact (integrable_gs hc).const_mul a
  | add p q hp hq =>
    intro c hc
    have e : (fun x => evX (p + q) x * gs c x) = fun x => evX p x * gs c x + evX q x * gs c x := by
      funext x
      simp only [evX, map_add, add_mul]
    rw [e]
    exact (hp hc).add (hq hc)
  | mul_X p k hp =>
    intro c hc
    have hc2 : 0 < c / 2 := by positivity
    have e : (fun x => evX (p * X k) x * gs c x) = fun x =>
        ((if k.2.2 = true then star (x k.1 k.2.1) else x k.1 k.2.1) * gs (c / 2) x) *
          (evX p x * gs (c / 2) x) := by
      funext x
      simp only [evX, map_mul, eval_X]
      rw [gs_half c x]
      ring
    rw [e]
    refine (hp hc2).bdd_mul (c := 1 + 1 / (c / 2)) ?_ ?_
    · refine Continuous.aestronglyMeasurable (Continuous.mul ?_ (continuous_gs _))
      by_cases hk : k.2.2 = true
      · simp only [hk, if_true]
        fun_prop
      · simp only [hk, Bool.false_eq_true, if_false]
        fun_prop
    · refine ae_of_all _ fun x => ?_
      have hn : ‖(if k.2.2 = true then star (x k.1 k.2.1) else x k.1 k.2.1)‖ = ‖x k.1 k.2.1‖ := by
        split_ifs <;> simp
      rw [norm_mul, norm_gs, hn]
      exact bound_aux hc2 (norm_nonneg _) (sq_le_sum_sum x k.1 k.2.1)

theorem mom_add {c : ℝ} (hc : 0 < c) (R1 R2 P : PX m n) :
    mom c ((R1 + R2) * P) = mom c (R1 * P) + mom c (R2 * P) := by
  unfold mom
  have h : ∀ x, evX ((R1 + R2) * P) x * gs c x = evX (R1 * P) x * gs c x + evX (R2 * P) x * gs c x := by
    intro x
    simp only [evX, add_mul, map_add]
  simp_rw [h]
  exact integral_add (integrable_evX_gs _ hc) (integrable_evX_gs _ hc)

theorem mom_smul (c : ℝ) (a : ℂ) (R P : PX m n) : mom c ((a • R) * P) = a * mom c (R * P) := by
  unfold mom
  have h : ∀ x, evX ((a • R) * P) x * gs c x = a * (evX (R * P) x * gs c x) := by
    intro x
    simp only [evX, smul_eq_C_mul, map_mul, eval_C]
    ring
  simp_rw [h]
  exact integral_const_mul a _

theorem mom_zero (c : ℝ) (P : PX m n) : mom c (0 * P) = 0 := by
  simp [mom, evX]

theorem evX_ell (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (x : Fin m → Fin n → ℂ) :
    evX (∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) x = (b * gramX ε x).trace := by
  simp only [evX, map_sum, map_mul, MvPolynomial.eval_C, Matrix.trace, Matrix.diag, Matrix.mul_apply, gramX]

theorem ell_mem (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) ∈
      Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => (Qp ε ij.1 ij.2 : PX m n)) := by
  refine Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ ?_ ?_
  · exact Subalgebra.algebraMap_mem _ (b i j)
  · exact Algebra.subset_adjoin ⟨(j, i), rfl⟩

theorem mom_ellpow (ε : Fin m → Bool) (c : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) (P : PX m n) :
    mom c ((∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) ^ k * P) =
      ∫ x : Fin m → Fin n → ℂ, evX P x * gs c x * ((b * gramX ε x).trace) ^ k := by
  unfold mom
  congr 1
  ext x
  have e : evX ((∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) ^ k * P) x =
      (evX (∑ i, ∑ j, C (b i j) * (Qp ε j i : PX m n)) x) ^ k * evX P x := by
    simp only [evX, map_mul, map_pow]
  rw [e, evX_ell]
  ring

theorem strip_open (δ : ℝ) : IsOpen {z : ℂ | |z.im| < δ} :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem strip_conn (δ : ℝ) : IsPreconnected {z : ℂ | |z.im| < δ} := by
  have e : {z : ℂ | |z.im| < δ} = Complex.imLm ⁻¹' Set.Ioo (-δ) δ := by
    ext z; simp [abs_lt]
  rw [e]
  exact ((convex_Ioo (-δ) δ).linear_preimage Complex.imLm).isPreconnected

theorem nullIff_of (hS : SecLine) (hP : PowSpan) : NullIff := by
  intro m n ε c t hc ht P
  constructor
  · intro hN b hb
    obtain ⟨δ, hδ, hd, hre, hder⟩ := hS m n ε c t hc P b hb
    set F : ℂ → ℂ := fun z => ∫ x : Fin m → Fin n → ℂ,
      evX P x * gs c x * Complex.exp (Complex.I * ↑t * z * (b * gramX ε x).trace) with hF
    have hball : Metric.ball (0:ℂ) δ ⊆ {z : ℂ | |z.im| < δ} := by
      intro z hz
      simp only [Metric.mem_ball, dist_zero_right] at hz
      exact lt_of_le_of_lt (Complex.abs_im_le_norm z) hz
    have hzero : ∀ k, iteratedDeriv k F 0 = 0 := by
      intro k
      rw [hder k, ← mom_ellpow, hN _ (Subalgebra.pow_mem _ (ell_mem ε b) k), mul_zero]
    have hloc : F =ᶠ[𝓝 0] 0 := by
      filter_upwards [Metric.ball_mem_nhds (0:ℂ) hδ] with z hz
      rw [← Complex.taylorSeries_eq_on_ball' hz (hd.mono hball)]
      simp [hzero]
    have han : AnalyticOnNhd ℂ F {z : ℂ | |z.im| < δ} := hd.analyticOnNhd (strip_open δ)
    have h0 : (0:ℂ) ∈ {z : ℂ | |z.im| < δ} := by simpa using hδ
    have h1 : (1:ℂ) ∈ {z : ℂ | |z.im| < δ} := by simpa using hδ
    have hF1 := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (strip_conn δ) h0 hloc h1
    have e1 := hre 1 (by simp)
    rw [one_smul] at e1
    rw [← e1]
    exact hF1
  · intro hall R hR
    have hR' : R ∈ Submodule.span ℂ {R : PX m n | ∃ (b : Matrix (Fin n) (Fin n) ℂ) (k : ℕ),
        b.IsHermitian ∧ R = (∑ i : Fin n, ∑ j : Fin n, C (b i j) * Qp ε j i) ^ k} := by
      rw [← hP m n ε]
      exact hR
    clear hR
    induction hR' using Submodule.span_induction with
    | mem R hmem =>
      obtain ⟨b, k, hb, rfl⟩ := hmem
      obtain ⟨δ, hδ, hd, hre, hder⟩ := hS m n ε c t hc P b hb
      set F : ℂ → ℂ := fun z => ∫ x : Fin m → Fin n → ℂ,
        evX P x * gs c x * Complex.exp (Complex.I * ↑t * z * (b * gramX ε x).trace) with hF
      have han : AnalyticOnNhd ℂ F {z : ℂ | |z.im| < δ} := hd.analyticOnNhd (strip_open δ)
      have h0 : (0:ℂ) ∈ {z : ℂ | |z.im| < δ} := by simpa using hδ
      have hreal : ∀ r : ℝ, F r = 0 := by
        intro r
        rw [show F r = _ from hre (r:ℂ) (Complex.ofReal_im r)]
        apply hall
        unfold Matrix.IsHermitian
        rw [Matrix.conjTranspose_smul, hb.eq, Complex.star_def, Complex.conj_ofReal]
      have hfreq : ∃ᶠ z in 𝓝[≠] (0:ℂ), F z = 0 := by
        have hc0 : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝 0) (𝓝 0) := by
          simpa using Complex.continuous_ofReal.tendsto (0:ℝ)
        have hT : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
          refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
            (hc0.mono_left nhdsWithin_le_nhds) ?_
          filter_upwards [self_mem_nhdsWithin] with r hr
          simpa using hr
        exact hT.frequently (Frequently.of_forall hreal)
      have hloc := ((han 0 h0).frequently_zero_iff_eventually_zero).mp hfreq
      have hk := hder k
      rw [Filter.EventuallyEq.iteratedDeriv_eq k (hloc : F =ᶠ[𝓝 0] 0)] at hk
      simp at hk
      rw [mom_ellpow]
      exact hk.resolve_left (fun h => ht h.1)
    | zero => exact mom_zero c P
    | add x y _ _ hx hy => rw [mom_add hc, hx, hy, add_zero]
    | smul a x _ hx => rw [mom_smul, hx, mul_zero]

end PositivityTheory.Rg.Sw.FFTSteps
end
end

section
namespace PositivityTheory.Rg.Sw

open FFTSteps

theorem fft : FFT := assembly stable ext avg pos

theorem cyc_of (h : FFT) : Cyc := fun m n ε c hc P => by
  obtain ⟨Q, hQ, hPQ⟩ := cycAvg m n ε c hc P
  exact ⟨Q, cycFFT h m n ε Q hQ, hPQ⟩

theorem nullIff : NullIff := nullIff_of secLine powSpan

end PositivityTheory.Rg.Sw
end
