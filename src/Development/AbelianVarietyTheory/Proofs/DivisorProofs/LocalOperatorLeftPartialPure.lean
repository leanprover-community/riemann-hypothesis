import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductMemSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthProdMkConst
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSeminormTranslateSubLineDerivLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFunctionFactorizableSum

section
section
open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp

namespace GlobalTheory.SchwartzFstOp

theorem norm_iteratedFDeriv_sliceCLM_le {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V'] (f : 𝓢(V × V', ℂ)) (x' : V') (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (sliceCLM x' f) x‖ ≤ ‖iteratedFDeriv ℝ n f (x, x')‖ := by
  have e : (⇑(sliceCLM x' f) : V → ℂ) =
      (fun q => f (q + ((0 : V), x'))) ∘ (ContinuousLinearMap.inl ℝ V V') := by
    funext y; simp
  have hc : ContDiff ℝ n (fun q : V × V' => f (q + ((0 : V), x'))) :=
    ((f.smooth ⊤).comp (contDiff_id.add contDiff_const)).of_le (by exact_mod_cast le_top)
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hc _ le_rfl, iteratedFDeriv_comp_add_right]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ∏ _i : Fin n, ‖ContinuousLinearMap.inl ℝ V V'‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_inl_le_one ℝ V V')
  have h2 : (ContinuousLinearMap.inl ℝ V V') x + ((0 : V), x') = (x, x') := by simp
  rw [h2]
  exact (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans (le_of_eq (mul_one _))

theorem norm_pow_mul_seminorm_sliceCLM_le {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V'] (f : 𝓢(V × V', ℂ)) (x' : V') (j k n : ℕ) :
    ‖x'‖ ^ k * SchwartzMap.seminorm ℂ j n (sliceCLM x' f) ≤ SchwartzMap.seminorm ℂ (j + k) n f := by
  set M := SchwartzMap.seminorm ℂ (j + k) n f
  have hM : 0 ≤ M := apply_nonneg _ _
  have hpt : ∀ x : V, ‖x'‖ ^ k * (‖x‖ ^ j * ‖iteratedFDeriv ℝ n (sliceCLM x' f) x‖) ≤ M := by
    intro x
    have hw : ‖x'‖ ^ k * ‖x‖ ^ j ≤ ‖(x, x')‖ ^ (j + k) := by
      rw [pow_add, mul_comm]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (norm_fst_le (x, x')) _)
        (pow_le_pow_left₀ (norm_nonneg _) (norm_snd_le (x, x')) _) (by positivity) (by positivity)
    calc ‖x'‖ ^ k * (‖x‖ ^ j * ‖iteratedFDeriv ℝ n (sliceCLM x' f) x‖)
        = (‖x'‖ ^ k * ‖x‖ ^ j) * ‖iteratedFDeriv ℝ n (sliceCLM x' f) x‖ := by ring
      _ ≤ ‖(x, x')‖ ^ (j + k) * ‖iteratedFDeriv ℝ n f (x, x')‖ :=
          mul_le_mul hw (norm_iteratedFDeriv_sliceCLM_le f x' n x) (norm_nonneg _) (by positivity)
      _ ≤ M := SchwartzMap.le_seminorm ℂ (j + k) n f (x, x')
  rcases eq_or_lt_of_le (pow_nonneg (norm_nonneg x') k : (0 : ℝ) ≤ ‖x'‖ ^ k) with h0 | hpos
  · rw [← h0, zero_mul]; exact hM
  · rw [mul_comm, ← le_div_iff₀ hpos]
    refine SchwartzMap.seminorm_le_bound ℂ j n _ (div_nonneg hM hpos.le) (fun x => ?_)
    rw [le_div_iff₀ hpos, mul_comm]
    exact hpt x

end GlobalTheory.SchwartzFstOp
end

open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_slice_seminorm_le : ∀ {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V'] (f : 𝓢(V × V', ℂ)) (x' : V') (j k n : ℕ), ‖x'‖ ^ k * SchwartzMap.seminorm ℂ j n (sliceCLM x' f) ≤ SchwartzMap.seminorm ℂ (j + k) n f := by
  atlas_forward_decl GlobalTheory.SchwartzFstOp.norm_pow_mul_seminorm_sliceCLM_le
end

section
section
open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp

namespace GlobalTheory.SchwartzTranslateUnif

open GlobalTheory.SchwartzTranslate

theorem seminorm_lineDerivOp_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V)
    (g : 𝓢(V, ℂ)) (k n : ℕ) :
    SchwartzMap.seminorm ℂ k n (LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a g)
      ≤ ‖a‖ * SchwartzMap.seminorm ℂ k (n + 1) g := by
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x => ?_
  have e : ⇑(LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a g) = fun y => fderiv ℝ g y a := by
    funext y; rw [LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [e]
  have h1 : ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) x‖
      ≤ ‖a‖ * ‖iteratedFDeriv ℝ (n + 1) g x‖ := by
    rw [← norm_iteratedFDeriv_fderiv]
    exact norm_iteratedFDeriv_clm_apply_const
      (g.smooth'.fderiv_right (m := ∞) le_rfl).contDiffAt
      (by exact_mod_cast le_top)
  have h2 := SchwartzMap.le_seminorm ℂ k (n + 1) g x
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) x‖
      ≤ ‖x‖ ^ k * (‖a‖ * ‖iteratedFDeriv ℝ (n + 1) g x‖) := by gcongr
    _ = ‖a‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) g x‖) := by ring
    _ ≤ _ := by gcongr

theorem seminorm_translate_sub_le_explicit {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : V) (f : 𝓢(V, ℂ)) (k n : ℕ) (t : ℝ) (ht : |t| ≤ 1) :
    SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f
        - (t : ℂ) • LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f)
      ≤ 2 ^ (k - 1) * (SchwartzMap.seminorm ℂ k n
            (LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a (LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f))
          + ‖a‖ ^ k * SchwartzMap.seminorm ℂ 0 n
            (LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a (LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f)))
        * t ^ 2 := by
  set f1 : 𝓢(V, ℂ) := LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f with hf1
  set f2 : 𝓢(V, ℂ) := LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f1 with hf2
  have e1 : (fun y => fderiv ℝ f y a) = f1 := by
    funext y; rw [hf1, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have e2 : (fun y => fderiv ℝ f1 y a) = f2 := by
    funext y; rw [hf2, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x => ?_
  have hn : ((n : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have c0 : ContDiff ℝ ∞ f := f.smooth'
  have c1 : ContDiff ℝ ∞ f1 := f1.smooth'
  have ct : ContDiff ℝ ∞ (fun z => f (z + t • a)) := c0.comp (contDiff_id.add contDiff_const)
  have efun : ⇑(SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f - (t : ℂ) • f1)
      = (fun z => f (z + t • a)) - ⇑f - t • ⇑f1 := by
    funext z
    simp
  have eit : iteratedFDeriv ℝ n
      ⇑(SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f - (t : ℂ) • f1) x
      = iteratedFDeriv ℝ n f (x + t • a) - iteratedFDeriv ℝ n f x
        - t • iteratedFDeriv ℝ n f1 x := by
    rw [efun, iteratedFDeriv_sub_apply (f := (fun z => f (z + t • a)) - ⇑f) (g := t • ⇑f1)
      ((ct.sub c0).of_le hn).contDiffAt
      ((c1.const_smul t).of_le hn).contDiffAt,
      iteratedFDeriv_sub_apply (ct.of_le hn).contDiffAt (c0.of_le hn).contDiffAt,
      iteratedFDeriv_const_smul_apply (c1.of_le hn).contDiffAt, iteratedFDeriv_comp_add_right]
  have key := taylor_two (fun s : ℝ => ‖x‖ ^ k • iteratedFDeriv ℝ n f (x + s • a))
    (fun s : ℝ => ‖x‖ ^ k • iteratedFDeriv ℝ n f1 (x + s • a))
    (fun s : ℝ => ‖x‖ ^ k • iteratedFDeriv ℝ n f2 (x + s • a))
    (fun s => by
      have := hasDerivAt_iteratedFDeriv_line a n f c0 x s
      rw [e1] at this
      exact this.const_smul (‖x‖ ^ k))
    (fun s => by
      have := hasDerivAt_iteratedFDeriv_line a n f1 c1 x s
      rw [e2] at this
      exact this.const_smul (‖x‖ ^ k))
    (2 ^ (k - 1) * (SchwartzMap.seminorm ℂ k n f2 + ‖a‖ ^ k * SchwartzMap.seminorm ℂ 0 n f2))
    (fun s hs => by
      have hx : ‖x‖ ≤ ‖x + s • a‖ + ‖a‖ := by
        have h3 : ‖s • a‖ ≤ ‖a‖ := by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_of_le_one_left (norm_nonneg _) hs
        have h4 := norm_sub_le (x + s • a) (s • a)
        rw [add_sub_cancel_right] at h4
        linarith
      have hp : ‖x‖ ^ k ≤ 2 ^ (k - 1) * (‖x + s • a‖ ^ k + ‖a‖ ^ k) :=
        (pow_le_pow_left₀ (norm_nonneg _) hx k).trans
          (add_pow_le (norm_nonneg _) (norm_nonneg _) k)
      have b1 := SchwartzMap.le_seminorm ℂ k n f2 (x + s • a)
      have b2 := SchwartzMap.le_seminorm ℂ 0 n f2 (x + s • a)
      rw [pow_zero, one_mul] at b2
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      calc _ ≤ 2 ^ (k - 1) * (‖x + s • a‖ ^ k + ‖a‖ ^ k)
              * ‖iteratedFDeriv ℝ n f2 (x + s • a)‖ := by gcongr
        _ = 2 ^ (k - 1) * (‖x + s • a‖ ^ k * ‖iteratedFDeriv ℝ n f2 (x + s • a)‖
              + ‖a‖ ^ k * ‖iteratedFDeriv ℝ n f2 (x + s • a)‖) := by ring
        _ ≤ _ := by gcongr) t ht
  simp only [zero_smul, add_zero] at key
  rw [smul_comm t, ← smul_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)] at key
  rw [eit]
  exact key

theorem seminorm_translate_sub_lineDeriv_le {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : 𝓢(X, ℂ)) (k n : ℕ) : ∃ C : ℝ, ∀ a : X, ‖a‖ ≤ 1 →
      SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-a) f - f
        - LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a f) ≤ C * ‖a‖ ^ 2 := by
  refine ⟨2 ^ (k - 1) * (SchwartzMap.seminorm ℂ k (n + 2) f
    + SchwartzMap.seminorm ℂ 0 (n + 2) f), fun a ha => ?_⟩
  have h := seminorm_translate_sub_le_explicit a f k n 1 (by simp)
  simp only [one_smul, Complex.ofReal_one, one_pow, mul_one] at h
  refine h.trans ?_
  have hA : ∀ j, SchwartzMap.seminorm ℂ j n
      (LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a (LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a f))
      ≤ ‖a‖ ^ 2 * SchwartzMap.seminorm ℂ j (n + 2) f := by
    intro j
    calc _ ≤ ‖a‖ * SchwartzMap.seminorm ℂ j (n + 1) (LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a f) :=
          seminorm_lineDerivOp_le a _ j n
      _ ≤ ‖a‖ * (‖a‖ * SchwartzMap.seminorm ℂ j (n + 1 + 1) f) := by
          gcongr; exact seminorm_lineDerivOp_le a f j (n + 1)
      _ = _ := by ring
  have hak : ‖a‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) ha
  have h0 := hA 0
  have hk := hA k
  have s0 : 0 ≤ SchwartzMap.seminorm ℂ 0 n
      (LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a (LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a f)) :=
    apply_nonneg _ _
  have hmul : ‖a‖ ^ k * SchwartzMap.seminorm ℂ 0 n
      (LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a (LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a f))
      ≤ ‖a‖ ^ 2 * SchwartzMap.seminorm ℂ 0 (n + 2) f :=
    (mul_le_of_le_one_left s0 hak).trans h0
  calc _ ≤ 2 ^ (k - 1) * (‖a‖ ^ 2 * SchwartzMap.seminorm ℂ k (n + 2) f
          + ‖a‖ ^ 2 * SchwartzMap.seminorm ℂ 0 (n + 2) f) := by gcongr
    _ = _ := by ring

end GlobalTheory.SchwartzTranslateUnif
end

open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_translate_taylor_second_order : ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (f : 𝓢(X, ℂ)) (k n : ℕ), ∃ C : ℝ, ∀ a : X, ‖a‖ ≤ 1 → SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-a) f - f - LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a f) ≤ C * ‖a‖ ^ 2 := by
  atlas_forward_decl GlobalTheory.SchwartzTranslateUnif.seminorm_translate_sub_lineDeriv_le
end

section
section
open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp

noncomputable section

open Filter Topology Asymptotics

namespace GlobalTheory.SchwartzFstOp

variable {V W V' E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem sliceCLM_add_eq (x' v : V') (f : 𝓢(V × V', ℂ)) :
    sliceCLM (x' + v) f = sliceCLM x' (SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f) := by
  ext x
  simp [SchwartzMap.compSubConstCLM_apply]

theorem remainder_bound (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (x' : V') :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : V', ‖v‖ ≤ 1 → ∀ z : W,
      ‖T (sliceCLM x' (SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f - f - lineSnd v f)) z‖
        ≤ K * ‖v‖ ^ 2 := by
  let q : Seminorm ℂ 𝓢(V × V', ℂ) :=
    (SchwartzMap.seminorm ℂ 0 0).comp (T.comp (sliceCLM x')).toLinearMap
  have hq : Continuous q :=
    ((schwartz_withSeminorms ℂ W E).continuous_seminorm (0, 0)).comp (T.comp (sliceCLM x')).continuous
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (V × V') ℂ) q hq
  choose D hD using fun i : ℕ × ℕ => GlobalTheory.T.schwartz_translate_taylor_second_order f i.1 i.2
  refine ⟨(C : ℝ) * ∑ i ∈ s, |D i|, by positivity, fun v hv z => ?_⟩
  set g := SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f - f - lineSnd v f with hg
  have ha : ‖((0 : V), v)‖ = ‖v‖ := by simp [Prod.norm_def]
  have h1 : ‖T (sliceCLM x' g) z‖ ≤ q g := SchwartzMap.norm_le_seminorm ℂ _ _
  have h2 : q g ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ (V × V') ℂ)) g := by
    have := hC g
    simpa [Seminorm.smul_apply, NNReal.smul_def] using this
  have h3 : (s.sup (schwartzSeminormFamily ℂ (V × V') ℂ)) g ≤ (∑ i ∈ s, |D i|) * ‖v‖ ^ 2 := by
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro i hi
    have hDi := hD i ((0 : V), v) (by rw [ha]; exact hv)
    rw [ha] at hDi
    calc schwartzSeminormFamily ℂ (V × V') ℂ i g ≤ D i * ‖v‖ ^ 2 := hDi
      _ ≤ |D i| * ‖v‖ ^ 2 := by gcongr; exact le_abs_self _
      _ ≤ (∑ j ∈ s, |D j|) * ‖v‖ ^ 2 := by
          gcongr; exact Finset.single_le_sum (fun j _ => abs_nonneg (D j)) hi
  calc ‖T (sliceCLM x' g) z‖ ≤ q g := h1
    _ ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ (V × V') ℂ)) g := h2
    _ ≤ (C : ℝ) * ((∑ i ∈ s, |D i|) * ‖v‖ ^ 2) := by gcongr
    _ = (C : ℝ) * (∑ i ∈ s, |D i|) * ‖v‖ ^ 2 := by ring

theorem opFst_add_decomp (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (y w : W) (x' v : V') :
    opFst T f (y + w, x' + v) =
      T (sliceCLM x' (SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f - f - lineSnd v f)) (y + w)
        + T (sliceCLM x' f) (y + w) + T (sliceCLM x' (lineSnd v f)) (y + w) := by
  rw [opFst_apply, sliceCLM_add_eq]
  conv_lhs => rw [show SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f
      = (SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f - f - lineSnd v f) + f + lineSnd v f by abel]
  simp only [map_add, SchwartzMap.add_apply]

theorem hasFDerivAt_opFst [FiniteDimensional ℝ V'] (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ))
    (y : W) (x' : V') :
    HasFDerivAt (opFst T f) ((fderiv ℝ (T (sliceCLM x' f)) y).comp (ContinuousLinearMap.fst ℝ W V')
      + (dSndCLM T f (y, x')).comp (ContinuousLinearMap.snd ℝ W V')) (y, x') := by
  have hA : HasFDerivAt (fun q : W × V' => T (sliceCLM x' f) q.1)
      ((fderiv ℝ (T (sliceCLM x' f)) y).comp (ContinuousLinearMap.fst ℝ W V')) (y, x') :=
    ((T (sliceCLM x' f)).differentiableAt.hasFDerivAt).comp (y, x') hasFDerivAt_fst
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hA ⊢
  have hcont : Continuous fun z : W => dSndCLM T f (z, x') := by
    rw [continuous_clm_apply]
    intro v
    exact (T (sliceCLM x' (lineSnd v f))).continuous
  have hB : (fun p : W × V' => dSndCLM T f (y + p.1, x') p.2 - dSndCLM T f (y, x') p.2)
      =o[𝓝 0] fun p => p := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have ht : Tendsto (fun p : W × V' => dSndCLM T f (y + p.1, x')) (𝓝 0) (𝓝 (dSndCLM T f (y, x'))) := by
      have : Tendsto (fun p : W × V' => y + p.1) (𝓝 0) (𝓝 y) := by
        have := (tendsto_const_nhds (x := y)).add ((continuous_fst.tendsto (0 : W × V')))
        simpa using this
      exact (hcont.tendsto y).comp this
    filter_upwards [(Metric.tendsto_nhds.mp ht) c hc] with p hp
    rw [← ContinuousLinearMap.sub_apply]
    calc _ ≤ ‖dSndCLM T f (y + p.1, x') - dSndCLM T f (y, x')‖ * ‖p.2‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ c * ‖p‖ := by
          gcongr
          · rw [← dist_eq_norm]; exact hp.le
          · exact norm_snd_le p
  obtain ⟨K, hK0, hK⟩ := remainder_bound T f x'
  have hC : (fun p : W × V' =>
      T (sliceCLM x' (SchwartzMap.compSubConstCLM ℂ (-((0 : V), p.2)) f - f - lineSnd p.2 f)) (y + p.1))
      =o[𝓝 0] fun p => p := by
    have h1 : (fun p : W × V' =>
        T (sliceCLM x' (SchwartzMap.compSubConstCLM ℂ (-((0 : V), p.2)) f - f - lineSnd p.2 f)) (y + p.1))
        =O[𝓝 0] fun p : W × V' => ‖p‖ ^ 2 := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨K, ?_⟩
      filter_upwards [Metric.closedBall_mem_nhds (0 : W × V') one_pos] with p hp
      rw [Metric.mem_closedBall, dist_zero_right] at hp
      calc _ ≤ K * ‖p.2‖ ^ 2 := hK p.2 ((norm_snd_le p).trans hp) _
        _ ≤ K * ‖p‖ ^ 2 := by gcongr; exact norm_snd_le p
        _ = K * ‖‖p‖ ^ 2‖ := by rw [norm_pow, norm_norm]
    exact h1.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  refine ((hA.add hB).add hC).congr_left (fun p => ?_)
  obtain ⟨w, v⟩ := p
  simp only [Prod.mk_add_mk]
  rw [opFst_add_decomp]
  simp only [opFst_apply, dSndCLM_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  abel

end GlobalTheory.SchwartzFstOp
end
end

open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.has_fderiv_at_schwartz_operator_first : ∀ {V W V' E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V'] [NormedAddCommGroup E] [NormedSpace ℂ E] (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (y : W) (x' : V'), HasFDerivAt (opFst T f) ((fderiv ℝ (T (sliceCLM x' f)) y).comp (ContinuousLinearMap.fst ℝ W V') + (dSndCLM T f (y, x')).comp (ContinuousLinearMap.snd ℝ W V')) (y, x') := by
  atlas_forward_decl GlobalTheory.SchwartzFstOp.hasFDerivAt_opFst
end

section
section
noncomputable section

open scoped SchwartzMap ContDiff

namespace GlobalTheory.SchwartzFstOp

section Bounds

variable {X Y F G : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]

theorem continuous_finset_sup_schwartz (s : Finset (ℕ × ℕ)) :
    Continuous ⇑(s.sup (schwartzSeminormFamily ℂ Y G)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sup_empty]; exact continuous_const
  | insert i s _ ih =>
    rw [Finset.sup_insert]
    exact (((schwartz_withSeminorms ℂ Y G).continuous_seminorm i).max ih).congr
      fun x => (Seminorm.sup_apply _ _ _).symm

theorem exists_sup_bound (A : 𝓢(X, F) →L[ℂ] 𝓢(Y, G)) (s : Finset (ℕ × ℕ)) :
    ∃ (t : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ f, (s.sup (schwartzSeminormFamily ℂ Y G)) (A f) ≤
      C * (t.sup (schwartzSeminormFamily ℂ X F)) f := by
  obtain ⟨t, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ X F)
    ((s.sup (schwartzSeminormFamily ℂ Y G)).comp A.toLinearMap)
    ((continuous_finset_sup_schwartz s).comp A.continuous)
  exact ⟨t, C, C.2, fun f => by simpa [Seminorm.comp_apply, Seminorm.smul_apply, NNReal.smul_def] using hC f⟩

theorem sup_apply_mono {s t : Finset (ℕ × ℕ)} (h : s ⊆ t) (f : 𝓢(X, F)) :
    (s.sup (schwartzSeminormFamily ℂ X F)) f ≤ (t.sup (schwartzSeminormFamily ℂ X F)) f :=
  Seminorm.le_def.1 (Finset.sup_mono h) f

end Bounds

variable {V W V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']

theorem slice_sup_le (f : 𝓢(V × V', ℂ)) (x' : V') (s : Finset (ℕ × ℕ)) (k : ℕ) :
    ‖x'‖ ^ k * (s.sup (schwartzSeminormFamily ℂ V ℂ)) (sliceCLM x' f) ≤
      ((s.image fun m : ℕ × ℕ => ((m.1 + k, m.2) : ℕ × ℕ)).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f := by
  set c : ℝ := ‖x'‖ ^ k with hc
  have c0 : 0 ≤ c := by positivity
  set R := ((s.image fun m : ℕ × ℕ => ((m.1 + k, m.2) : ℕ × ℕ)).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f
  have h1 : ∀ m ∈ s, c * schwartzSeminormFamily ℂ V ℂ m (sliceCLM x' f) ≤ R := by
    intro m hm
    have a1 : ‖x'‖ ^ k * SchwartzMap.seminorm ℂ m.1 m.2 (sliceCLM x' f) ≤
        SchwartzMap.seminorm ℂ (m.1 + k) m.2 f := GlobalTheory.T.schwartz_slice_seminorm_le f x' m.1 k m.2
    have a2 : schwartzSeminormFamily ℂ (V × V') ℂ ((m.1 + k, m.2) : ℕ × ℕ) f ≤ R :=
      Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ (V × V') ℂ)
        (Finset.mem_image_of_mem (fun m : ℕ × ℕ => ((m.1 + k, m.2) : ℕ × ℕ)) hm)
    exact a1.trans a2
  rcases c0.eq_or_lt with h | h
  · rw [← h, zero_mul]; exact apply_nonneg _ _
  · rw [← le_div_iff₀' h]
    refine Seminorm.finset_sup_apply_le (div_nonneg (apply_nonneg _ _) c0) fun m hm => ?_
    rw [le_div_iff₀' h]
    exact h1 m hm

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem base_bound (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (k : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : 𝓢(V × V', ℂ)) (p : W × V'),
      ‖p‖ ^ k * ‖opFst T f p‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f := by
  obtain ⟨s₁, C₁, hC₁, h₁⟩ := exists_sup_bound T {(k, 0)}
  obtain ⟨s₂, C₂, hC₂, h₂⟩ := exists_sup_bound T {(0, 0)}
  set t₁ := s₁.image fun m : ℕ × ℕ => ((m.1 + 0, m.2) : ℕ × ℕ)
  set t₂ := s₂.image fun m : ℕ × ℕ => ((m.1 + k, m.2) : ℕ × ℕ)
  refine ⟨t₁ ∪ t₂, C₁ + C₂, by positivity, fun f p => ?_⟩
  obtain ⟨y, x'⟩ := p
  set h := sliceCLM x' f
  have e1 : ‖y‖ ^ k * ‖T h y‖ ≤ C₁ * (s₁.sup (schwartzSeminormFamily ℂ V ℂ)) h := by
    refine (SchwartzMap.norm_pow_mul_le_seminorm ℂ (T h) k y).trans ?_
    have := h₁ h
    simpa [schwartzSeminormFamily] using this
  have e2 : ‖T h y‖ ≤ C₂ * (s₂.sup (schwartzSeminormFamily ℂ V ℂ)) h := by
    have a := SchwartzMap.norm_pow_mul_le_seminorm ℂ (T h) 0 y
    simp only [pow_zero, one_mul] at a
    refine a.trans ?_
    have := h₂ h
    simpa [schwartzSeminormFamily] using this
  have f1 : (s₁.sup (schwartzSeminormFamily ℂ V ℂ)) h ≤
      ((t₁ ∪ t₂).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f := by
    have := slice_sup_le f x' s₁ 0
    rw [pow_zero, one_mul] at this
    exact this.trans (sup_apply_mono Finset.subset_union_left f)
  have f2 : ‖x'‖ ^ k * (s₂.sup (schwartzSeminormFamily ℂ V ℂ)) h ≤
      ((t₁ ∪ t₂).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f :=
    (slice_sup_le f x' s₂ k).trans (sup_apply_mono Finset.subset_union_right f)
  have hp : ‖(y, x')‖ ^ k ≤ ‖y‖ ^ k + ‖x'‖ ^ k := by
    rw [Prod.norm_mk]
    rcases le_total ‖y‖ ‖x'‖ with hl | hl
    · rw [max_eq_right hl]; linarith [pow_nonneg (norm_nonneg y) k]
    · rw [max_eq_left hl]; linarith [pow_nonneg (norm_nonneg x') k]
  set S := ((t₁ ∪ t₂).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f
  change ‖(y, x')‖ ^ k * ‖T h y‖ ≤ (C₁ + C₂) * S
  calc ‖(y, x')‖ ^ k * ‖T h y‖ ≤ (‖y‖ ^ k + ‖x'‖ ^ k) * ‖T h y‖ := by gcongr
    _ = ‖y‖ ^ k * ‖T h y‖ + ‖x'‖ ^ k * ‖T h y‖ := by ring
    _ ≤ C₁ * (s₁.sup (schwartzSeminormFamily ℂ V ℂ)) h +
          ‖x'‖ ^ k * (C₂ * (s₂.sup (schwartzSeminormFamily ℂ V ℂ)) h) := by gcongr
    _ = C₁ * (s₁.sup (schwartzSeminormFamily ℂ V ℂ)) h +
          C₂ * (‖x'‖ ^ k * (s₂.sup (schwartzSeminormFamily ℂ V ℂ)) h) := by ring
    _ ≤ C₁ * S + C₂ * S := by gcongr
    _ = (C₁ + C₂) * S := by ring

variable [FiniteDimensional ℝ V']

theorem differentiable_opFst (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) :
    Differentiable ℝ (opFst T f) := fun p => (GlobalTheory.T.has_fderiv_at_schwartz_operator_first T f p.1 p.2).differentiableAt

variable (W V' E) in

def compFst : (W →L[ℝ] E) →L[ℝ] (W × V' →L[ℝ] E) :=
  (ContinuousLinearMap.compL ℝ (W × V') W E).flip (ContinuousLinearMap.fst ℝ W V')

variable (W V' E) in

def coordSnd (i : Fin (Module.finrank ℝ V')) : E →L[ℝ] (W × V' →L[ℝ] E) :=
  ContinuousLinearMap.smulRightL ℝ (W × V') E
    ((LinearMap.toContinuousLinearMap ((Module.finBasis ℝ V').coord i)).comp (ContinuousLinearMap.snd ℝ W V'))

theorem fderiv_opFst (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) :
    fderiv ℝ (opFst T f) = fun p =>
      compFst W V' E (opFst ((SchwartzMap.fderivCLM ℂ W E).comp T) f p) +
        ∑ i, coordSnd W V' E i (opFst T (lineSnd (Module.finBasis ℝ V' i) f) p) := by
  funext p
  rw [(GlobalTheory.T.has_fderiv_at_schwartz_operator_first T f p.1 p.2).fderiv]
  refine ContinuousLinearMap.ext fun q => ?_
  have hv : q.2 = ∑ i, (Module.finBasis ℝ V').repr q.2 i • Module.finBasis ℝ V' i :=
    ((Module.finBasis ℝ V').sum_repr q.2).symm
  simp [compFst, coordSnd]
  congr 1
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, dSndCLM_apply]

theorem finiteRing_sq_sub_mul_sq_eq_of_card (n : ℕ) : ∀ (E' : Type) [NormedAddCommGroup E'] [NormedSpace ℂ E']
    (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E')),
    (∀ f : 𝓢(V × V', ℂ), ContDiff ℝ n (opFst T f)) ∧
    ∀ k : ℕ, ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : 𝓢(V × V', ℂ)) (p : W × V'),
      ‖p‖ ^ k * ‖iteratedFDeriv ℝ n (opFst T f) p‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f := by
  induction n with
  | zero =>
    intro E' _ _ T
    refine ⟨fun f => contDiff_zero.2 (differentiable_opFst T f).continuous, fun k => ?_⟩
    obtain ⟨s, C, hC, h⟩ := base_bound (V' := V') T k
    exact ⟨s, C, hC, fun f p => by rw [norm_iteratedFDeriv_zero]; exact h f p⟩
  | succ n ih =>
    intro E' _ _ T
    set b := Module.finBasis ℝ V'
    set T₁ := (SchwartzMap.fderivCLM ℂ W E').comp T
    obtain ⟨c₁, b₁⟩ := ih _ T₁
    obtain ⟨c₂, b₂⟩ := ih E' T
    have hA : ∀ f : 𝓢(V × V', ℂ), ContDiff ℝ n (fun p => compFst W V' E' (opFst T₁ f p)) :=
      fun f => (compFst W V' E').contDiff.comp (c₁ f)
    have hB : ∀ (f : 𝓢(V × V', ℂ)) (i : Fin (Module.finrank ℝ V')),
        ContDiff ℝ n (fun p => coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) :=
      fun f i => (coordSnd W V' E' i).contDiff.comp (c₂ _)
    have hG : ∀ f : 𝓢(V × V', ℂ), ContDiff ℝ n (fderiv ℝ (opFst T f)) := fun f => by
      rw [fderiv_opFst]
      exact (hA f).add (ContDiff.sum fun i _ => hB f i)
    refine ⟨fun f => ?_, fun k => ?_⟩
    · rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
      exact ⟨differentiable_opFst T f, by simp, hG f⟩
    · obtain ⟨s₁, C₁, hC₁, h₁⟩ := b₁ k
      obtain ⟨s₂, C₂, hC₂, h₂⟩ := b₂ k
      choose t Ct hCt ht using fun i : Fin (Module.finrank ℝ V') =>
        exists_sup_bound (lineSnd (b i) : 𝓢(V × V', ℂ) →L[ℂ] 𝓢(V × V', ℂ)) s₂
      refine ⟨s₁ ∪ Finset.univ.biUnion t,
        ‖compFst W V' E'‖ * C₁ + ∑ i, ‖coordSnd W V' E' i‖ * (C₂ * Ct i), ?_, fun f p => ?_⟩
      · exact add_nonneg (mul_nonneg (norm_nonneg _) hC₁)
          (Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (mul_nonneg hC₂ (hCt i)))
      set S := ((s₁ ∪ Finset.univ.biUnion t).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f
      rw [← norm_iteratedFDeriv_fderiv, fderiv_opFst]
      have e : iteratedFDeriv ℝ n (fun p => compFst W V' E' (opFst T₁ f p) +
            ∑ i, coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) p =
          iteratedFDeriv ℝ n (fun p => compFst W V' E' (opFst T₁ f p)) p +
            ∑ i, iteratedFDeriv ℝ n (fun p => coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) p := by
        rw [show (fun p => compFst W V' E' (opFst T₁ f p) +
            ∑ i, coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) =
            (fun p => compFst W V' E' (opFst T₁ f p)) +
            (fun p => ∑ i, coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) from rfl]
        rw [iteratedFDeriv_add_apply (f := fun p => compFst W V' E' (opFst T₁ f p))
          (g := fun p => ∑ i, coordSnd W V' E' i (opFst T (lineSnd (b i) f) p))
          (hA f).contDiffAt (ContDiff.sum fun i _ => hB f i).contDiffAt,
          iteratedFDeriv_fun_sum_apply fun i _ => (hB f i).contDiffAt]
      rw [e]
      have kA : ‖p‖ ^ k * ‖iteratedFDeriv ℝ n (fun p => compFst W V' E' (opFst T₁ f p)) p‖ ≤
          ‖compFst W V' E'‖ * C₁ * S := by
        have a := (compFst W V' E').norm_iteratedFDeriv_comp_left (c₁ f).contDiffAt (x := p) le_rfl
        have a2 := h₁ f p
        have a3 := sup_apply_mono (Finset.subset_union_left (s₁ := s₁) (s₂ := Finset.univ.biUnion t)) f
        calc _ ≤ ‖p‖ ^ k * (‖compFst W V' E'‖ * ‖iteratedFDeriv ℝ n (opFst T₁ f) p‖) := by
              gcongr; exact a
          _ = ‖compFst W V' E'‖ * (‖p‖ ^ k * ‖iteratedFDeriv ℝ n (opFst T₁ f) p‖) := by ring
          _ ≤ ‖compFst W V' E'‖ * (C₁ * S) :=
              mul_le_mul_of_nonneg_left (a2.trans (mul_le_mul_of_nonneg_left a3 hC₁)) (norm_nonneg _)
          _ = _ := by ring
      have kB : ∀ i, ‖p‖ ^ k *
          ‖iteratedFDeriv ℝ n (fun p => coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) p‖ ≤
          ‖coordSnd W V' E' i‖ * (C₂ * Ct i) * S := by
        intro i
        have a := (coordSnd W V' E' i).norm_iteratedFDeriv_comp_left (c₂ (lineSnd (b i) f)).contDiffAt
          (x := p) le_rfl
        have a2 := h₂ (lineSnd (b i) f) p
        have a3 := ht i f
        have a4 : ((t i).sup (schwartzSeminormFamily ℂ (V × V') ℂ)) f ≤ S :=
          sup_apply_mono (Finset.subset_union_right.trans' (Finset.subset_biUnion_of_mem t (Finset.mem_univ i))) f
        calc _ ≤ ‖p‖ ^ k * (‖coordSnd W V' E' i‖ *
                ‖iteratedFDeriv ℝ n (opFst T (lineSnd (b i) f)) p‖) := by
              gcongr; exact a
          _ = ‖coordSnd W V' E' i‖ * (‖p‖ ^ k * ‖iteratedFDeriv ℝ n (opFst T (lineSnd (b i) f)) p‖) := by ring
          _ ≤ ‖coordSnd W V' E' i‖ * (C₂ * (Ct i * S)) :=
              mul_le_mul_of_nonneg_left (a2.trans (mul_le_mul_of_nonneg_left
                (a3.trans (mul_le_mul_of_nonneg_left a4 (hCt i))) hC₂)) (norm_nonneg _)
          _ = _ := by ring
      calc ‖p‖ ^ k * ‖iteratedFDeriv ℝ n (fun p => compFst W V' E' (opFst T₁ f p)) p +
            ∑ i, iteratedFDeriv ℝ n (fun p => coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) p‖
          ≤ ‖p‖ ^ k * ‖iteratedFDeriv ℝ n (fun p => compFst W V' E' (opFst T₁ f p)) p‖ +
            ∑ i, ‖p‖ ^ k *
              ‖iteratedFDeriv ℝ n (fun p => coordSnd W V' E' i (opFst T (lineSnd (b i) f) p)) p‖ := by
            rw [← Finset.mul_sum, ← mul_add]
            gcongr
            exact (norm_add_le _ _).trans (by gcongr; exact norm_sum_le _ _)
        _ ≤ ‖compFst W V' E'‖ * C₁ * S + ∑ i, ‖coordSnd W V' E' i‖ * (C₂ * Ct i) * S := by
            exact add_le_add kA (Finset.sum_le_sum fun i _ => kB i)
        _ = _ := by rw [← Finset.sum_mul, ← add_mul]

def tensorId (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, ℂ)) : 𝓢(V × V', ℂ) →L[ℂ] 𝓢(W × V', ℂ) :=
  SchwartzMap.mkCLM (σ := RingHom.id ℂ) (fun f p => opFst T f p)
    (fun f g p => by simp [opFst, map_add])
    (fun a f p => by simp [opFst, map_smul])
    (fun f => contDiff_infty.2 fun n => (finiteRing_sq_sub_mul_sq_eq_of_card n ℂ T).1 f)
    (fun m => (finiteRing_sq_sub_mul_sq_eq_of_card m.2 ℂ T).2 m.1)

theorem tensorId_apply (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, ℂ)) (f : 𝓢(V × V', ℂ)) (y : W) (x' : V') :
    tensorId T f (y, x') = T (sliceCLM x' f) y := rfl

theorem exists_tensorId : ∀ {V W V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [NormedAddCommGroup V']
    [NormedSpace ℝ V'] [FiniteDimensional ℝ V'] (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap W ℂ),
    ∃ P : SchwartzMap (V × V') ℂ →L[ℂ] SchwartzMap (W × V') ℂ, ∀ (f : SchwartzMap (V × V') ℂ) (x' : V')
      (h : SchwartzMap V ℂ), (∀ x, h x = f (x, x')) → ∀ y, P f (y, x') = T h y := by
  intro V W V' _ _ _ _ _ _ _ _ _ T
  refine ⟨tensorId T, fun f x' h hh y => ?_⟩
  have e : sliceCLM x' f = h := by
    ext x
    rw [sliceCLM_apply, hh]
  rw [tensorId_apply, e]

end GlobalTheory.SchwartzFstOp
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_operator_parametric_extension : ∀ {V W V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V'] (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap W ℂ), ∃ P : SchwartzMap (V × V') ℂ →L[ℂ] SchwartzMap (W × V') ℂ, ∀ (f : SchwartzMap (V × V') ℂ) (x' : V') (h : SchwartzMap V ℂ), (∀ x, h x = f (x, x')) → ∀ y, P f (y, x') = T h y := by
  atlas_forward_decl GlobalTheory.SchwartzFstOp.exists_tensorId
end

section
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblEval
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_schwartz_function_factorizable_sum : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (a : (κ → Af F) → ℂ), a ∈ SB (κ → Af F) → ∃ (m : ℕ) (φ : Fin m → ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ j v, φ j v ∈ SB (κ → Fv F v)) ∧ (∀ j, ∀ᶠ v in cofinite, φ j v = stdInd F κ v) ∧ ∀ x, a x = ∑ j, ∏ᶠ v, φ j v fun i => evalV F v (x i) := by
  first | exact @GlobalTheory.SBRestrProd.sb_eq_sum_restrProd | exact GlobalTheory.SBRestrProd.sb_eq_sum_restrProd | (intros; apply GlobalTheory.SBRestrProd.sb_eq_sum_restrProd <;> assumption)
end

section
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.SBBlocks

theorem isClosed_support_of_isLocallyConstant {Z : Type} [TopologicalSpace Z] {f : Z → ℂ}
    (hf : IsLocallyConstant f) : IsClosed (Function.support f) := by
  have : Function.support f = (f ⁻¹' {0})ᶜ := by ext; simp
  rw [this]; exact (hf.isOpen_fiber 0).isClosed_compl

theorem mem_SB_of_support_subset {Z : Type} [TopologicalSpace Z] {f : Z → ℂ} {C : Set Z}
    (hf : IsLocallyConstant f) (hC : IsCompact C) (hs : Function.support f ⊆ C) : f ∈ SB Z :=
  ⟨hf, HasCompactSupport.intro' (hC.of_isClosed_subset (isClosed_support_of_isLocallyConstant hf) hs)
    (isClosed_support_of_isLocallyConstant hf) fun _ hx => Function.notMem_support.1 hx⟩

theorem prod_decomp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (h : X × Y → ℂ)
    (hh : h ∈ SB (X × Y)) :
    ∃ (m : ℕ) (a : Fin m → X → ℂ) (b : Fin m → Y → ℂ), (∀ j, a j ∈ SB X) ∧ (∀ j, b j ∈ SB Y) ∧
      ∀ x y, h (x, y) = ∑ j, a j x * b j y := by
  classical
  obtain ⟨hlc, hcs⟩ := hh
  have hK : IsCompact (tsupport h) := hcs.isCompact
  have hK1 : IsCompact (Prod.fst '' tsupport h) := hK.image continuous_fst
  have hK2 : IsCompact (Prod.snd '' tsupport h) := hK.image continuous_snd
  have hzero : ∀ x y, h (x, y) ≠ 0 → x ∈ Prod.fst '' tsupport h ∧ y ∈ Prod.snd '' tsupport h :=
    fun x y hne => ⟨⟨(x, y), subset_tsupport h hne, rfl⟩, ⟨(x, y), subset_tsupport h hne, rfl⟩⟩
  let s : Y → X → ℂ := fun y x => h (x, y)
  have hs : IsLocallyConstant s := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro y₀
    have key : ∀ᶠ y in 𝓝 y₀, ∀ x ∈ Prod.fst '' tsupport h, h (x, y) = h (x, y₀) := by
      refine hK1.eventually_forall_of_forall_eventually (P := fun y x => h (x, y) = h (x, y₀)) ?_
      intro x _
      have h1 : IsLocallyConstant (fun z : Y × X => h (z.2, z.1)) := hlc.comp_continuous continuous_swap
      have h2 : IsLocallyConstant (fun z : Y × X => h (z.2, y₀)) :=
        hlc.comp_continuous (continuous_snd.prodMk continuous_const)
      filter_upwards [h1.eventually_eq (y₀, x), h2.eventually_eq (y₀, x)] with z hz1 hz2
      rw [hz1, hz2]
    filter_upwards [key] with y hy
    funext x
    by_cases hx : x ∈ Prod.fst '' tsupport h
    · exact hy x hx
    · show h (x, y) = h (x, y₀)
      rw [image_eq_zero_of_notMem_tsupport (fun hm => hx ⟨_, hm, rfl⟩),
        image_eq_zero_of_notMem_tsupport (fun hm => hx ⟨_, hm, rfl⟩)]
  have hsSB : ∀ y, s y ∈ SB X := fun y =>
    mem_SB_of_support_subset (hlc.comp_continuous (continuous_id.prodMk continuous_const)) hK1
      (fun x hx => (hzero x y hx).1)
  have hsne : ∀ y, s y ≠ 0 → y ∈ Prod.snd '' tsupport h := fun y hy => by
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hy
    exact (hzero x y hx).2
  obtain ⟨t, ht⟩ := hK2.elim_finite_subcover (fun φ : X → ℂ => s ⁻¹' {φ}) (fun φ => hs.isOpen_fiber φ)
    (fun y _ => Set.mem_iUnion.2 ⟨s y, rfl⟩)
  let t' := t.filter (fun φ => φ ≠ 0 ∧ φ ∈ SB X)
  let bb : (X → ℂ) → Y → ℂ := fun φ y => if s y = φ then 1 else 0
  have hbSB : ∀ φ ∈ t', bb φ ∈ SB Y := by
    intro φ hφ
    have hφ0 : φ ≠ 0 := (Finset.mem_filter.1 hφ).2.1
    refine mem_SB_of_support_subset (hs.comp fun v => if v = φ then (1 : ℂ) else 0) hK2 ?_
    intro y hy
    have : s y = φ := by
      by_contra hne
      exact hy (if_neg hne)
    exact hsne y (this ▸ hφ0)
  have hsum : ∀ x y, h (x, y) = ∑ φ ∈ t', φ x * bb φ y := by
    intro x y
    have e1 : ∑ φ ∈ t', φ x * bb φ y = ∑ φ ∈ t', if s y = φ then φ x else 0 :=
      Finset.sum_congr rfl fun φ _ => by simp only [bb]; split_ifs <;> simp
    rw [e1, Finset.sum_ite_eq]
    split_ifs with hin
    · rfl
    · show s y x = 0
      by_contra hne
      have hy0 : s y ≠ 0 := fun h0 => hne (by rw [h0]; rfl)
      apply hin
      obtain ⟨φ, hφ, hyφ⟩ := Set.mem_iUnion₂.1 (ht (hsne y hy0))
      have : s y = φ := hyφ
      exact Finset.mem_filter.2 ⟨this ▸ hφ, hy0, hsSB y⟩
  refine ⟨t'.card, fun j => (t'.equivFin.symm j : X → ℂ), fun j => bb (t'.equivFin.symm j),
    fun j => (Finset.mem_filter.1 (t'.equivFin.symm j).2).2.2, fun j => hbSB _ (t'.equivFin.symm j).2, ?_⟩
  intro x y
  rw [hsum x y, ← Finset.sum_coe_sort t']
  exact (Equiv.sum_comp t'.equivFin.symm (fun φ : t' => (φ : X → ℂ) x * bb φ y)).symm

theorem sum_prod_blocks {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (g : (κ ⊕ κ' → Af F) → ℂ) (hg : g ∈ SB (κ ⊕ κ' → Af F)) :
    ∃ (m : ℕ) (a : Fin m → (κ → Af F) → ℂ) (b : Fin m → (κ' → Af F) → ℂ), (∀ j, a j ∈ SB (κ → Af F)) ∧
      (∀ j, b j ∈ SB (κ' → Af F)) ∧ ∀ x x', g (Sum.elim x x') = ∑ j, a j x * b j x' := by
  let e : (κ ⊕ κ' → Af F) ≃ₜ (κ → Af F) × (κ' → Af F) := Homeomorph.sumArrowHomeomorphProdArrow
  have hh : g ∘ e.symm ∈ SB ((κ → Af F) × (κ' → Af F)) :=
    ⟨hg.1.comp_continuous e.symm.continuous, hg.2.comp_homeomorph e.symm⟩
  obtain ⟨m, a, b, ha, hb, hab⟩ := prod_decomp _ hh
  refine ⟨m, a, b, ha, hb, fun x x' => ?_⟩
  rw [← hab]
  show g _ = g (e.symm (x, x'))
  congr 1

end GlobalTheory.SBBlocks
end
end

section
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblEval
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_sum_split_tensor : ∀ {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ'] (g : (κ ⊕ κ' → Af F) → ℂ), g ∈ SB (κ ⊕ κ' → Af F) → ∃ (m : ℕ) (a : Fin m → (κ → Af F) → ℂ) (b : Fin m → (κ' → Af F) → ℂ), (∀ j, a j ∈ SB (κ → Af F)) ∧ (∀ j, b j ∈ SB (κ' → Af F)) ∧ ∀ x x', g (Sum.elim x x') = ∑ j, a j x * b j x' := by
  first | exact @GlobalTheory.SBBlocks.sum_prod_blocks | exact GlobalTheory.SBBlocks.sum_prod_blocks | (intros; apply GlobalTheory.SBBlocks.sum_prod_blocks <;> assumption)
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section
namespace GlobalTheory.DblEval.PartLStr

theorem mul_blocks_mem_SB {X : Type} [TopologicalSpace X] [T2Space X] {κ κ' : Type} {a : (κ → X) → ℂ} {b : (κ' → X) → ℂ}
    (ha : a ∈ SB (κ → X)) (hb : b ∈ SB (κ' → X)) :
    (fun z : κ ⊕ κ' → X => a (z ∘ Sum.inl) * b (z ∘ Sum.inr)) ∈ SB (κ ⊕ κ' → X) := by
  have hc : Continuous fun p : (κ → X) × (κ' → X) => Sum.elim p.1 p.2 :=
    continuous_pi fun k => by
      cases k
      exacts [(continuous_apply _).comp continuous_fst, (continuous_apply _).comp continuous_snd]
  refine ⟨(ha.1.comp_continuous (f := fun z : κ ⊕ κ' → X => z ∘ Sum.inl) (by fun_prop)).mul
    (hb.1.comp_continuous (f := fun z : κ ⊕ κ' → X => z ∘ Sum.inr) (by fun_prop)), ?_⟩
  refine HasCompactSupport.intro ((ha.2.isCompact.prod hb.2.isCompact).image hc) fun z hz => ?_
  by_cases h1 : z ∘ Sum.inl ∈ tsupport a
  · by_cases h2 : z ∘ Sum.inr ∈ tsupport b
    · exact absurd ⟨(z ∘ Sum.inl, z ∘ Sum.inr), ⟨h1, h2⟩, Sum.elim_comp_inl_inr z⟩ hz
    · simp only [image_eq_zero_of_notMem_tsupport h2, mul_zero]
  · simp only [image_eq_zero_of_notMem_tsupport h1, zero_mul]

theorem glue_sumComm {R κ κ' : Type} (a : κ' → R) (x : κ → R) :
    GlobalTheory.ThK.Adapt.glue (Equiv.sumComm κ κ') a x = Sum.elim x a := by
  funext k; cases k <;> rfl

theorem exists_partL_pureA : ∀ {F : Type} [Field F] [NumberField F] {κ κ₁ κ' : Type} [Fintype κ] [Fintype κ₁] [Fintype κ']
    (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ), IsLocOp e →
    ∃ P : SInf F (κ ⊕ κ') →L[ℂ] SInf F (κ₁ ⊕ κ'), ∀ g ∈ SB (κ ⊕ κ' → Af F), ∃ g₁ ∈ SB (κ₁ ⊕ κ' → Af F),
      ∀ f : SInf F (κ ⊕ κ'), partL e (pureA F f g) = pureA F (P f) g₁ := by
  intro F _ _ κ κ₁ κ' _ _ _ e he
  classical
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  obtain ⟨ei, ev, hSB, hstd, hpure⟩ := he
  let eq₀ : (κ ⊕ κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) × (κ' → mixedEmbedding.mixedSpace F) :=
    (LinearEquiv.sumArrowLequivProdArrow κ κ' ℝ _).toContinuousLinearEquiv
  let eq₁ : (κ₁ ⊕ κ' → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ₁ → mixedEmbedding.mixedSpace F) × (κ' → mixedEmbedding.mixedSpace F) :=
    (LinearEquiv.sumArrowLequivProdArrow κ₁ κ' ℝ _).toContinuousLinearEquiv
  obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.schwartz_operator_parametric_extension (V' := κ' → mixedEmbedding.mixedSpace F) ei
  let P : SInf F (κ ⊕ κ') →L[ℂ] SInf F (κ₁ ⊕ κ') := (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eq₁).comp
    (P₀.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ eq₀.symm))
  have hP : ∀ (f : SInf F (κ ⊕ κ')) (y : κ₁ → mixedEmbedding.mixedSpace F) (x' : κ' → mixedEmbedding.mixedSpace F)
      (h : SInf F κ), (∀ x, h x = f (Sum.elim x x')) → P f (Sum.elim y x') = ei h y := by
    intro f y x' h hh
    have h1 : eq₁ (Sum.elim y x') = (y, x') := rfl
    simp only [P, ContinuousLinearMap.comp_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, h1]
    exact hP₀ _ x' h (fun x => (hh x).trans rfl) y
  refine ⟨P, fun g hg => ?_⟩
  have hE : ∀ (z : AF F) (v : Pl F), evFin F v z = evalV F v z.2 := fun _ _ => rfl
  obtain ⟨m, a, b, ha, hb, hab⟩ := GlobalTheory.T.schwartz_bruhat_sum_split_tensor g hg
  choose n φ hφSB hφstd hφ using fun k => GlobalTheory.T.adelic_schwartz_function_factorizable_sum (a k) (ha k)
  let g₁ : (κ₁ ⊕ κ' → Af F) → ℂ := ∑ k, ∑ j : Fin (n k), fun z =>
    (∏ᶠ v, ev v (φ k j v) fun i => evalV F v (z (Sum.inl i))) * b k (z ∘ Sum.inr)
  have hev : ∀ k j, ∀ᶠ v in cofinite, ev v (φ k j v) = stdInd F κ₁ v := fun k j => by
    filter_upwards [hstd, hφstd k j] with v h1 h2
    rw [h2, h1]
  refine ⟨g₁, Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun j _ =>
    mul_blocks_mem_SB (GlobalTheory.AdelicCoordSB.finprod_mem_SB F κ₁ _ (fun v => hSB v _ (hφSB k j v)) (hev k j)) (hb k), ?_⟩
  intro f
  funext y
  obtain ⟨T, hT⟩ := GlobalTheory.ThK.Adapt.exists_slice (κ := κ ⊕ κ') (κ₁ := κ) (Equiv.sumComm κ κ')
    (fun i => evI F (y (Sum.inr i)))
  have hh : ∀ x, T f x = f (Sum.elim x fun i => evI F (y (Sum.inr i))) := fun x => by
    rw [hT, glue_sumComm]
  have hslice : (fun x : κ → AF F => pureA F f g (Sum.elim x (y ∘ Sum.inr))) =
      ∑ k, ∑ j : Fin (n k), b k (fun i => (y (Sum.inr i)).2) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (T f) (φ k j) := by
    funext x
    have e1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (Sum.elim x (y ∘ Sum.inr) i).1) =
        Sum.elim (fun i => evI F (x i)) fun i => evI F (y (Sum.inr i)) := by
      funext i; cases i <;> rfl
    have e2 : (fun i => (Sum.elim x (y ∘ Sum.inr) i).2) = Sum.elim (fun i => (x i).2) fun i => (y (Sum.inr i)).2 := by
      funext i; cases i <;> rfl
    simp only [pureA, e1, e2, hab, hφ, ← hh, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hE]
    ring
  have ey : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1) =
      Sum.elim (fun i => evI F (y (Sum.inl i))) fun i => evI F (y (Sum.inr i)) := by
    funext i; cases i <;> rfl
  show e (fun x => pureA F f g (Sum.elim x (y ∘ Sum.inr))) (y ∘ Sum.inl) = pureA F (P f) g₁ y
  rw [hslice]
  simp only [map_sum, map_smul, hpure (T f) _ (hφSB _ _) (hφstd _ _), pureA, ey,
    hP f _ _ (T f) hh, g₁, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [hE, Function.comp_def]
  ring
end GlobalTheory.DblEval.PartLStr

end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_operator_left_partial_pure : ∀ {F : Type} [Field F] [NumberField F] {κ κ₁ κ' : Type} [Fintype κ] [Fintype κ₁] [Fintype κ'] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ), IsLocOp e → ∃ P : SInf F (κ ⊕ κ') →L[ℂ] SInf F (κ₁ ⊕ κ'), ∀ g ∈ SB (κ ⊕ κ' → Af F), ∃ g₁ ∈ SB (κ₁ ⊕ κ' → Af F), ∀ f : SInf F (κ ⊕ κ'), partL e (pureA F f g) = pureA F (P f) g₁ := by
  atlas_forward_decl GlobalTheory.DblEval.PartLStr.exists_partL_pureA
end
