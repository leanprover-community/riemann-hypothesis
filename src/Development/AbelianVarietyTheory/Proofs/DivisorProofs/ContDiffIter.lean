import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
import BuildAid.ForwardExisting

section
section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

noncomputable section

namespace GlobalTheory.PsCo.HomotDeriv

theorem ev_rP {n : ℕ} (ε : Fin n → Bool) (g : Mat n) : ev g (rP ε) = ((rM ε g : ℝ) : ℂ) := by
  simp only [rP, rM, map_sum, map_mul, ev, MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem hasDerivAt_scale (G : ℝ → ℝ) (hG : ContDiff ℝ (⊤ : ℕ∞) G) (k : ℕ) (r t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ => iteratedDeriv k (fun y => G (s * y)) r)
      (t⁻¹ * (k * iteratedDeriv k (fun y => G (t * y)) r + r * iteratedDeriv (k + 1) (fun y => G (t * y)) r)) t := by
  have hc : ∀ m : ℕ, ContDiff ℝ m G := fun m => hG.of_le (by exact_mod_cast le_top)
  have e : ∀ (m : ℕ) (s : ℝ), iteratedDeriv m (fun y => G (s * y)) r = s ^ m * iteratedDeriv m G (s * r) :=
    fun m s => congrFun (iteratedDeriv_comp_const_mul (hc m) s) r
  simp only [e]
  have hD : HasDerivAt (iteratedDeriv k G) (iteratedDeriv (k + 1) G (t * r)) (t * r) := by
    rw [iteratedDeriv_succ]
    exact ((hc (k + 1)).differentiable_iteratedDeriv k (by exact_mod_cast Nat.lt_succ_self k)).differentiableAt.hasDerivAt
  have h1 : HasDerivAt (fun s : ℝ => s * r) r t := by simpa using (hasDerivAt_id t).mul_const r
  have h2 : HasDerivAt (fun s : ℝ => s ^ k * iteratedDeriv k G (s * r))
      (k * t ^ (k - 1) * iteratedDeriv k G (t * r) + t ^ k * (iteratedDeriv (k + 1) G (t * r) * r)) t :=
    by
    have h3 := (hasDerivAt_pow k t).mul (hD.comp t h1)
    exact h3
  refine h2.congr_deriv ?_
  rcases k with _ | k
  · simp only [Nat.cast_zero, zero_mul, zero_add, pow_zero, pow_one]
    field_simp
  · simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

theorem sum_shift (N : ℕ) (a e : ℕ → ℂ) (r : ℂ) (he : e (N + 1) = 0) :
    ∑ k ∈ Finset.range (N + 1), ((k : ℂ) * a k + r * a (k + 1)) * e k =
      ∑ k ∈ Finset.range (N + 1), a (k + 1) * (((k : ℂ) + 1) * e (k + 1) + r * e k) := by
  have h1 : ∑ k ∈ Finset.range (N + 1), (k : ℂ) * a k * e k =
      ∑ k ∈ Finset.range (N + 1), a (k + 1) * (((k : ℂ) + 1) * e (k + 1)) := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ (n := N), he]
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  simp only [add_mul (_ * a _), mul_add (a _), Finset.sum_add_distrib, h1]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

theorem sum_prev {n : ℕ} (g : Mat n) (N : ℕ) (a : ℕ → ℂ) (q : ℕ → Poly n) (hq : q N = 0) (R : ℂ) :
    ∑ k ∈ Finset.range (N + 1), a (k + 1) * (R * ev g (prev q k)) =
      ∑ k ∈ Finset.range (N + 1), a (k + 1 + 1) * (R * ev g (q k)) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ (n := N), hq]
  simp [prev]

theorem famF_hasDerivAt : ∀ {n : ℕ} (ε : Fin n → Bool) (G : ℝ → ℝ) (p : ℕ → GlobalTheory.PsCo.Pc1.Poly n) (q : GlobalTheory.PsCo.Pc1.Mode ε → ℕ → GlobalTheory.PsCo.Pc1.Poly n), ContDiff ℝ (⊤ : ℕ∞) G → GlobalTheory.PsCo.Pc1.IsKoszul ε p q → ∀ t : ℝ, 0 < t → ∀ g : GlobalTheory.PsCo.Pc1.Mat n, HasDerivAt (fun s : ℝ => GlobalTheory.PsCo.Pc1.famF ε G p s g) (((t⁻¹ : ℝ) : ℂ) * ∑ x : GlobalTheory.PsCo.Pc1.Mode ε, ∑ j ∈ Finset.range (GlobalTheory.PsCo.Pc1.nMode ε + 1), GlobalTheory.PsCo.Pc1.adBas ε (Matrix.single x.1.2 x.1.1 1) (iteratedDeriv (j + 1) (fun y => G (t * y))) (q x j) g) t := by
  intro n ε G p q hG hK t ht g
  obtain ⟨hrec, hp, hq⟩ := hK
  let a : ℕ → ℂ := fun j => ((iteratedDeriv j (fun y => G (t * y)) (rM ε g) : ℝ) : ℂ)
  have hd : ∀ k ∈ Finset.range (nMode ε + 1),
      HasDerivAt (fun s : ℝ => bas ε (iteratedDeriv k fun x => G (s * x)) (p k) g)
        (((t⁻¹ : ℝ) : ℂ) * (((k : ℂ) * a k + (rM ε g : ℂ) * a (k + 1)) * ev g (p k))) t := by
    intro k _
    refine (((hasDerivAt_scale G hG k (rM ε g) t ht.ne').ofReal_comp).mul_const (ev g (p k))).congr_deriv ?_
    simp only [a]
    push_cast
    ring
  refine (HasDerivAt.fun_sum hd).congr_deriv ?_
  rw [← Finset.mul_sum]
  congr 1
  have hA : ∀ (x : Mode ε) (j : ℕ),
      adBas ε (Matrix.single x.1.2 x.1.1 1) (iteratedDeriv (j + 1) (fun y => G (t * y))) (q x j) g =
        a (j + 1) * ev g (dM ε x (q x j)) + a (j + 1 + 1) * (ev g (dM ε x (rP ε)) * ev g (q x j)) := by
    intro x j
    simp only [adBas, bas, dM, ← iteratedDeriv_succ, map_mul, a]
    ring
  have hR : ∀ j : ℕ, ((j : ℂ) + 1) * ev g (p (j + 1)) + (rM ε g : ℂ) * ev g (p j) =
      ∑ x, (ev g (dM ε x (q x j)) + ev g (dM ε x (rP ε)) * ev g (prev (q x) j)) := by
    intro j
    have := congrArg (ev g) (hrec j)
    simpa only [map_sum, map_add, map_mul, ev_rP, map_natCast, map_one] using this
  rw [sum_shift (nMode ε) a (fun k => ev g (p k)) (rM ε g : ℂ) (by simp [hp (nMode ε + 1) (Nat.lt_succ_self _)])]
  simp only [hA, hR, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [mul_add, Finset.sum_add_distrib]
  rw [sum_prev g (nMode ε) a (q x) (hq x _ le_rfl)]

end GlobalTheory.PsCo.HomotDeriv
end
end

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledKoszulTestFamily_hasDerivAt_scale : ∀ {n : ℕ} (ε : Fin n → Bool) (G : ℝ → ℝ) (p : ℕ → GlobalTheory.PsCo.Pc1.Poly n) (q : GlobalTheory.PsCo.Pc1.Mode ε → ℕ → GlobalTheory.PsCo.Pc1.Poly n), ContDiff ℝ (⊤ : ℕ∞) G → GlobalTheory.PsCo.Pc1.IsKoszul ε p q → ∀ t : ℝ, 0 < t → ∀ g : GlobalTheory.PsCo.Pc1.Mat n, HasDerivAt (fun s : ℝ => GlobalTheory.PsCo.Pc1.famF ε G p s g) (((t⁻¹ : ℝ) : ℂ) * ∑ x : GlobalTheory.PsCo.Pc1.Mode ε, ∑ j ∈ Finset.range (GlobalTheory.PsCo.Pc1.nMode ε + 1), GlobalTheory.PsCo.Pc1.adBas ε (Matrix.single x.1.2 x.1.1 1) (iteratedDeriv (j + 1) (fun y => G (t * y))) (q x j) g) t := by
  atlas_forward_decl GlobalTheory.PsCo.HomotDeriv.famF_hasDerivAt
end

section
section
noncomputable section
open scoped ContDiff
open Set MeasureTheory

namespace GlobalTheory.ParamIntCut

theorem hasDerivAt_snd {F : ℝ → ℝ → ℝ} (hF : ContDiff ℝ 1 (Function.uncurry F)) (s y : ℝ) :
    HasDerivAt (F s) (fderiv ℝ (Function.uncurry F) (s, y) (0, 1)) y := by
  have h1 : HasFDerivAt (Function.uncurry F) (fderiv ℝ (Function.uncurry F) (s, y)) (s, y) :=
    (hF.differentiable one_ne_zero (s, y)).hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ => ((s, t) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) y :=
    (hasDerivAt_const y s).prodMk (hasDerivAt_id y)
  exact h1.comp_hasDerivAt y h2

theorem hasDerivAt_intervalIntegral {F : ℝ → ℝ → ℝ} (a b : ℝ)
    (hF : ContDiff ℝ 1 (Function.uncurry F)) (y₀ : ℝ) :
    HasDerivAt (fun y => ∫ s in a..b, F s y)
      (∫ s in a..b, fderiv ℝ (Function.uncurry F) (s, y₀) (0, 1)) y₀ := by
  set P : ℝ → ℝ → ℝ := fun s y => fderiv ℝ (Function.uncurry F) (s, y) (0, 1) with hP
  have hPc : Continuous (Function.uncurry P) :=
    (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hFc : Continuous (Function.uncurry F) := hF.continuous
  have hsec : ∀ (G : ℝ → ℝ → ℝ), Continuous (Function.uncurry G) → ∀ y, Continuous (fun s => G s y) :=
    fun G hG y => hG.comp (continuous_id.prodMk continuous_const)
  obtain ⟨C, hC⟩ : ∃ C, ∀ p ∈ (uIcc a b) ×ˢ (Metric.closedBall y₀ 1), ‖Function.uncurry P p‖ ≤ C :=
    (isCompact_uIcc.prod (isCompact_closedBall y₀ 1)).exists_bound_of_continuousOn hPc.continuousOn
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := volume)
    (a := a) (b := b) (F := fun y s => F s y) (F' := fun y s => P s y) (x₀ := y₀)
    (bound := fun _ => C) (s := Metric.ball y₀ 1) (Metric.ball_mem_nhds y₀ one_pos)
    (Filter.Eventually.of_forall fun y => (hsec F hFc y).aestronglyMeasurable)
    ((hsec F hFc y₀).intervalIntegrable _ _)
    ((hsec P hPc y₀).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t ht y hy =>
      hC (t, y) ⟨uIoc_subset_uIcc ht, Metric.ball_subset_closedBall hy⟩)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ y _ => hasDerivAt_snd hF t y)
  exact key.2

theorem contDiff_nat_intervalIntegral (a b : ℝ) :
    ∀ (n : ℕ) (F : ℝ → ℝ → ℝ), ContDiff ℝ ∞ (Function.uncurry F) →
      ContDiff ℝ n (fun y => ∫ s in a..b, F s y)
  | 0, F, hF => by
    have h1 : ContDiff ℝ 1 (Function.uncurry F) := hF.of_le (by exact_mod_cast le_top)
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun y => (hasDerivAt_intervalIntegral a b h1 y).continuousAt
  | n + 1, F, hF => by
    have h1 : ContDiff ℝ 1 (Function.uncurry F) := hF.of_le (by exact_mod_cast le_top)
    set P : ℝ → ℝ → ℝ := fun s y => fderiv ℝ (Function.uncurry F) (s, y) (0, 1) with hP
    have hPs : ContDiff ℝ ∞ (Function.uncurry P) :=
      (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hc : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by norm_cast
    rw [hc, contDiff_succ_iff_deriv]
    refine ⟨fun y => (hasDerivAt_intervalIntegral a b h1 y).differentiableAt, by simp, ?_⟩
    have hd : deriv (fun y => ∫ s in a..b, F s y) = fun y => ∫ s in a..b, P s y :=
      funext fun y => (hasDerivAt_intervalIntegral a b h1 y).deriv
    rw [hd]
    exact contDiff_nat_intervalIntegral a b n P hPs

end GlobalTheory.ParamIntCut

namespace GlobalTheory.PsCo.Pc1

theorem isCutFn_intervalIntegral_and_deriv :
    ∀ (F : ℝ → ℝ → ℝ) (a b : ℝ), ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F) →
      (∃ R : ℝ, ∀ s ∈ Set.uIcc a b, ∀ y, R ≤ y → F s y = 0) →
      GlobalTheory.PsCo.Pc1.IsCutFn (fun y => ∫ s in a..b, F s y) ∧
        ∀ y, deriv (fun y => ∫ s in a..b, F s y) y = ∫ s in a..b, deriv (F s) y := by
  intro F a b hF ⟨R, hR⟩
  have h1 : ContDiff ℝ 1 (Function.uncurry F) := hF.of_le (by exact_mod_cast le_top)
  refine ⟨⟨contDiff_infty.2 fun n => GlobalTheory.ParamIntCut.contDiff_nat_intervalIntegral a b n F hF, R, fun y hy => ?_⟩,
    fun y => ?_⟩
  · show ∫ s in a..b, F s y = 0
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun s hs => hR s hs y hy)]
    simp
  · rw [(GlobalTheory.ParamIntCut.hasDerivAt_intervalIntegral a b h1 y).deriv]
    refine intervalIntegral.integral_congr fun s _ => ?_
    exact ((GlobalTheory.ParamIntCut.hasDerivAt_snd h1 s y).deriv).symm

end GlobalTheory.PsCo.Pc1
end
end

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothEventuallyZeroCutoff_intervalIntegral_deriv : ∀ (F : ℝ → ℝ → ℝ) (a b : ℝ), ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F) → (∃ R : ℝ, ∀ s ∈ Set.uIcc a b, ∀ y, R ≤ y → F s y = 0) → GlobalTheory.PsCo.Pc1.IsCutFn (fun y => ∫ s in a..b, F s y) ∧ ∀ y, deriv (fun y => ∫ s in a..b, F s y) y = ∫ s in a..b, deriv (F s) y := by
  atlas_forward_decl GlobalTheory.PsCo.Pc1.isCutFn_intervalIntegral_and_deriv
end

section
section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Pc1

private theorem sg_sq' {n : ℕ} (ε : Fin n → Bool) (a : Fin n) : sg ε a * sg ε a = 1 := by
  unfold sg; split_ifs <;> simp

private theorem conj_sg' {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    (starRingEnd ℂ) (sg ε a) = sg ε a := by
  unfold sg; split_ifs <;> simp

private theorem lieU_decomposition {n : ℕ} (ε : Fin n → Bool) (Z : Mat n) :
    ∃ A B : Mat n, LieU ε A ∧ LieU ε B ∧ Z = A + Complex.I • B := by
  refine ⟨Matrix.of fun a b => (Z a b + (starRingEnd ℂ) (barM ε Z a b)) / 2,
    Matrix.of fun a b => -Complex.I * (Z a b - (starRingEnd ℂ) (barM ε Z a b)) / 2, ?_, ?_, ?_⟩
  · intro a b
    have ha := sg_sq' ε a
    have hb := sg_sq' ε b
    simp only [barM, Matrix.of_apply, map_div₀, map_add, map_neg, map_mul, conj_sg',
      Complex.conj_conj, map_ofNat]
    linear_combination (-(starRingEnd ℂ) (Z a b) / 2 * (sg ε b * sg ε b)) * ha
      + (-(starRingEnd ℂ) (Z a b) / 2) * hb
  · intro a b
    have ha := sg_sq' ε a
    have hb := sg_sq' ε b
    simp only [barM, Matrix.of_apply, map_div₀, map_sub, map_neg, map_mul, conj_sg',
      Complex.conj_conj, map_ofNat, Complex.conj_I]
    linear_combination (-Complex.I * (starRingEnd ℂ) (Z a b) / 2 * (sg ε b * sg ε b)) * ha
      + (-Complex.I * (starRingEnd ℂ) (Z a b) / 2) * hb
  · ext a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    linear_combination ((Z a b - (starRingEnd ℂ) (barM ε Z a b)) / 2) * Complex.I_mul_I

theorem dZ_add_smul {n : ℕ} (ε : Fin n → Bool) (A B : Mat n) (c : ℂ) :
    dZ ε (A + c • B) = dZ ε A + c • dZ ε B := by
  apply MvPolynomial.derivation_ext
  rintro (x | x)
  · simp only [dZ, Derivation.add_apply, Derivation.smul_apply, mkDerivation_X, Sum.elim_inl,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, smul_eq_C_mul,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  · simp only [dZ, Derivation.add_apply, Derivation.smul_apply, mkDerivation_X, Sum.elim_inr, barM,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_neg, smul_eq_C_mul,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem adBas_add_smul {n : ℕ} (ε : Fin n → Bool) (A B : Mat n) (c : ℂ) (H : ℝ → ℝ)
    (P : GlobalTheory.PsCo.Pc1.Poly n) :
    adBas ε (A + c • B) H P = adBas ε A H P + c • adBas ε B H P := by
  funext g
  have hC : ev g (C c) = c := by simp [ev]
  simp only [adBas, bas, dZ_add_smul, Derivation.add_apply, Derivation.smul_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, smul_eq_C_mul, map_add, map_mul, hC]
  ring

theorem adBas_mem_adSpanM  : ∀ {n : ℕ} (ε : Fin n → Bool) (Z : GlobalTheory.PsCo.Pc1.Mat n) (H : ℝ → ℝ)
    (P : GlobalTheory.PsCo.Pc1.Poly n), GlobalTheory.PsCo.Pc1.IsCutFn H →
    GlobalTheory.PsCo.Pc1.adBas ε Z H P ∈ GlobalTheory.PsCo.Pc1.AdSpanM ε := by
  intro n ε Z H P hH
  obtain ⟨A, B, hA, hB, rfl⟩ := lieU_decomposition ε Z
  rw [adBas_add_smul]
  exact Submodule.add_mem _ (Submodule.subset_span ⟨A, H, P, hA, hH, rfl⟩)
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨B, H, P, hB, hH, rfl⟩))

end GlobalTheory.PsCo.Pc1
end

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugationDerivCutoffPolynomial_mem_unitarySpan : ∀ {n : ℕ} (ε : Fin n → Bool) (Z : GlobalTheory.PsCo.Pc1.Mat n) (H : ℝ → ℝ) (P : GlobalTheory.PsCo.Pc1.Poly n), GlobalTheory.PsCo.Pc1.IsCutFn H → GlobalTheory.PsCo.Pc1.adBas ε Z H P ∈ GlobalTheory.PsCo.Pc1.AdSpanM ε := by
  atlas_forward_decl GlobalTheory.PsCo.Pc1.adBas_mem_adSpanM
end

section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A
open scoped ContDiff

namespace GlobalTheory.PsCo.Pc1.Homot

noncomputable def scF (G : ℝ → ℝ) (j : ℕ) (s y : ℝ) : ℝ := s ^ j * iteratedDeriv (j + 1) G (s * y)

lemma contDiff_iter {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (k : ℕ) : ContDiff ℝ ∞ (iteratedDeriv k G) := by
  rw [iteratedDeriv_eq_iterate]
  exact hG.iterate_deriv k

lemma scF_contDiff {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (j : ℕ) : ContDiff ℝ ∞ (Function.uncurry (scF G j)) := by
  have h := contDiff_iter hG (j + 1)
  exact (contDiff_fst.pow j).mul (h.comp (contDiff_fst.mul contDiff_snd))

lemma deriv_scF {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (j : ℕ) (s y : ℝ) : deriv (scF G j s) y = scF G (j + 1) s y := by
  have h := (contDiff_iter hG (j + 1)).differentiable (by simp)
  have h1 : HasDerivAt (fun y => s * y) s y := by simpa using (hasDerivAt_id y).const_mul s
  have h2 := ((h (s * y)).hasDerivAt.comp y h1).const_mul (s ^ j)
  have h3 : deriv (scF G j s) y = _ := h2.deriv
  rw [h3, scF, iteratedDeriv_succ (n := j + 1)]
  ring

lemma iter_scale {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (j : ℕ) (s y : ℝ) :
    iteratedDeriv (j + 1) (fun y => G (s * y)) y = s * scF G j s y := by
  rw [iteratedDeriv_comp_const_mul (hG.of_le (by exact_mod_cast le_top)) s, scF]
  ring

lemma iter_zero {G : ℝ → ℝ} (h0 : ∀ x, 1 ≤ x → G x = 0) (k : ℕ) {x : ℝ} (hx : 1 < x) : iteratedDeriv k G x = 0 := by
  have : G =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy using h0 y (le_of_lt hy)
  rw [this.iteratedDeriv_eq k]
  simp

lemma scF_cont {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (j : ℕ) (y : ℝ) : Continuous fun s => scF G j s y :=
  (scF_contDiff hG j).continuous.comp (continuous_id.prodMk continuous_const)

theorem stHomot : GlobalTheory.PsCo.Pc1.StHomot := by
  intro n ε G p q hP hK t ht
  obtain ⟨hG, h0, -, -⟩ := hP
  have hI : ∀ j, IsCutFn (fun y => ∫ s in (1:ℝ)..t, scF G j s y) ∧
      ∀ y, deriv (fun y => ∫ s in (1:ℝ)..t, scF G j s y) y = ∫ s in (1:ℝ)..t, deriv (scF G j s) y := by
    intro j
    refine GlobalTheory.T.isSmoothEventuallyZeroCutoff_intervalIntegral_deriv (scF G j) 1 t (scF_contDiff hG j) ⟨2, ?_⟩
    intro s hs y hy
    rw [Set.uIcc_of_le ht] at hs
    have : 1 < s * y := by nlinarith [hs.1]
    simp [scF, iter_zero h0 _ this]
  have key : famF ε G p 1 - famF ε G p t = -∑ x : Mode ε, ∑ j ∈ Finset.range (nMode ε + 1),
      adBas ε (Matrix.single x.1.2 x.1.1 1) (fun y => ∫ s in (1:ℝ)..t, scF G j s y) (q x j) := by
    funext g
    set D : ℝ → ℂ := fun s => ∑ x : Mode ε, ∑ j ∈ Finset.range (nMode ε + 1),
      ((scF G (j + 1) s (rM ε g) : ℂ) * ev g (dZ ε (Matrix.single x.1.2 x.1.1 1) (rP ε) * q x j) +
        (scF G j s (rM ε g) : ℂ) * ev g (dZ ε (Matrix.single x.1.2 x.1.1 1) (q x j))) with hD
    have hc : ∀ j, Continuous fun s => (scF G j s (rM ε g) : ℂ) := fun j =>
      Complex.continuous_ofReal.comp (scF_cont hG j _)
    have hder : ∀ s ∈ Set.uIcc (1:ℝ) t, HasDerivAt (fun s : ℝ => famF ε G p s g) (D s) s := by
      intro s hs
      rw [Set.uIcc_of_le ht] at hs
      have hs0 : 0 < s := by linarith [hs.1]
      have h := GlobalTheory.T.scaledKoszulTestFamily_hasDerivAt_scale ε G p q hG hK s hs0 g
      convert h using 1
      rw [hD, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
      simp only [adBas, bas]
      rw [← iteratedDeriv_succ, iter_scale hG, iter_scale hG]
      push_cast
      field_simp
    have hDc : Continuous D := by
      rw [hD]
      refine continuous_finset_sum _ fun x _ => continuous_finset_sum _ fun j _ => ?_
      exact ((hc _).mul continuous_const).add ((hc _).mul continuous_const)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hDc.intervalIntegrable _ _)
    have hint : ∫ s in (1:ℝ)..t, D s = ∑ x : Mode ε, ∑ j ∈ Finset.range (nMode ε + 1),
        adBas ε (Matrix.single x.1.2 x.1.1 1) (fun y => ∫ s in (1:ℝ)..t, scF G j s y) (q x j) g := by
      rw [hD, intervalIntegral.integral_finset_sum]
      · refine Finset.sum_congr rfl fun x _ => ?_
        rw [intervalIntegral.integral_finset_sum]
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [intervalIntegral.integral_add (((hc _).mul_const _).intervalIntegrable _ _)
            (((hc _).mul_const _).intervalIntegrable _ _),
            intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
            intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
          simp only [adBas, bas, (hI j).2, deriv_scF hG]
        · intro j _
          exact (((hc _).mul continuous_const).add ((hc _).mul continuous_const)).intervalIntegrable _ _
      · intro x _
        refine (continuous_finset_sum _ fun j _ => ?_).intervalIntegrable _ _
        exact ((hc _).mul continuous_const).add ((hc _).mul continuous_const)
    simp only [Pi.sub_apply, Pi.neg_apply, Finset.sum_apply]
    rw [← hint, hftc]
    ring
  rw [key]
  exact neg_mem (Submodule.sum_mem _ fun x _ => Submodule.sum_mem _ fun j _ => GlobalTheory.T.conjugationDerivCutoffPolynomial_mem_unitarySpan ε _ _ _ (hI j).1)

end GlobalTheory.PsCo.Pc1.Homot
end
