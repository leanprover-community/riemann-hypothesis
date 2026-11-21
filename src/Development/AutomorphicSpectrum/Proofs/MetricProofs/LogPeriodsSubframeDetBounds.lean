import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.StarInvMulVecDotProductMulVecInvMulVec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodMatrixLocalTrivialization

section
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.Flat

section SlopeTestRemainingChoices

open scoped ComplexOrder MatrixOrder

variable {g k : ℕ}

theorem subframe_map_posSemidef {A : Matrix (Fin g) (Fin g) ℝ} (h : A.PosSemidef) :
    (A.map Complex.ofReal).PosSemidef := by
  have hH : (A.map Complex.ofReal).IsHermitian :=
    h.isHermitian.map _ (fun x => by simp [Complex.conj_ofReal])
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH (fun x => ?_)
  have hu := h.dotProduct_mulVec_nonneg (fun i => (x i).re)
  have hv := h.dotProduct_mulVec_nonneg (fun i => (x i).im)
  simp only [dotProduct, mulVec, Pi.star_apply, star_trivial] at hu hv
  have key : (star x ⬝ᵥ (A.map Complex.ofReal) *ᵥ x).re =
      ∑ i, ((x i).re * ∑ j, A i j * (x j).re + (x i).im * ∑ j, A i j * (x j).im) := by
    simp only [dotProduct, mulVec, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.star_apply, Matrix.map_apply, Complex.mul_re, Complex.re_sum, Complex.im_sum,
      Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.re_ofReal_mul,
      Complex.im_ofReal_mul, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have him := hH.im_star_dotProduct_mulVec_self x
  rw [RCLike.im_to_complex] at him
  rw [Complex.nonneg_iff]
  refine ⟨?_, him.symm⟩
  rw [key, Finset.sum_add_distrib]
  exact add_nonneg hu hv

theorem subframe_inv_bounds (Y : Matrix (Fin g) (Fin g) ℝ) {c D : ℝ} (hc : 0 < c) (hD : 0 < D)
    (h1 : (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef)
    (h2 : (D • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef) :
    D⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ) ≤ (Y⁻¹).map Complex.ofReal ∧
      (Y⁻¹).map Complex.ofReal ≤ c⁻¹ • (1 : Matrix (Fin g) (Fin g) ℂ) := by
  have hmap : ∀ {P Q : Matrix (Fin g) (Fin g) ℝ}, P ≤ Q →
      P.map Complex.ofReal ≤ Q.map Complex.ofReal := by
    intro P Q hPQ
    rw [Matrix.le_iff] at hPQ ⊢
    have := subframe_map_posSemidef hPQ
    rwa [Matrix.map_sub _ (fun a b => Complex.ofReal_sub a b)] at this
  have hone : ∀ t : ℝ, (t • (1 : Matrix (Fin g) (Fin g) ℝ)).map Complex.ofReal =
      t • (1 : Matrix (Fin g) (Fin g) ℂ) := by
    intro t; ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Complex.real_smul]
  have hc1 : (c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosDef := Matrix.PosDef.one.smul hc
  have hle1 : c • (1 : Matrix (Fin g) (Fin g) ℝ) ≤ Y := Matrix.le_iff.mpr h1
  have hle2 : Y ≤ D • (1 : Matrix (Fin g) (Fin g) ℝ) := Matrix.le_iff.mpr h2
  have hY : Y.PosDef := GlobalTheory.posDef_of_le hc1 hle1
  have hlo : D⁻¹ • (1 : Matrix (Fin g) (Fin g) ℝ) ≤ Y⁻¹ :=
    GlobalTheory.inv_smul_one_le_inv_of_le_smul_one hY hD hle2
  have hhi : Y⁻¹ ≤ c⁻¹ • (1 : Matrix (Fin g) (Fin g) ℝ) := by
    have := GlobalTheory.inv_le_inv_of_posDef_of_le hc1 hle1
    rwa [GlobalTheory.inv_real_smul_of_posDef Matrix.PosDef.one hc.ne', inv_one] at this
  refine ⟨?_, ?_⟩
  · have := hmap hlo
    rwa [hone] at this
  · have := hmap hhi
    rwa [hone] at this

theorem subframe_det_bounds (P : Matrix (Fin g) (Fin k) ℂ) (A : Matrix (Fin g) (Fin g) ℂ)
    {a b : ℝ} (ha : 0 ≤ a) (h1 : a • (1 : Matrix (Fin g) (Fin g) ℂ) ≤ A)
    (h2 : A ≤ b • (1 : Matrix (Fin g) (Fin g) ℂ)) :
    a ^ k * (Pᴴ * P).det.re ≤ (Pᴴ * A * P).det.re ∧
      (Pᴴ * A * P).det.re ≤ b ^ k * (Pᴴ * P).det.re := by
  have hA : A.PosSemidef := GlobalTheory.posSemidef_of_le (Matrix.PosSemidef.one.smul ha) h1
  have hPP : (Pᴴ * P).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self P
  have hsm : ∀ t : ℝ, Pᴴ * (t • (1 : Matrix (Fin g) (Fin g) ℂ)) * P = t • (Pᴴ * P) := by
    intro t; rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have hlo : a • (Pᴴ * P) ≤ Pᴴ * A * P := by
    have := GlobalTheory.conjTranspose_mul_mul_le_of_le h1 P
    rwa [hsm] at this
  have hhi : Pᴴ * A * P ≤ b • (Pᴴ * P) := by
    have := GlobalTheory.conjTranspose_mul_mul_le_of_le h2 P
    rwa [hsm] at this
  have hdetsm : ∀ t : ℝ, ((t • (Pᴴ * P)).det).re = t ^ k * ((Pᴴ * P).det).re := by
    intro t
    have he : t • (Pᴴ * P) = (t : ℂ) • (Pᴴ * P) := by
      ext i j; simp [Complex.real_smul]
    rw [he, Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  refine ⟨?_, ?_⟩
  · have := GlobalTheory.pow_mul_re_det_le_of_smul_le hPP ha hlo
    simpa [Fintype.card_fin] using this
  · have := GlobalTheory.re_det_le_re_det_of_posSemidef_of_le (hA.conjTranspose_mul_mul_same P) hhi
    rw [RCLike.re_to_complex, RCLike.re_to_complex, hdetsm] at this
    exact this

theorem subframe_gram_posDef (F : Matrix (Fin g) (Fin k) ℂ) (h : F.rank = k) :
    ((F.map star)ᴴ * F.map star).PosDef := by
  have hr : (F.map star).rank = k := by
    have he : F.map star = (Fᴴ)ᵀ := by
      ext i j; simp [Matrix.conjTranspose_apply]
    rw [he, Matrix.rank_transpose, Matrix.rank_conjTranspose, h]
  have hr' : Module.finrank ℂ (LinearMap.range (F.map star).mulVecLin) = k := hr
  have hsum := LinearMap.finrank_range_add_finrank_ker (F.map star).mulVecLin
  rw [Module.finrank_fin_fun, hr'] at hsum
  have hker0 : Module.finrank ℂ (LinearMap.ker (F.map star).mulVecLin) = 0 := by omega
  have hbot : LinearMap.ker (F.map star).mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hker0
  have hinj : Function.Injective (F.map star).mulVec := by
    intro v w hvw
    have h0 : (F.map star).mulVec (v - w) = 0 := by
      rw [Matrix.mulVec_sub, hvw, sub_self]
    have := (Matrix.ker_mulVecLin_eq_bot_iff.mp hbot) (v - w) h0
    exact sub_eq_zero.mp this
  exact Matrix.PosDef.conjTranspose_mul_self _ hinj

theorem subframe_continuous_det :
    Continuous fun M : Matrix (Fin g) (Fin k) ℂ => ((Mᵀ * M.map star).det).re := by
  exact Complex.continuous_re.comp
    ((continuous_id.matrix_transpose.matrix_mul (continuous_id.matrix_map continuous_star)).matrix_det)

end SlopeTestRemainingChoices

theorem subframe_det_log_growth : ∀ (g k : ℕ) (X : Type) [TopologicalSpace X] (K : Set X), IsCompact K → ∀ (F : X → Matrix (Fin g) (Fin k) ℂ), ContinuousOn F K → (∀ x ∈ K, (F x).rank = k) → ∀ c C : ℝ, 0 < c → ∃ C' : ℝ, 0 < C' ∧ ∀ x ∈ K, ∀ (Y : Matrix (Fin g) (Fin g) ℝ) (r : ℝ), 1 ≤ r → (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ((C * r) • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef → let d := (((F x)ᵀ * (Y⁻¹).map Complex.ofReal * (F x).map star).det).re; d ≤ C' ∧ 1 ≤ C' * r ^ k * d := by
  intro g k X _ K hK F hF hrank c C hc
  by_cases hne : K.Nonempty
  swap
  · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ hne⟩
  have hT : ∀ x, ((F x).map star)ᴴ = (F x)ᵀ := by
    intro x; ext i j; simp [Matrix.conjTranspose_apply]
  have hGc : ContinuousOn (fun x => (((F x)ᵀ * (F x).map star).det).re) K :=
    subframe_continuous_det.comp_continuousOn hF
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hGc
  obtain ⟨x₀, hx₀K, hx₀⟩ := hK.exists_isMinOn hne hGc
  have hGpos : ∀ x ∈ K, 0 < (((F x)ᵀ * (F x).map star).det).re := by
    intro x hx
    have hpd := subframe_gram_posDef (F x) (hrank x hx)
    rw [hT] at hpd
    have := GlobalTheory.re_det_pos_of_posDef hpd
    simpa using this
  obtain ⟨m, hm⟩ : ∃ m, m = (((F x₀)ᵀ * (F x₀).map star).det).re := ⟨_, rfl⟩
  have hmpos : 0 < m := by rw [hm]; exact hGpos x₀ hx₀K
  have hA0 : 0 ≤ c⁻¹ ^ k * |M| := mul_nonneg (pow_nonneg (inv_nonneg.2 hc.le) k) (abs_nonneg M)
  have hB0 : 0 ≤ |C| ^ k / m := div_nonneg (pow_nonneg (abs_nonneg C) k) hmpos.le
  refine ⟨c⁻¹ ^ k * |M| + |C| ^ k / m + 1, by linarith, ?_⟩
  intro x hx Y r hr h1 h2 d
  have hd : d = (((F x)ᵀ * (Y⁻¹).map Complex.ofReal * (F x).map star).det).re := rfl
  rcases Nat.eq_zero_or_pos g with hg0 | hgpos
  · subst hg0
    have hk : k = 0 := by
      have := Matrix.rank_le_height (F x)
      rw [hrank x hx] at this
      omega
    subst hk
    have hd1 : d = 1 := by
      rw [hd, Matrix.det_isEmpty, Complex.one_re]
    rw [hd1]
    simp only [pow_zero, one_mul, mul_one] at hA0 hB0 ⊢
    refine ⟨?_, ?_⟩ <;> linarith
  · have hdiag := (h1.add h2).diag_nonneg (i := ⟨0, hgpos⟩)
    have hcr : c ≤ C * r := by
      simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq] at hdiag
      linarith
    have hCr : 0 < C * r := lt_of_lt_of_le hc hcr
    have hr0 : 0 < r := by linarith
    have hC : 0 < C := by nlinarith
    have hinv := subframe_inv_bounds Y hc hCr h1 h2
    have hb := subframe_det_bounds ((F x).map star) ((Y⁻¹).map Complex.ofReal)
      (inv_nonneg.2 hCr.le) hinv.1 hinv.2
    rw [hT] at hb
    obtain ⟨hlo, hhi⟩ := hb
    have hGx_le : (((F x)ᵀ * (F x).map star).det).re ≤ |M| := by
      have := hM x hx
      simp only [Real.norm_eq_abs] at this
      exact le_trans (le_abs_self _) (le_trans this (le_abs_self M))
    have hGx_ge : m ≤ (((F x)ᵀ * (F x).map star).det).re := by
      have := isMinOn_iff.mp hx₀ x hx
      rw [hm]; exact this
    rw [hd]
    generalize (((F x)ᵀ * (Y⁻¹).map Complex.ofReal * (F x).map star).det).re = D at hlo hhi ⊢
    generalize (((F x)ᵀ * (F x).map star).det).re = Gx at hlo hhi hGx_le hGx_ge
    have hpk : 0 < (C * r)⁻¹ ^ k := pow_pos (inv_pos.2 hCr) k
    refine ⟨?_, ?_⟩
    · have h3 : c⁻¹ ^ k * Gx ≤ c⁻¹ ^ k * |M| :=
        mul_le_mul_of_nonneg_left hGx_le (pow_nonneg (inv_nonneg.2 hc.le) k)
      linarith
    · have hDlo : (C * r)⁻¹ ^ k * m ≤ D := le_trans (mul_le_mul_of_nonneg_left hGx_ge hpk.le) hlo
      have hone : |C| ^ k / m * r ^ k * ((C * r)⁻¹ ^ k * m) = 1 := by
        rw [abs_of_pos hC, inv_pow, mul_pow]
        field_simp
      calc (1 : ℝ) = |C| ^ k / m * r ^ k * ((C * r)⁻¹ ^ k * m) := hone.symm
        _ ≤ (c⁻¹ ^ k * |M| + |C| ^ k / m + 1) * r ^ k * D := by
          apply mul_le_mul _ hDlo (mul_nonneg hpk.le hmpos.le)
          · exact mul_nonneg (by linarith) (pow_nonneg hr0.le k)
          · exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hr0.le k)

end GlobalTheory.CompanionTheory.Ar.Flat
end

section
open Matrix Metric GroundTheory.Heights₂.Heights.Regular GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_matrix_local_trivialization : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : LogPeriods n a g Λ), ∃ (Q : PeriodPolydisc n a g) (A : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ i j, DifferentiableOn ℂ (fun z => A z i j) (ball 0 1)) ∧ (A 0).det ≠ 0 ∧ ∀ w ∈ logCover L.a_le, A (expCover a w) * L.H (expCover a w) * (A (expCover a w))ᴴ = (((Q.τ w).map Complex.im)⁻¹).map Complex.ofReal := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_periodPolydisc_frame | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_periodPolydisc_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_periodPolydisc_frame <;> assumption)
end

section
open Matrix Metric GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

open scoped ComplexOrder

theorem frame_rank_of_gram_det_ne_zero {g k : ℕ} (M : Matrix (Fin g) (Fin k) ℂ)
    (h : (Mᵀ * M.map star).det ≠ 0) : M.rank = k := by
  have hu : IsUnit (Mᵀ * M.map star) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  have h1 := Matrix.rank_of_isUnit _ hu
  simp only [Fintype.card_fin] at h1
  have h2 := Matrix.rank_mul_le_left Mᵀ (M.map star)
  rw [Matrix.rank_transpose] at h2
  have h3 := M.rank_le_width
  omega

theorem frame_compact_nhd {g k : ℕ} (M₀ : Matrix (Fin g) (Fin k) ℂ) (h : M₀.rank = k) :
    ∃ S : Set (Matrix (Fin g) (Fin k) ℂ), IsCompact S ∧ S ∈ nhds M₀ ∧ ∀ M ∈ S, M.rank = k := by
  have hP : (M₀.map star)ᴴ = M₀ᵀ := by
    ext i j
    simp
  have hpos : 0 < ((M₀ᵀ * M₀.map star).det).re := by
    have := GlobalTheory.re_det_pos_of_posDef (subframe_gram_posDef M₀ h)
    rw [hP] at this
    exact this
  have hU : IsOpen {M : Matrix (Fin g) (Fin k) ℂ | 0 < ((Mᵀ * M.map star).det).re} :=
    isOpen_lt continuous_const subframe_continuous_det
  haveI : LocallyCompactSpace (Matrix (Fin g) (Fin k) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin g → Fin k → ℂ))
  obtain ⟨S, hS, hSU, hSc⟩ := local_compact_nhds (hU.mem_nhds hpos)
  refine ⟨S, hSc, hS, fun M hM => frame_rank_of_gram_det_ne_zero M ?_⟩
  intro h0
  have := hSU hM
  rw [Set.mem_setOf_eq, h0] at this
  simp at this

theorem continuousAt_matrix_inv {X : Type*} [TopologicalSpace X] {g : ℕ}
    (A : X → Matrix (Fin g) (Fin g) ℂ) (x : X) (hA : ContinuousAt A x) (h : (A x).det ≠ 0) :
    ContinuousAt (fun y => (A y)⁻¹) x := by
  have hd : ContinuousAt (fun y => (A y).det) x :=
    (continuous_id.matrix_det).continuousAt.comp hA
  have ha : ContinuousAt (fun y => (A y).adjugate) x :=
    (continuous_id.matrix_adjugate).continuousAt.comp hA
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact (hd.inv₀ h).smul ha

theorem chartRadius_le_log_sum {n a : ℕ} (h : a ≤ n) (z : Fin n → ℂ) (h1 : ∀ k, ‖z k‖ < 1)
    (h0 : ∀ i : Fin n, i.val < a → z i ≠ 0) :
    1 ≤ chartRadius h z ∧ chartRadius h z ≤ (Real.exp 1 + 2) *
      (1 + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖|) := by
  have hsum : ∑ j : Fin a, |Real.log ‖z (Fin.castLE h j)‖| =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| := by
    refine Finset.sum_bij (fun j _ => Fin.castLE h j) ?_ ?_ ?_ ?_
    · intro j _
      simp
    · intro j _ j' _ e
      exact Fin.castLE_injective h e
    · intro i hi
      have hi' : i.val < a := by simpa using hi
      exact ⟨⟨i.val, hi'⟩, Finset.mem_univ _, by ext; simp⟩
    · intro j _
      rfl
  have hterm : ∀ j : Fin a, Real.log (‖cuspCoord h z j‖ ^ 2)⁻¹ =
      2 * |Real.log ‖z (Fin.castLE h j)‖| := by
    intro j
    have hc : cuspCoord h z j = z (Fin.castLE h j) := rfl
    have hn : 0 ≤ ‖z (Fin.castLE h j)‖ := norm_nonneg _
    rw [hc, Real.log_inv, Real.log_pow, abs_of_nonpos (Real.log_nonpos hn (h1 _).le)]
    push_cast
    ring
  have hr : chartRadius h z = Real.exp 1 + 2 *
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| := by
    rw [chartRadius, ← hsum, Finset.mul_sum]
    simp only [hterm]
  have hS : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [hr]
  constructor
  · linarith
  · nlinarith

theorem logPeriods_subframe_det_bounds : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : LogPeriods n a g Λ) (k : ℕ) (F : (Fin n → ℂ) → Matrix (Fin k) (Fin g) ℂ), ContinuousAt F 0 → (F 0).rank = k → ∃ (ρ K : ℝ) (N : ℕ), 0 < ρ ∧ ρ ≤ 1 ∧ ∀ z ∈ ball (0 : Fin n → ℂ) ρ, (∀ i : Fin n, i.val < a → z i ≠ 0) → ‖(F z * L.H z * (F z)ᴴ).det‖ ≤ K ∧ 1 ≤ K * (1 + ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖|) ^ N * ‖(F z * L.H z * (F z)ᴴ).det‖ := by
  intro n a g Λ _ L k F hF hrk
  obtain ⟨Q, A, hAd, hA0, hAH⟩ := GlobalTheory.T.period_matrix_local_trivialization n a g Λ L
  obtain ⟨ρ₁, c, C, hρ₁, hρ₁1, hc, hb⟩ :=
    (ImTauBounds.cond RiemannExtensionSlices.proof PuncturedExpOrder.proof LogCoverDescent.proof) n a g Q
  have hAc : ContinuousAt A 0 := by
    have : ContinuousOn A (ball 0 1) :=
      continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hAd i j).continuousOn
    exact this.continuousAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))
  have hAi := continuousAt_matrix_inv A 0 hAc hA0
  have hc2 : Continuous (fun p : Matrix (Fin k) (Fin g) ℂ × Matrix (Fin g) (Fin g) ℂ => p.1 * p.2) :=
    continuous_fst.matrix_mul continuous_snd
  have hmul : ContinuousAt (fun z => F z * (A z)⁻¹) 0 :=
    ContinuousAt.comp (g := fun p : Matrix (Fin k) (Fin g) ℂ × Matrix (Fin g) (Fin g) ℂ => p.1 * p.2)
      (f := fun z => (F z, (A z)⁻¹)) hc2.continuousAt (hF.prodMk hAi)
  have hG : ContinuousAt (fun z => (F z * (A z)⁻¹)ᵀ) 0 :=
    (continuous_id.matrix_transpose.continuousAt).comp hmul
  have hM0 : ((F 0 * (A 0)⁻¹)ᵀ).rank = k := by
    have hu : IsUnit ((A 0)⁻¹).det := Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 hA0)
    rw [Matrix.rank_transpose, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hu, hrk]
  obtain ⟨S, hS, hSn, hSr⟩ := frame_compact_nhd _ hM0
  obtain ⟨C', hC', hd⟩ := subframe_det_log_growth g k (Matrix (Fin g) (Fin k) ℂ) S hS id
    continuousOn_id hSr c C hc
  have hdet : ContinuousAt (fun z => (A z).det) 0 :=
    (continuous_id.matrix_det).continuousAt.comp hAc
  have hev : ∀ᶠ z in nhds (0 : Fin n → ℂ), (F z * (A z)⁻¹)ᵀ ∈ S ∧ (A z).det ≠ 0 :=
    (hG.eventually_mem hSn).and (hdet.eventually_ne hA0)
  obtain ⟨ρ₂, hρ₂, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have he : 0 < Real.exp 1 + 2 := by positivity
  refine ⟨min (min ρ₁ ρ₂) 1, C' * (Real.exp 1 + 2) ^ k, k, lt_min (lt_min hρ₁ hρ₂) one_pos,
    min_le_right _ _, fun z hz hz0 => ?_⟩
  have hzρ : ‖z‖ < min (min ρ₁ ρ₂) 1 := by simpa [dist_zero_right] using hz
  have hz1n : ‖z‖ < 1 := lt_of_lt_of_le hzρ (min_le_right _ _)
  have hz1 : ∀ k, ‖z k‖ < 1 := fun k => lt_of_le_of_lt (norm_le_pi_norm z k) hz1n
  have hzρ₁ : z ∈ closedBall (0 : Fin n → ℂ) ρ₁ := by
    have : ‖z‖ ≤ ρ₁ := hzρ.le.trans ((min_le_left _ _).trans (min_le_left _ _))
    simpa [dist_zero_right] using this
  have hzρ₂ : z ∈ ball (0 : Fin n → ℂ) ρ₂ := by
    have : ‖z‖ < ρ₂ := lt_of_lt_of_le hzρ ((min_le_left _ _).trans (min_le_right _ _))
    simpa [dist_zero_right] using this
  obtain ⟨hGS, hAz⟩ := hball z hzρ₂
  have hcusp : ∀ j : Fin a, cuspCoord L.a_le z j ≠ 0 := fun j => hz0 _ (by simp)
  have hzp : z ∈ puncturedChart L.a_le (ball (0 : Fin n → ℂ) 1) :=
    ⟨by simpa [dist_zero_right] using hz1n, hcusp⟩
  have hw := HodgeDerivative.logLift_mem L.a_le hzp
  have hexp := HodgeDerivative.expCover_logLift L.a_le hcusp
  have hAHz := hAH _ hw
  rw [hexp] at hAHz
  obtain ⟨hb1, hb2⟩ := hb _ hw (by rw [hexp]; exact hzρ₁)
  rw [hexp] at hb2
  obtain ⟨hr1, hr2⟩ := chartRadius_le_log_sum L.a_le z hz1 hz0
  have hx := hd _ hGS ((Q.τ (logLift a z)).map Complex.im) (chartRadius L.a_le z) hr1 hb1 hb2
  set Y := (Q.τ (logLift a z)).map Complex.im with hY
  set S' := ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < a), |Real.log ‖z i‖| with hS'
  have hAu : IsUnit (A z).det := isUnit_iff_ne_zero.2 hAz
  have hinv1 : (A z)⁻¹ * A z = 1 := Matrix.nonsing_inv_mul _ hAu
  have hinv2 : (A z)ᴴ * ((A z)⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hinv1, Matrix.conjTranspose_one]
  have hkey : F z * L.H z * (F z)ᴴ = (F z * (A z)⁻¹) * (Y⁻¹).map Complex.ofReal * (F z * (A z)⁻¹)ᴴ := by
    rw [← hAHz, Matrix.conjTranspose_mul]
    have e : F z * (A z)⁻¹ * (A z * L.H z * (A z)ᴴ) * (((A z)⁻¹)ᴴ * (F z)ᴴ) =
        F z * ((A z)⁻¹ * A z) * L.H z * ((A z)ᴴ * ((A z)⁻¹)ᴴ) * (F z)ᴴ := by
      simp only [Matrix.mul_assoc]
    rw [e, hinv1, hinv2]
    simp
  have hd1 : ((F z * L.H z * (F z)ᴴ).det).re ≤ C' := by
    rw [hkey]
    exact hx.1
  have hd2 : 1 ≤ C' * chartRadius L.a_le z ^ k * ((F z * L.H z * (F z)ᴴ).det).re := by
    rw [hkey]
    exact hx.2
  have hpsd : (F z * L.H z * (F z)ᴴ).PosSemidef := by
    rw [hkey]
    have hYp : Y.PosDef := Q.im_posDef _ hw
    exact (subframe_map_posSemidef hYp.inv.posSemidef).mul_mul_conjTranspose_same _
  have hD := hpsd.det_nonneg
  obtain ⟨D, hDdef⟩ : ∃ D, D = (F z * L.H z * (F z)ᴴ).det := ⟨_, rfl⟩
  rw [← hDdef] at hd1 hd2 hD ⊢
  have hnorm : ‖D‖ = D.re := by
    obtain ⟨h1, h2⟩ := Complex.nonneg_iff.1 hD
    have e : D = (D.re : ℂ) := by
      apply Complex.ext <;> simp [h2.symm]
    rw [e, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re, abs_of_nonneg h1]
  rw [hnorm]
  have hre : 0 ≤ D.re := (Complex.nonneg_iff.1 hD).1
  have hS0 : 0 ≤ S' := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hE1 : 1 ≤ (Real.exp 1 + 2) ^ k := one_le_pow₀ (by linarith [Real.exp_pos 1])
  constructor
  · calc D.re ≤ C' := hd1
      _ ≤ C' * (Real.exp 1 + 2) ^ k := le_mul_of_one_le_right hC'.le hE1
  · have hpow : chartRadius L.a_le z ^ k ≤ ((Real.exp 1 + 2) * (1 + S')) ^ k :=
      pow_le_pow_left₀ (by linarith) hr2 k
    calc (1 : ℝ) ≤ C' * chartRadius L.a_le z ^ k * D.re := hd2
      _ ≤ C' * ((Real.exp 1 + 2) * (1 + S')) ^ k * D.re := by gcongr
      _ = C' * (Real.exp 1 + 2) ^ k * (1 + S') ^ k * D.re := by rw [mul_pow]; ring

end GlobalTheory.CompanionTheory.Ar.Flat
end
