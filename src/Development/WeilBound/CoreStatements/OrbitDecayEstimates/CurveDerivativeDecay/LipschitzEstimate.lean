import Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.KFiniteWordBoundIndefUnitary
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FrobeniusBoundOfMulNearOne
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CoefDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigZeroDecay
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HeBranching

section
open MeasureTheory Matrix Topology Metric Formalism.REAL
open scoped ENNReal

noncomputable section

namespace CompanionTheory.Lime.T3

section frob

open scoped Matrix.Norms.Frobenius

theorem hs_box {n : ℕ} {u : Matrix (Fin n) (Fin n) ℂ} {s : ℝ} (h : ∀ i j, ‖u i j‖ ≤ s) : hs u ≤ (n * s) ^ 2 := by
  unfold hs
  calc ∑ i, ∑ j, ‖u i j‖ ^ 2 ≤ ∑ _i : Fin n, ∑ _j : Fin n, s ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (h i j) 2
    _ = (n * s) ^ 2 := by simp; ring

theorem near_one {n : ℕ} {k u v : Matrix (Fin n) (Fin n) ℂ} {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2)
    (hu : hs (u - 1) ≤ t ^ 2) (hv : hs (v - 1) ≤ t ^ 2) (h : k * u = v) : hs (k - 1) ≤ (4 * t) ^ 2 := by
  rw [frobenius_eq_norm_sq] at hu hv ⊢
  have hu' : ‖u - 1‖ ≤ t := (pow_le_pow_iff_left₀ (norm_nonneg _) ht0 two_ne_zero).1 hu
  have hv' : ‖v - 1‖ ≤ t := (pow_le_pow_iff_left₀ (norm_nonneg _) ht0 two_ne_zero).1 hv
  have e : k - 1 = (v - 1) - (k - 1) * (u - 1) - (u - 1) := by rw [← h]; noncomm_ring
  have h1 : ‖k - 1‖ ≤ ‖v - 1‖ + ‖k - 1‖ * ‖u - 1‖ + ‖u - 1‖ := by
    calc ‖k - 1‖ = ‖(v - 1) - (k - 1) * (u - 1) - (u - 1)‖ := by rw [← e]
      _ ≤ ‖(v - 1) - (k - 1) * (u - 1)‖ + ‖u - 1‖ := norm_sub_le _ _
      _ ≤ ‖v - 1‖ + ‖(k - 1) * (u - 1)‖ + ‖u - 1‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ _ := by gcongr; exact Matrix.frobenius_norm_mul _ _
  have h2 : ‖k - 1‖ * ‖u - 1‖ ≤ ‖k - 1‖ * (1 / 2) := mul_le_mul_of_nonneg_left (hu'.trans ht) (norm_nonneg _)
  exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2

theorem entry_le {n : ℕ} {g u : Matrix (Fin n) (Fin n) ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hg : hs g ≤ R ^ 2) (hu : hs (u - 1) ≤ (1 / 2) ^ 2) (i j : Fin n) : ‖(g * u) i j‖ ≤ R * (Real.sqrt n + 1) := by
  rw [frobenius_eq_norm_sq] at hg hu
  have hg' : ‖g‖ ≤ R := (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).1 hg
  have hu1 : ‖u - 1‖ ≤ 1 / 2 := (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).1 hu
  have hu' : ‖u‖ ≤ Real.sqrt n + 1 := by
    calc ‖u‖ = ‖1 + (u - 1)‖ := by rw [add_sub_cancel]
      _ ≤ ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ + ‖u - 1‖ := norm_add_le _ _
      _ ≤ _ := by rw [norm_one_matrix_eq_sqrt]; linarith
  have he : ‖(g * u) i j‖ ≤ ‖g * u‖ := by
    have := f1auxiliary_entry_le (g * u) i j
    rw [frobenius_eq_norm_sq] at this
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  calc ‖(g * u) i j‖ ≤ ‖g * u‖ := he
    _ ≤ ‖g‖ * ‖u‖ := Matrix.frobenius_norm_mul _ _
    _ ≤ R * (Real.sqrt n + 1) := by gcongr

end frob

def nearSet {n : ℕ} (ε : Fin n → Bool) (δ : ℝ) : Set (UJ ε) := {k | hs (coeMatrixAlt ε k - 1) ≤ δ ^ 2}

theorem vol_ratio {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [SFinite μ] [μ.IsMulLeftInvariant]
    {δ R : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 2) (hR0 : 0 ≤ R) :
    μ {g | hsG g ≤ R ^ 2} ≤ ENNReal.ofReal ((4 * n * (Real.sqrt n + 1) * R / δ) ^ (2 * n ^ 2)) * μ (nearSet ε δ) := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let lam : Measure (MatrixCoordinates n) := Measure.addHaar
  set s : ℝ := δ / (4 * n) with hs_def
  have hs0 : 0 < s := by positivity
  have hns : n * s = δ / 4 := by rw [hs_def]; field_simp
  let O : Set (MatrixCoordinates n) := closedBall (Matrix.of.symm 1) s
  have hO : ∀ x ∈ O, hs (Matrix.of x - 1) ≤ (δ / 4) ^ 2 := by
    intro x hx
    rw [← hns]
    refine hs_box fun i j => ?_
    set o : MatrixCoordinates n := Matrix.of.symm 1 with ho
    have h1 : ‖x - o‖ ≤ s := by rwa [← mem_closedBall_iff_norm]
    exact ((norm_le_pi_norm ((x - o) i) j).trans (norm_le_pi_norm (x - o) i)).trans h1
  have hof : Continuous (fun x : MatrixCoordinates n => Matrix.of x) := continuous_id
  have hofs : Continuous (fun x : Matrix (Fin n) (Fin n) ℂ => (Matrix.of.symm x : MatrixCoordinates n)) := continuous_id
  have hfr : Module.finrank ℝ (MatrixCoordinates n) = 2 * n ^ 2 := by
    simp [MatrixCoordinates, Module.finrank_pi_fintype, Complex.finrank_real_complex]; ring
  have hB_pos : 0 < lam (ball 0 1) := measure_ball_pos lam _ one_pos
  have hB_fin : lam (ball 0 1) < ⊤ := measure_ball_lt_top
  have hOv : lam O = ENNReal.ofReal (s ^ (2 * n ^ 2)) * lam (ball 0 1) := by
    rw [Measure.addHaar_closedBall lam _ hs0.le, hfr]
  set W := nearSet ε δ
  set ρ : ℝ := R * (Real.sqrt n + 1) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  set S : Set (UJ ε) := {g | hsG g ≤ R ^ 2} with hS
  have hS_meas : MeasurableSet S :=
    (isClosed_le (continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)) continuous_const).measurableSet
  let Φ : UJ ε × MatrixCoordinates n → MatrixCoordinates n := fun p => leftMulReal (coeMatrixAlt ε p.1⁻¹) p.2
  have hΦ : Continuous Φ := by
    show Continuous fun p : UJ ε × MatrixCoordinates n =>
      (Matrix.of.symm (coeMatrixAlt ε p.1⁻¹ * Matrix.of p.2) : MatrixCoordinates n)
    exact hofs.comp (((continuous_coeMatrix ε).comp (continuous_inv.comp continuous_fst)).matrix_mul
      (hof.comp continuous_snd))
  let T : Set (UJ ε × MatrixCoordinates n) := {p | hsG p.1 ≤ R ^ 2} ∩ Φ ⁻¹' O
  have hT : MeasurableSet T :=
    (isClosed_le ((continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)).comp continuous_fst)
      continuous_const).measurableSet.inter (isClosed_closedBall.preimage hΦ).measurableSet
  have h1 : (μ.prod lam) T = μ S * lam O := by
    rw [Measure.prod_apply hT]
    have : ∀ g, lam (Prod.mk g ⁻¹' T) = S.indicator (fun _ => lam O) g := by
      intro g
      by_cases hg : g ∈ S
      · rw [Set.indicator_of_mem hg]
        have hdet : LinearMap.det (leftMulReal (coeMatrixAlt ε g⁻¹)) = 1 := det_leftMulReal_eq_one (g⁻¹).2
        have e : Prod.mk g ⁻¹' T = leftMulReal (coeMatrixAlt ε g⁻¹) ⁻¹' O := by
          ext x
          simp only [T, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, Φ]
          exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
        rw [e, Measure.addHaar_preimage_linearMap lam (by rw [hdet]; exact one_ne_zero), hdet]
        simp
      · rw [Set.indicator_of_notMem hg]
        have e : Prod.mk g ⁻¹' T = ∅ := by
          ext x
          simp only [T, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq,
            Set.mem_empty_iff_false, iff_false, not_and]
          exact fun h => absurd h hg
        rw [e, measure_empty]
    simp_rw [this]
    rw [lintegral_indicator_const hS_meas, mul_comm]
  have hq : (δ / 4) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h2 : (μ.prod lam) T ≤ μ W * lam (closedBall 0 ρ) := by
    rw [Measure.prod_apply_symm hT]
    calc ∫⁻ x, μ ((fun g => (g, x)) ⁻¹' T) ∂lam
        ≤ ∫⁻ x, (closedBall (0 : MatrixCoordinates n) ρ).indicator (fun _ => μ W) x ∂lam := by
          refine lintegral_mono fun x => ?_
          by_cases hne : ((fun g => (g, x)) ⁻¹' T).Nonempty
          · obtain ⟨h, hh⟩ := hne
            have hh1 : hsG h ≤ R ^ 2 := hh.1
            have hh2 := hO _ hh.2
            simp only [Φ] at hh2
            rw [of_leftMulReal_apply] at hh2
            have hx : x ∈ closedBall (0 : MatrixCoordinates n) ρ := by
              rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hρ0]
              intro i
              rw [pi_norm_le_iff_of_nonneg hρ0]
              intro j
              have := entry_le (g := coeMatrixAlt ε h) hR0 hh1 (hh2.trans hq) i j
              rw [← Matrix.mul_assoc, determinant_character_mul_inv, Matrix.one_mul] at this
              exact this
            rw [Set.indicator_of_mem hx]
            calc μ ((fun g => (g, x)) ⁻¹' T) ≤ μ ((fun g => h⁻¹ * g) ⁻¹' W) := by
                  refine measure_mono fun g hg => ?_
                  have hg2 := hO _ hg.2
                  simp only [Φ] at hg2
                  rw [of_leftMulReal_apply] at hg2
                  show hs (coeMatrixAlt ε (h⁻¹ * g) - 1) ≤ δ ^ 2
                  have := near_one (k := coeMatrixAlt ε (h⁻¹ * g)) (by positivity) (by linarith) hg2 hh2 (by
                    rw [determinant_character_mul, ← Matrix.mul_assoc, Matrix.mul_assoc (coeMatrixAlt ε h⁻¹),
                      determinant_character_mul_inv, Matrix.mul_one])
                  rwa [show 4 * (δ / 4) = δ by ring] at this
              _ = μ W := measure_preimage_mul μ h⁻¹ W
          · rw [Set.not_nonempty_iff_eq_empty.1 hne, measure_empty]
            exact bot_le
      _ = μ W * lam (closedBall 0 ρ) := lintegral_indicator_const measurableSet_closedBall _
  have h3 : lam (closedBall 0 ρ) = ENNReal.ofReal (ρ ^ (2 * n ^ 2)) * lam (ball 0 1) := by
    rw [Measure.addHaar_closedBall lam _ hρ0, hfr]
  have hO0 : lam O ≠ 0 := by
    rw [hOv]; exact mul_ne_zero (ENNReal.ofReal_pos.2 (by positivity)).ne' hB_pos.ne'
  have hOt : lam O ≠ ⊤ := measure_closedBall_lt_top.ne
  refine (ENNReal.mul_le_mul_iff_left hO0 hOt).1 ?_
  rw [← h1]
  refine h2.trans (le_of_eq ?_)
  have e : ρ ^ (2 * n ^ 2) = (4 * n * (Real.sqrt n + 1) * R / δ) ^ (2 * n ^ 2) * s ^ (2 * n ^ 2) := by
    rw [← mul_pow]
    congr 1
    rw [hρ, hs_def]
    field_simp
  rw [h3, hOv, e, ENNReal.ofReal_mul (by positivity)]
  ring

theorem one_le_hsG {n : ℕ} (hn : 1 ≤ n) {ε : Fin n → Bool} (g : UJ ε) : 1 ≤ hsG g := by
  let j : Fin n := ⟨0, hn⟩
  have hg : inUJ ε (coeMatrixAlt ε g) := g.2
  have h1 := congrFun (congrFun hg j) j
  have h2 : ((coeMatrixAlt ε g)ᴴ * Jm ε * coeMatrixAlt ε g) j j =
      ∑ i, (if ε i then 1 else -1) * (((‖coeMatrixAlt ε g i j‖ ^ 2 : ℝ)) : ℂ) := by
    simp only [Jm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := Complex.conj_mul' (coeMatrixAlt ε g i j)
    split_ifs <;> simp [← this]
  have h3 : ‖Jm ε j j‖ = 1 := by simp only [Jm, Matrix.diagonal_apply_eq]; split_ifs <;> simp
  have h4 : (1 : ℝ) ≤ ∑ i, ‖coeMatrixAlt ε g i j‖ ^ 2 := by
    rw [← h3, ← h1, h2]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    split_ifs <;> simp
  refine h4.trans ?_
  show _ ≤ ∑ i, ∑ k, ‖coeMatrixAlt ε g i k‖ ^ 2
  exact Finset.sum_le_sum fun i _ =>
    Finset.single_le_sum (f := fun k => ‖coeMatrixAlt ε g i k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)

theorem int_ratio {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [SFinite μ] [μ.IsMulLeftInvariant]
    {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 2) {A : ℕ} (hA : 2 * n ^ 2 + 1 ≤ A) :
    ∫⁻ g, ENNReal.ofReal ((Real.sqrt (hsG g))⁻¹ ^ A) ∂μ ≤
      ENNReal.ofReal (2 * (8 * n * (Real.sqrt n + 1) / δ) ^ (2 * n ^ 2)) * μ (nearSet ε δ) := by
  set c : ℝ := 8 * n * (Real.sqrt n + 1) / δ with hc
  have hc0 : 0 ≤ c := by positivity
  let S : ℕ → Set (UJ ε) := fun j => {g | hsG g ≤ ((2 : ℝ) ^ (j + 1)) ^ 2}
  have hSm : ∀ j, MeasurableSet (S j) := fun j =>
    (isClosed_le (continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)) continuous_const).measurableSet
  have hpt : ∀ g : UJ ε, ENNReal.ofReal ((Real.sqrt (hsG g))⁻¹ ^ A) ≤
      ∑' j, (S j).indicator (fun _ => ENNReal.ofReal (((2 : ℝ) ^ j)⁻¹ ^ A)) g := by
    intro g
    have h1 : 1 ≤ Real.sqrt (hsG g) := Real.one_le_sqrt.2 (one_le_hsG hn g)
    obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near h1 (by norm_num : (1 : ℝ) < 2)
    refine le_trans ?_ (ENNReal.le_tsum j)
    have hmem : g ∈ S j := by
      show hsG g ≤ _
      rw [← Real.sq_sqrt (le_trans zero_le_one (one_le_hsG hn g))]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hj2.le 2
    rw [Set.indicator_of_mem hmem]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) (inv_anti₀ (by positivity) hj1) A)
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_tsum fun j => (measurable_const.indicator (hSm j)).aemeasurable]
  have hterm : ∀ j, ∫⁻ g, (S j).indicator (fun _ => ENNReal.ofReal (((2 : ℝ) ^ j)⁻¹ ^ A)) g ∂μ ≤
      ENNReal.ofReal (c ^ (2 * n ^ 2) * (1 / 2) ^ j) * μ (nearSet ε δ) := by
    intro j
    rw [lintegral_indicator_const (hSm j)]
    refine (mul_le_mul_right (vol_ratio hn ε μ hδ hδ2 (by positivity)) _).trans ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    have e : 4 * n * (Real.sqrt n + 1) * (2 : ℝ) ^ (j + 1) / δ = c * 2 ^ j := by rw [hc]; ring
    have h2 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have h3 : ((2 : ℝ) ^ j)⁻¹ ^ A ≤ ((2 : ℝ) ^ j)⁻¹ ^ (2 * n ^ 2 + 1) :=
      pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ h2) hA
    have h4 : ((2 : ℝ) ^ j)⁻¹ ^ (2 * n ^ 2 + 1) * (c * 2 ^ j) ^ (2 * n ^ 2) = c ^ (2 * n ^ 2) * (1 / 2) ^ j := by
      rw [mul_pow, pow_succ, inv_pow, one_div, inv_pow]
      field_simp
    rw [e, ← h4]
    exact mul_le_mul_of_nonneg_right h3 (by positivity)
  refine (ENNReal.tsum_le_tsum hterm).trans (le_of_eq ?_)
  rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
    (summable_geometric_two.mul_left _), tsum_mul_left, tsum_geometric_two, mul_comm (c ^ _)]

end CompanionTheory.Lime.T3
end
end

section
noncomputable section

open Matrix Finset MeasureTheory Formalism.REAL Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.Lime.T3

def nG {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : ℝ := Real.sqrt (hs (uMat g))

theorem nG_mul {m : ℕ} {ε : Fin m → Bool} (g h : UJ ε) : nG (g * h) ≤ nG g * nG h := sqrt_frobenius_mul_le _ _

theorem one_le_nG {m : ℕ} (hm : 1 ≤ m) {ε : Fin m → Bool} (g : UJ ε) : 1 ≤ nG g :=
  Real.one_le_sqrt.2 (one_le_hsG hm g)

theorem nG_sq {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : nG g ^ 2 = hs (uMat g) :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)

theorem uMat_inv {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : uMat g⁻¹ = Jm ε * (uMat g)ᴴ * Jm ε := by
  have hg : (uMat g)ᴴ * Jm ε * uMat g = Jm ε := g.2
  have e : uMat g * uMat g⁻¹ = 1 := determinant_character_mul_inv g
  calc uMat g⁻¹ = Jm ε * Jm ε * uMat g⁻¹ := by rw [Jm_mul_self, Matrix.one_mul]
    _ = Jm ε * ((uMat g)ᴴ * Jm ε * uMat g) * uMat g⁻¹ := by rw [hg]
    _ = Jm ε * (uMat g)ᴴ * Jm ε * (uMat g * uMat g⁻¹) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [e, Matrix.mul_one]

theorem hs_conjJ {m : ℕ} (ε : Fin m → Bool) (M : Matrix (Fin m) (Fin m) ℂ) : hs (Jm ε * Mᴴ * Jm ε) = hs M := by
  unfold hs
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, norm_mul, norm_star]
  split_ifs <;> simp

theorem nG_inv {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : nG g⁻¹ = nG g := by
  unfold nG
  rw [uMat_inv, hs_conjJ]

theorem hs_inv_sub_one {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) : hs (uMat g⁻¹ - 1) = hs (uMat g - 1) := by
  rw [← hs_conjJ ε (uMat g - 1), uMat_inv, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_one, Jm_mul_self]

theorem hs_of_compact {m : ℕ} {ε : Fin m → Bool} (hc : ∀ a b, ε a = ε b) (g : UJ ε) : hs (uMat g) = m := by
  have hg : (uMat g)ᴴ * Jm ε * uMat g = Jm ε := g.2
  unfold hs
  rw [Finset.sum_comm]
  have : ∀ j, ∑ i, ‖uMat g i j‖ ^ 2 = 1 := by
    intro j
    have h1 := congrFun (congrFun hg j) j
    simp only [Jm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    have h2 : ∀ i, (if ε i = true then star (uMat g i j) * 1 else star (uMat g i j) * -1) * uMat g i j =
        (if ε j = true then 1 else -1) * ((‖uMat g i j‖ ^ 2 : ℝ) : ℂ) := by
      intro i
      have := Complex.conj_mul' (uMat g i j)
      rw [hc i j]
      split_ifs <;> simp [← this]
    simp only [h2, ← Finset.mul_sum] at h1
    have h3 : (∑ i, ((‖uMat g i j‖ ^ 2 : ℝ) : ℂ)) = 1 := by
      split_ifs at h1
      · simpa using h1
      · linear_combination -h1
    exact_mod_cast h3
  simp [this]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem dec_low {m N : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} (hm : 1 ≤ m)
    (hmN : m ≤ N) (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hDS : IsDS ε lam π)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * (N : ℝ) ^ 3)) {v : H} (hv : v ∈ lowKSub ε lam π) (hv1 : ‖v‖ = 1)
    {A : ℕ} (hA1 : 1 ≤ A) (hA : A ≤ 12 * N ^ 2) (g : UJ ε) :
    ‖⟪v, π (uMat g) v⟫_ℂ‖ ≤ (Real.exp 1 * Real.sqrt m) ^ A * (nG g)⁻¹ ^ A := by
  have : CompleteSpace H := hDS.1
  have hm2 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hN2 : (m : ℝ) ≤ N := by exact_mod_cast hmN
  by_cases hcp : ∀ a b, ε a = ε b
  · have h1 := norm_inner_le_norm (𝕜 := ℂ) v (π (uMat g) v)
    rw [hDS.2.2.1.2.1 _ g.2, hv1, one_mul] at h1
    have h2 : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (by linarith)
    unfold nG
    rw [hs_of_compact hcp, ← mul_pow, mul_assoc, mul_inv_cancel₀ h2.ne', mul_one]
    exact h1.trans (one_le_pow₀ (Real.one_le_exp zero_le_one))
  have hpq' : (∃ a, ε a = true) ∧ ∃ a, ε a = false := by
    push_neg at hcp
    obtain ⟨a, b, hab⟩ := hcp
    cases ha : ε a <;> cases hb : ε b <;> simp_all <;> exact ⟨⟨_, ‹_›⟩, ⟨_, ‹_›⟩⟩
  obtain ⟨hp, hq⟩ := hpq'
  set h : ℝ := 200 * (N : ℝ) ^ 3 with hh
  have hN3 : (m : ℝ) ^ 3 ≤ N ^ 3 := pow_le_pow_left₀ (by linarith) hN2 3
  have hm3 : (1 : ℝ) ≤ m ^ 3 := one_le_pow₀ hm2
  have hpm : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) ≤ m := by
    exact_mod_cast (Finset.card_filter_le _ _).trans_eq (Finset.card_fin m)
  have hqm : (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤ m := by
    exact_mod_cast (Finset.card_filter_le _ _).trans_eq (Finset.card_fin m)
  have hq1 : 1 ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 ε := by
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact le_min (Finset.card_pos.2 ⟨a, by simp [ha]⟩) (Finset.card_pos.2 ⟨b, by simp [hb]⟩)
  have hq0 : (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ m := le_trans (by exact_mod_cast min_le_left _ _) hpm
  have hq1' : (1 : ℝ) ≤ ReciprocityTheory.ChartRestriction.DS.S7.q0 ε := by exact_mod_cast hq1
  have hmm : (m : ℝ) ^ 2 ≤ m ^ 3 := by nlinarith
  have hpq : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) * ReciprocityTheory.ChartRestriction.DS.qOf ε ≤ m * m :=
    mul_le_mul hpm hqm (Nat.cast_nonneg _) (by linarith)
  obtain ⟨k, X, hX, e⟩ := ReciprocityTheory.ChartRestriction.DS.S7.polar_exists (ε := ε) (g := uMat g) g.2
  have hd := ReciprocityTheory.ChartRestriction.DS.coef_dec_of_isDS hDS hl hg hq1 (by nlinarith) (by nlinarith) ⟨hv1, hv⟩ k hX
  rw [← e] at hd
  set c := Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ)) with hc
  have hc1 : 1 ≤ c := Real.one_le_sqrt.2 (by linarith)
  have hcm : c ≤ 2 * N := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  set s := Real.sqrt (ReciprocityTheory.ChartRestriction.DS.S7.hs X) with hs_def
  have hsX : ReciprocityTheory.ChartRestriction.DS.S7.hs X = s ^ 2 := (Real.sq_sqrt (ReciprocityTheory.ChartRestriction.DS.S7.hs_nonnegVG X)).symm
  have hG1 := one_le_nG hm g
  have hN : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hGle : nG g ≤ Real.sqrt m * Real.exp s := by
    unfold nG
    rw [e]
    change Real.sqrt (ReciprocityTheory.ChartRestriction.DS.S7.hs _) ≤ _
    rw [ReciprocityTheory.ChartRestriction.DS.S7.hs_kmulVG, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have e2 : Real.exp s ^ 2 = Real.exp (2 * s) := by rw [← Real.exp_nat_mul]; norm_num
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m), e2]
    exact ReciprocityTheory.ChartRestriction.DS.S7.hs_exp_leVG X
  have hA' : (A : ℝ) ≤ 12 * N ^ 2 := by exact_mod_cast hA
  have hA1' : (1 : ℝ) ≤ A := by exact_mod_cast hA1
  have hr := ReciprocityTheory.ChartRestriction.DS.sigZeroDecay_real (h := 8 * c * A) (s := s) (by positivity) hc1 hN (by linarith) hGle
  rw [show 8 * c * A / (8 * c) = (A : ℝ) by field_simp, Real.rpow_neg (by linarith), Real.rpow_natCast,
    Real.rpow_natCast, ← inv_pow] at hr
  rw [hsX] at hd
  have hmin : 0 ≤ min (s ^ 2) (s / c) := le_min (by positivity) (by positivity)
  have hle : 8 * c * A ≤ h := by
    have : c * A ≤ (2 * N) * (12 * N ^ 2) := mul_le_mul hcm hA' (by linarith) (by linarith)
    nlinarith
  refine hd.trans ((Real.exp_le_exp.2 (by nlinarith)).trans (hr.trans (le_of_eq ?_)))
  rw [show Real.exp (A : ℝ) = Real.exp 1 ^ A by rw [← Real.exp_nat_mul, mul_one], ← mul_pow]

theorem dec_conj {m : ℕ} {ε : Fin m → Bool} {π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} (hm : 1 ≤ m)
    (hπ : IsURepOn (UJset ε) π) {v : H} {C : ℝ} (hC : 0 ≤ C) {A : ℕ}
    (hd : ∀ g : UJ ε, ‖⟪v, π (uMat g) v⟫_ℂ‖ ≤ C * (nG g)⁻¹ ^ A) (g₀ g : UJ ε) :
    ‖⟪π (uMat g₀) v, π (uMat g) (π (uMat g₀) v)⟫_ℂ‖ ≤ C * hs (uMat g₀) ^ A * (nG g)⁻¹ ^ A := by
  let U : H →ₗᵢ[ℂ] H := ⟨(π (uMat g₀)).toLinearMap, hπ.2.1 _ g₀.2⟩
  have e : π (uMat g) (π (uMat g₀) v) = π (uMat g₀) (π (uMat (g₀⁻¹ * g * g₀)) v) := by
    have h1 := hπ.1.2 (uMat g) g.2 (uMat g₀) g₀.2
    have h2 := hπ.1.2 (uMat g₀) g₀.2 (uMat (g₀⁻¹ * g * g₀)) (g₀⁻¹ * g * g₀).2
    have h3 : uMat g₀ * uMat (g₀⁻¹ * g * g₀) = uMat g * uMat g₀ := by
      change uMat (g₀ * (g₀⁻¹ * g * g₀)) = uMat (g * g₀)
      congr 1
      group
    rw [← ContinuousLinearMap.comp_apply, ← h1, ← h3, h2, ContinuousLinearMap.comp_apply]
  have e2 := U.inner_map_map v (π (uMat (g₀⁻¹ * g * g₀)) v)
  rw [e]
  change ‖⟪U v, U _⟫_ℂ‖ ≤ _
  rw [e2]
  refine (hd _).trans ?_
  rw [mul_assoc C, ← mul_pow]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by unfold nG; positivity) ?_ A) hC
  have h1 : nG g ≤ nG g₀ * nG (g₀⁻¹ * g * g₀) * nG g₀ := by
    calc nG g = nG (g₀ * (g₀⁻¹ * g * g₀) * g₀⁻¹) := by congr 1; group
      _ ≤ nG (g₀ * (g₀⁻¹ * g * g₀)) * nG g₀⁻¹ := nG_mul _ _
      _ ≤ _ := by rw [nG_inv]; exact mul_le_mul_of_nonneg_right (nG_mul _ _) (by unfold nG; positivity)
  have h2 := one_le_nG hm g
  have h3 := one_le_nG hm (g₀⁻¹ * g * g₀)
  rw [← nG_sq, ← div_eq_mul_inv, le_div_iff₀ (by linarith), inv_mul_le_iff₀ (by linarith)]
  nlinarith

theorem nearSet_lt_top {m : ℕ} (ε : Fin m → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] : μ (nearSet ε 1) < ⊤ := by
  have hc : IsCompact {g : UJ ε | hsG g ≤ (Real.sqrt m + 1) ^ 2} := by
    have := (isClosedEmbeddingMatrix m ε).1.isCompact_preimage ((hermitian_small_ball m ε).1 ((Real.sqrt m + 1) ^ 2))
    convert this using 1
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hsG]
    exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
  refine (measure_mono fun g hg => ?_).trans_lt hc.measure_lt_top
  have h1 := sqrt_frobenius_add_le (1 : Matrix (Fin m) (Fin m) ℂ) (coeMatrixAlt ε g - 1)
  rw [add_sub_cancel, f1auxiliary_hs_one] at h1
  have h2 : Real.sqrt (hs (coeMatrixAlt ε g - 1)) ≤ 1 := Real.sqrt_le_iff.2 ⟨zero_le_one, hg⟩
  show hs (coeMatrixAlt ε g) ≤ _
  rw [← Real.sqrt_le_left (by positivity)]
  linarith

theorem integrable_of_dec {m : ℕ} {ε : Fin m → Bool} (hm : 1 ≤ m) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] {f : UJ ε → ℂ}
    (hf : Continuous f) {C : ℝ} (hC : 0 ≤ C) {A : ℕ} (hA : 2 * m ^ 2 + 1 ≤ A) (hd : ∀ g, ‖f g‖ ≤ C * (nG g)⁻¹ ^ A) :
    Integrable f μ := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  have h1 := int_ratio hm ε μ one_pos (by norm_num) hA
  calc ∫⁻ g, ‖f g‖ₑ ∂μ ≤ ∫⁻ g, ENNReal.ofReal C * ENNReal.ofReal ((Real.sqrt (hsG g))⁻¹ ^ A) ∂μ := by
        refine lintegral_mono fun g => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_mul hC]
        exact ENNReal.ofReal_le_ofReal (hd g)
    _ = ENNReal.ofReal C * ∫⁻ g, ENNReal.ofReal ((Real.sqrt (hsG g))⁻¹ ^ A) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (h1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (nearSet_lt_top ε μ)))

end CompanionTheory.Lime.T3
end
end

section
noncomputable section

open Matrix Finset MeasureTheory Formalism.REAL Formalism.MainNotions.S Filter Topology
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.Lime.T3

open ReciprocityTheory.ChartRestriction.DS (smD smE actM dS IsSmoothVecU mem_smD_iff isDerivedOn_smE dS_eq_actM)

variable {m : ℕ} {ε : Fin m → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)}

section Sup

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem inG_of_curve {c : ℝ → Matrix (Fin m) (Fin m) ℂ} {Y : Matrix (Fin m) (Fin m) ℂ} (h0 : c 0 = 1)
    (hc : HasDerivAt c Y 0) (hG : ∀ᶠ s in 𝓝 (0 : ℝ), inUJ ε (c s)) : inG ε Y := by
  unfold inG
  ext i j
  have he : ∀ a b, HasDerivAt (fun s => c s a b) (Y a b) 0 := fun a b =>
    (hasDerivAt_pi.1 (hasDerivAt_pi.1 hc a) b)
  have h1 : HasDerivAt (fun s => ∑ a, star (c s a i) * (if ε a then 1 else -1) * c s a j)
      (∑ a, (star (Y a i) * (if ε a then 1 else -1) * c 0 a j + star (c 0 a i) * (if ε a then 1 else -1) * Y a j)) 0 :=
    HasDerivAt.fun_sum fun a _ => (((he a i).star).mul_const _).mul (he a j)
  have h2 : (fun s => ∑ a, star (c s a i) * (if ε a then 1 else -1) * c s a j) =ᶠ[𝓝 0] fun _ => Jm ε i j := by
    filter_upwards [hG] with s hs
    rw [← congrFun (congrFun hs i) j]
    simp only [Jm, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h3 := (h1.congr_of_eventuallyEq h2.symm).unique (hasDerivAt_const _ _)
  rw [Matrix.zero_apply, ← h3, h0, Finset.sum_add_distrib]
  simp only [Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.one_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  congr 1
  rw [Finset.sum_eq_single i (fun a _ ha => by simp [ha]) (by simp), if_pos rfl]
  split_ifs <;> simp

theorem hasDerivAt_curve (hπ : IsURepOn (UJset ε) π) {v : H} (hv : v ∈ smD ε π) {c : ℝ → Matrix (Fin m) (Fin m) ℂ}
    {Y : Matrix (Fin m) (Fin m) ℂ} (h0 : c 0 = 1) (hc : HasDerivAt c Y 0) (hG : ∀ᶠ s in 𝓝 (0 : ℝ), inUJ ε (c s)) :
    HasDerivAt (fun s => π (c s) v) (dS π Y v) 0 := by
  have hY := inG_of_curve h0 hc hG
  have h1 : inUJ ε (1 : Matrix (Fin m) (Fin m) ℂ) := by simp [inUJ]
  obtain ⟨U, F, hU, hU1, hF, hE⟩ := (mem_smD_iff ε π v).1 hv 1 h1
  have hFd : HasFDerivAt F (fderiv ℝ F 1) 1 :=
    ((hF.contDiffAt (hU.mem_nhds hU1)).differentiableAt (by simp)).hasFDerivAt
  have key : ∀ d : ℝ → Matrix (Fin m) (Fin m) ℂ, d 0 = 1 → HasDerivAt d Y 0 → (∀ᶠ s in 𝓝 (0 : ℝ), inUJ ε (d s)) →
      HasDerivAt (fun s => π (d s) v) (fderiv ℝ F 1 Y) 0 := by
    intro d d0 hd hdG
    have a1 : HasDerivAt (F ∘ d) (fderiv ℝ F 1 Y) 0 := HasFDerivAt.comp_hasDerivAt_of_eq 0 hFd hd d0.symm
    refine a1.congr_of_eventuallyEq ?_
    have a2 : ∀ᶠ s in 𝓝 (0 : ℝ), d s ∈ U := hd.continuousAt.eventually (hU.mem_nhds (d0 ▸ hU1))
    filter_upwards [a2, hdG] with s s1 s2
    exact hE _ s1 s2
  have hexp : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • Y)) Y 0 := by
    have a : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Y)) (NormedSpace.exp ((0 : ℝ) • Y) * Y) 0 := by
      open scoped Matrix.Norms.Frobenius in exact hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0
    simpa using a
  have b1 := key _ (by simp) hexp (Filter.Eventually.of_forall fun t => exp_indefinite_unitary_holds m ε Y hY t)
  have b2 := ReciprocityTheory.ChartRestriction.DS.hasDerivAt_dS hπ hY ((mem_smD_iff ε π v).1 hv)
  rw [b2.unique b1]
  exact key c h0 hc hG

end Sup

theorem actM_smul (x : smD ε π) (a : ℝ) (Z : Matrix (Fin m) (Fin m) ℂ) :
    actM (smE ε π) ((a : ℂ) • Z) x = (a : ℂ) • actM (smE ε π) Z x := by
  simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem hs_smul (a : ℝ) (Y : Matrix (Fin m) (Fin m) ℂ) : hs ((a : ℂ) • Y) = a ^ 2 * hs Y := by
  simp only [hs, Matrix.smul_apply, norm_smul, mul_pow, Finset.mul_sum, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem eq_zero_of_hs {Y : Matrix (Fin m) (Fin m) ℂ} (h : hs Y = 0) : Y = 0 := by
  ext i j
  have := f1auxiliary_entry_le Y i j
  have h2 : ‖Y i j‖ ^ 2 = 0 := le_antisymm (by linarith) (by positivity)
  simpa using h2

theorem scale_le {M : Type*} [NormedAddCommGroup M] [NormedSpace ℂ M] (T : Matrix (Fin m) (Fin m) ℂ → M)
    (hsm : ∀ (a : ℝ) Z, T ((a : ℂ) • Z) = (a : ℂ) • T Z) {C : ℝ} (hC : ∀ X, hs X ≤ 1 → ‖T X‖ ≤ C)
    (Y : Matrix (Fin m) (Fin m) ℂ) : ‖T Y‖ ≤ Real.sqrt (hs Y) * C := by
  have hs0 : 0 ≤ hs Y := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  rcases hs0.eq_or_lt with h | h
  · have hY : Y = ((0 : ℝ) : ℂ) • Y := by rw [eq_zero_of_hs h.symm, smul_zero]
    rw [← h, hY, hsm]
    simp
  · have hr : 0 < Real.sqrt (hs Y) := Real.sqrt_pos.2 h
    have e : Y = ((Real.sqrt (hs Y) : ℝ) : ℂ) • (((Real.sqrt (hs Y))⁻¹ : ℝ) : ℂ) • Y := by
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne']; simp
    have h1 : hs ((((Real.sqrt (hs Y))⁻¹ : ℝ) : ℂ) • Y) ≤ 1 := by
      rw [hs_smul, inv_pow, Real.sq_sqrt hs0, inv_mul_cancel₀ h.ne']
    conv_lhs => rw [e, hsm, norm_smul, Complex.norm_real, Real.norm_of_nonneg hr.le]
    exact mul_le_mul_of_nonneg_left (hC _ h1) hr.le

theorem norm_dS_le (x : smD ε π) {C : ℝ} (hC : ∀ X, hs X ≤ 1 → ‖actM (smE ε π) X x‖ ≤ C)
    (Y : Matrix (Fin m) (Fin m) ℂ) : ‖actM (smE ε π) Y x‖ ≤ Real.sqrt (hs Y) * C :=
  scale_le (fun X => actM (smE ε π) X x) (actM_smul x) hC Y

section Cayley

open scoped Matrix.Norms.Frobenius

theorem norm_mul_near {x M : Matrix (Fin m) (Fin m) ℂ} {a : ℝ} (hx : ‖x - 1‖ ≤ a) : ‖x * M‖ ≤ (1 + a) * ‖M‖ := by
  calc ‖x * M‖ = ‖M + (x - 1) * M‖ := by congr 1; noncomm_ring
    _ ≤ ‖M‖ + ‖x - 1‖ * ‖M‖ := (norm_add_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ ≤ _ := by nlinarith [norm_nonneg M]

theorem norm_mul_near' {x M : Matrix (Fin m) (Fin m) ℂ} {a : ℝ} (hx : ‖x - 1‖ ≤ a) : ‖M * x‖ ≤ (1 + a) * ‖M‖ := by
  calc ‖M * x‖ = ‖M + M * (x - 1)‖ := by congr 1; noncomm_ring
    _ ≤ ‖M‖ + ‖M‖ * ‖x - 1‖ := (norm_add_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ ≤ _ := by nlinarith [norm_nonneg M]

theorem sqrt_hs_mul_near {x M : Matrix (Fin m) (Fin m) ℂ} {a : ℝ} (hx : Real.sqrt (hs (x - 1)) ≤ a) :
    Real.sqrt (hs (x * M)) ≤ (1 + a) * Real.sqrt (hs M) := by
  simp only [sqrt_frobenius_eq_norm] at hx ⊢
  exact norm_mul_near hx

theorem cay_facts {h : Matrix (Fin m) (Fin m) ℂ} (hh : inUJ ε h) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2)
    (hD : hs (h - 1) ≤ δ ^ 2) :
    ∃ γ γ' : ℝ → Matrix (Fin m) (Fin m) ℂ, γ 0 = 1 ∧ γ 1 = h ∧ (∀ t ∈ Set.Ioo (-1 : ℝ) 2, inUJ ε (γ t)) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt γ (γ' t) t ∧ Real.sqrt (hs (γ t - 1)) ≤ 5 / 4 ∧
        Real.sqrt (hs (γ' t)) ≤ 3 * δ := by
  set D := h - 1 with hDd
  have hDn : ‖D‖ ≤ δ := by
    rw [frobenius_eq_norm_sq] at hD
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hδ0 two_ne_zero).1 hD
  let A : ℝ → Matrix (Fin m) (Fin m) ℂ := fun t => 1 + ((1 + t) / 2) • D
  let B : ℝ → Matrix (Fin m) (Fin m) ℂ := fun t => 1 + ((1 - t) / 2) • D
  have hBu : ∀ t ∈ Set.Ioo (-1 : ℝ) 2, IsUnit (B t) := by
    intro t ht
    have : ‖-(((1 - t) / 2) • D)‖ < 1 := by
      rw [norm_neg, norm_smul, Real.norm_eq_abs]
      have : |(1 - t) / 2| ≤ 1 := abs_le.2 ⟨by linarith [ht.2], by linarith [ht.1]⟩
      nlinarith [norm_nonneg D, abs_nonneg ((1 - t) / 2)]
    have := (Units.oneSub _ this).isUnit
    simpa [B, sub_neg_eq_add] using this
  have hAB : ∀ t, (A t)ᴴ * Jm ε * A t = (B t)ᴴ * Jm ε * B t := by
    intro t
    have e0 : Dᴴ * Jm ε * D = -(Dᴴ * Jm ε) - Jm ε * D := by
      have : hᴴ * Jm ε * h = Jm ε := hh
      rw [show h = D + 1 by rw [hDd, sub_add_cancel], Matrix.conjTranspose_add, Matrix.conjTranspose_one] at this
      have e : (Dᴴ + 1) * Jm ε * (D + 1) = Dᴴ * Jm ε * D + Dᴴ * Jm ε + Jm ε * D + Jm ε := by noncomm_ring
      rw [e] at this
      have e2 : Dᴴ * Jm ε * D = (Dᴴ * Jm ε * D + Dᴴ * Jm ε + Jm ε * D + Jm ε) - Jm ε - Dᴴ * Jm ε - Jm ε * D := by abel
      rw [e2, this]
      abel
    have e1 : ∀ a : ℝ, (1 + a • D)ᴴ * Jm ε * (1 + a • D) = Jm ε + (a - a * a) • (Dᴴ * Jm ε + Jm ε * D) := by
      intro a
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, star_trivial]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, e0]
      module
    simp only [A, B, e1]
    congr 2
    ring
  refine ⟨fun t => A t * Ring.inverse (B t), fun t => (1 / 2 : ℝ) • D * Ring.inverse (B t) +
    A t * (Ring.inverse (B t) * ((1 / 2 : ℝ) • D) * Ring.inverse (B t)), ?_, ?_, ?_, ?_⟩
  · have : A 0 = B 0 := by simp [A, B]
    simp only [this]
    exact Ring.mul_inverse_cancel _ (hBu 0 (by norm_num))
  · simp [A, B, hDd]
  · intro t ht
    have hu := Ring.mul_inverse_cancel _ (hBu t ht)
    show (A t * Ring.inverse (B t))ᴴ * Jm ε * (A t * Ring.inverse (B t)) = Jm ε
    calc _ = (Ring.inverse (B t))ᴴ * ((A t)ᴴ * Jm ε * A t) * Ring.inverse (B t) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (B t * Ring.inverse (B t))ᴴ * Jm ε * (B t * Ring.inverse (B t)) := by
          rw [hAB, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [hu]; simp
  · intro t ht
    have ht' : t ∈ Set.Ioo (-1 : ℝ) 2 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    obtain ⟨u, hu⟩ := hBu t ht'
    have dA : HasDerivAt A ((1 / 2 : ℝ) • D) t := by
      have := ((((hasDerivAt_id t).const_add 1).div_const 2).smul_const D).const_add 1
      exact this
    have dB : HasDerivAt B (-((1 / 2 : ℝ) • D)) t := by
      have := ((((hasDerivAt_id t).const_sub 1).div_const 2).smul_const D).const_add 1
      refine this.congr_deriv ?_
      rw [neg_div, neg_smul]
    have dR : HasDerivAt (fun s => Ring.inverse (B s)) (Ring.inverse (B t) * ((1 / 2 : ℝ) • D) * Ring.inverse (B t)) t := by
      have := HasFDerivAt.comp_hasDerivAt_of_eq t (hasFDerivAt_ringInverse (𝕜 := ℝ) u) dB hu
      refine this.congr_deriv ?_
      rw [← hu, Ring.inverse_unit]
      simp
    set R := Ring.inverse (B t) with hR
    have hRn : ‖R - 1‖ ≤ δ := by
      have e : R - 1 = -(((1 - t) / 2) • (D * R)) := by
        have := Ring.mul_inverse_cancel _ (hBu t ht')
        simp only [B, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul] at this
        rw [← this]; simp [hR, B]
      have h2 : |(1 - t) / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have h3 : ‖D * R‖ ≤ (1 + ‖R - 1‖) * δ :=
        (norm_mul_near' le_rfl).trans (mul_le_mul_of_nonneg_left hDn (by positivity))
      have h1 : ‖R - 1‖ ≤ 1 / 2 * ((1 + ‖R - 1‖) * δ) := by
        conv_lhs => rw [e, norm_neg, norm_smul, Real.norm_eq_abs]
        exact mul_le_mul h2 h3 (norm_nonneg _) (by norm_num)
      nlinarith [norm_nonneg (R - 1)]
    have hAn : ‖A t - 1‖ ≤ δ := by
      have h2 : |(1 + t) / 2| ≤ 1 := abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
      simp only [A, add_sub_cancel_left]
      rw [norm_smul, Real.norm_eq_abs]
      nlinarith [norm_nonneg D, abs_nonneg ((1 + t) / 2)]
    have hHn : ‖(1 / 2 : ℝ) • D‖ ≤ δ / 2 := by rw [norm_smul]; norm_num; linarith
    have hR2 : ‖R - 1‖ ≤ 1 / 2 := hRn.trans hδ
    have hA2 : ‖A t - 1‖ ≤ 1 / 2 := hAn.trans hδ
    refine ⟨dA.mul dR, ?_, ?_⟩
    · rw [sqrt_frobenius_eq_norm]
      calc ‖A t * R - 1‖ = ‖(A t - 1) * R + (R - 1)‖ := by congr 1; noncomm_ring
        _ ≤ (1 + 1 / 2) * ‖A t - 1‖ + ‖R - 1‖ := (norm_add_le _ _).trans (by gcongr; exact norm_mul_near' hR2)
        _ ≤ _ := by linarith
    · rw [sqrt_frobenius_eq_norm]
      have b1 := norm_mul_near' (M := (1 / 2 : ℝ) • D) hR2
      have b2 := norm_mul_near (M := (1 / 2 : ℝ) • D) hR2
      have b3 := norm_mul_near' (M := R * ((1 / 2 : ℝ) • D)) hR2
      have b4 := norm_mul_near (M := R * ((1 / 2 : ℝ) • D) * R) hA2
      have b5 := norm_add_le ((1 / 2 : ℝ) • D * R) (A t * (R * ((1 / 2 : ℝ) • D) * R))
      linarith

end Cayley

theorem disp_le (hπ : IsURepOn (UJset ε) π) (x : smD ε π) {C : ℝ}
    (hC : ∀ X, hs X ≤ 1 → ‖actM (smE ε π) X x‖ ≤ C) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) {g : UJ ε}
    (hg : g ∈ nearSet ε δ) : ‖π (uMat g) x - x‖ ≤ 7 * δ * C := by
  obtain ⟨γ, γ', h0, h1, hG, hd⟩ := cay_facts g.2 hδ0 hδ hg
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (by simp [hs]))
  have key : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ w : H, HasDerivAt (fun s => π (γ s) (x : H)) w t ∧
      ‖w‖ ≤ 7 * δ * C := by
    intro t ht
    have ht' : t ∈ Set.Ioo (-1 : ℝ) 2 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    obtain ⟨u, hu⟩ : γ t ∈ Set.range fun g : UJ ε => uMat g := by
      rw [(isClosedEmbeddingMatrix m ε).2]; exact hG t ht'
    have hu : uMat u = γ t := hu
    have hev : ∀ᶠ s in 𝓝 (0 : ℝ), inUJ ε (γ (t + s)) := by
      have : ∀ᶠ s in 𝓝 (0 : ℝ), t + s ∈ Set.Ioo (-1 : ℝ) 2 :=
        (continuous_const.add continuous_id).continuousAt.eventually (isOpen_Ioo.mem_nhds (by simpa using ht'))
      exact this.mono fun s hs => hG _ hs
    have hmul : ∀ a b : Matrix (Fin m) (Fin m) ℂ, inUJ ε a → inUJ ε b → inUJ ε (a * b) := by
      intro a b ha hb
      unfold inUJ at *
      rw [Matrix.conjTranspose_mul]
      calc bᴴ * aᴴ * Jm ε * (a * b) = bᴴ * (aᴴ * Jm ε * a) * b := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [ha, hb]
    have hinv : uMat u * uMat u⁻¹ = 1 := determinant_character_mul_inv u
    have hinv' : uMat u⁻¹ * uMat u = 1 := by
      have := determinant_character_mul_inv u⁻¹
      rwa [inv_inv] at this
    have d1 : HasDerivAt (fun s => uMat u⁻¹ * γ (t + s)) (uMat u⁻¹ * γ' t) 0 := by
      have a0 : HasDerivAt γ (γ' t) (t + 0) := by rw [add_zero]; exact (hd t ht).1
      open scoped Matrix.Norms.Frobenius in exact (HasDerivAt.comp_const_add t 0 a0).const_mul (uMat u⁻¹)
    have c0 : uMat u⁻¹ * γ (t + 0) = 1 := by rw [add_zero, ← hu, hinv']
    have hev' : ∀ᶠ s in 𝓝 (0 : ℝ), inUJ ε (uMat u⁻¹ * γ (t + s)) := hev.mono fun s hs => hmul _ _ (u⁻¹).2 hs
    have d2 := hasDerivAt_curve hπ x.2 c0 d1 hev'
    have hY := inG_of_curve c0 d1 hev'
    have d3 := ((π (uMat u)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 d2
    have d4 : HasDerivAt (fun s => π (γ (t + s)) (x : H)) (π (uMat u) (dS π (uMat u⁻¹ * γ' t) x)) 0 := by
      refine d3.congr_of_eventuallyEq ?_
      filter_upwards [hev'] with s hs
      have := hπ.1.2 (uMat u) u.2 _ hs
      rw [← Matrix.mul_assoc, hinv, Matrix.one_mul] at this
      simp [this]
    have d5 : HasDerivAt (fun s => π (γ s) (x : H)) (π (uMat u) (dS π (uMat u⁻¹ * γ' t) x)) t := by
      have := HasDerivAt.comp_sub_const t t (f := fun s => π (γ (t + s)) (x : H)) (by rw [sub_self]; exact d4)
      simpa using this
    refine ⟨_, d5, ?_⟩
    rw [hπ.2.1 _ u.2, dS_eq_actM (isDerivedOn_smE hπ) hY x]
    refine (norm_dS_le x hC _).trans (mul_le_mul_of_nonneg_right ?_ hC0)
    have a1 : Real.sqrt (hs (uMat u⁻¹ - 1)) ≤ 5 / 4 := by
      rw [hs_inv_sub_one, hu]
      exact (hd t ht).2.1
    have a2 := sqrt_hs_mul_near (M := γ' t) a1
    have a3 := (hd t ht).2.2
    linarith
  choose! w hw using key
  have := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun s => π (γ s) (x : H)) (f' := w)
    (fun t ht => (hw t ht).1.hasDerivWithinAt) (fun t ht => (hw t (Set.Ico_subset_Icc_self ht)).2)
  simp only [h0, h1] at this
  rwa [hπ.1.1, one_apply_eq_self] at this

end CompanionTheory.Lime.T3
end
end

section
noncomputable section

open Matrix Finset MeasureTheory Formalism.REAL Formalism.MainNotions.S Filter Topology
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.Lime.T3

open ReciprocityTheory.ChartRestriction.DS (smD smE actM dS IsSmoothVecU mem_smD_iff isDerivedOn_smE dS_eq_actM)

theorem interp {f f' : ℝ → ℂ} (hf : ∀ s, HasDerivAt f (f' s) s) {M η τ a : ℝ} (hM : 0 ≤ M)
    (hL : ∀ s t, ‖f' s - f' t‖ ≤ M * |s - t|) (hη : ∀ s ∈ Set.Icc (0 : ℝ) 2, ‖f s‖ ≤ η) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) : ‖f a - f 0‖ ≤ (2 * η / τ + M * τ) * a := by
  obtain ⟨ha0, ha1⟩ := ha
  have key : ∀ s ∈ Set.Icc (0:ℝ) 1, ‖f' s‖ ≤ 2 * η / τ + M * τ := by
    intro s hs
    obtain ⟨hs0, hs1⟩ := hs
    have hg : ∀ t ∈ Set.Icc (0:ℝ) τ, HasDerivWithinAt (fun t : ℝ => f (s + t) - (t : ℂ) * f' s)
        (f' (s + t) - f' s) (Set.Icc 0 τ) t := by
      intro t _
      have h1 : HasDerivAt (fun t : ℝ => f (s + t)) (f' (s + t)) t := by
        have := (hf (s + t)).scomp t ((hasDerivAt_id' t).const_add s)
        simpa [Function.comp_def] using this
      have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * f' s) (f' s) t := by
        have := (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (f' s)
        simpa using this
      exact (h1.sub h2).hasDerivWithinAt
    have hb : ∀ t ∈ Set.Ico (0:ℝ) τ, ‖f' (s + t) - f' s‖ ≤ M * τ := by
      intro t ht
      calc ‖f' (s + t) - f' s‖ ≤ M * |s + t - s| := hL _ _
        _ ≤ M * τ := by
          apply mul_le_mul_of_nonneg_left _ hM
          rw [add_sub_cancel_left, abs_of_nonneg ht.1]
          exact ht.2.le
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hg hb τ ⟨hτ.le, le_rfl⟩
    simp only [Complex.ofReal_zero, zero_mul, sub_zero, add_zero] at hmv
    have e1 := hη (s + τ) ⟨by linarith, by linarith⟩
    have e2 := hη s ⟨hs0, by linarith⟩
    have htri : ‖(τ : ℂ) * f' s‖ ≤ ‖f (s + τ) - (τ:ℂ) * f' s - f s‖ + ‖f (s + τ)‖ + ‖f s‖ := by
      calc ‖(τ : ℂ) * f' s‖ = ‖-(f (s + τ) - (τ:ℂ) * f' s - f s) + f (s + τ) - f s‖ := by
            congr 1
            ring
        _ ≤ ‖-(f (s + τ) - (τ:ℂ) * f' s - f s) + f (s + τ)‖ + ‖f s‖ := norm_sub_le _ _
        _ ≤ ‖-(f (s + τ) - (τ:ℂ) * f' s - f s)‖ + ‖f (s + τ)‖ + ‖f s‖ := by
          gcongr
          exact norm_add_le _ _
        _ = _ := by rw [norm_neg]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hτ.le] at htri
    rw [div_add' _ _ _ hτ.ne', le_div_iff₀ hτ]
    nlinarith
  have hg2 : ∀ x ∈ Set.Icc (0:ℝ) a, HasDerivWithinAt f (f' x) (Set.Icc 0 a) x :=
    fun x _ => (hf x).hasDerivWithinAt
  have hb2 : ∀ x ∈ Set.Ico (0:ℝ) a, ‖f' x‖ ≤ 2 * η / τ + M * τ :=
    fun x hx => key x ⟨hx.1, by linarith [hx.2]⟩
  have hfin := norm_image_sub_le_of_norm_deriv_le_segment' hg2 hb2 a ⟨ha0, le_rfl⟩
  simpa using hfin

variable {m : ℕ} {ε : Fin m → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)}

theorem orbit_deriv (hπ : IsURepOn (UJset ε) π) (x : smD ε π) {c : ℝ → UJ ε} {Z : Matrix (Fin m) (Fin m) ℂ}
    (h0 : c 0 = 1) (hadd : ∀ s t, c (s + t) = c s * c t) (hc : HasDerivAt (fun t => uMat (c t)) Z 0) (s : ℝ) :
    HasDerivAt (fun t : ℝ => π (uMat (c t)) (x : H)) (π (uMat (c s)) (actM (smE ε π) Z x : smD ε π)) s := by
  have mem : ∀ h : UJ ε, uMat h ∈ UJset ε := fun h => h.2
  have hu0 : uMat (c 0) = 1 := by
    rw [h0]
    rfl
  have hd0 : HasDerivAt (fun t : ℝ => π (uMat (c t)) (x : H)) (actM (smE ε π) Z x : smD ε π) 0 := by
    have hev : ∀ᶠ t : ℝ in 𝓝 0, inUJ ε (uMat (c t)) := Filter.Eventually.of_forall fun t => (c t).2
    have h1 := hasDerivAt_curve hπ x.2 hu0 hc hev
    rwa [dS_eq_actM (isDerivedOn_smE hπ) (inG_of_curve hu0 hc hev) x] at h1
  set L := π (uMat (c s)) with hL
  have h4 : HasDerivAt (fun t : ℝ => π (uMat (c t)) (x : H)) (actM (smE ε π) Z x : smD ε π) (s - s) := by
    rw [sub_self]
    exact hd0
  have h2 : HasDerivAt (fun t : ℝ => L (π (uMat (c (t - s))) (x : H)))
      (L (actM (smE ε π) Z x : smD ε π)) s := by
    have h3 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (s - s) h4
    exact h3.comp_sub_const s s
  convert h2 using 1
  funext t
  have e : c t = c s * c (t - s) := by
    rw [← hadd]
    congr 1
    ring
  show π (uMat (c t)) (x : H) = L (π (uMat (c (t - s))) x)
  rw [e, show uMat (c s * c (t - s)) = uMat (c s) * uMat (c (t - s)) from rfl,
    hπ.1.2 _ (mem _) _ (mem _)]
  rfl

theorem coef_interp (hπ : IsURepOn (UJset ε) π) (x : smD ε π) {c : ℝ → UJ ε} {Z : Matrix (Fin m) (Fin m) ℂ}
    (h0 : c 0 = 1) (hadd : ∀ s t, c (s + t) = c s * c t) (hc : HasDerivAt (fun t => uMat (c t)) Z 0) {u : H}
    (hu : ‖u‖ ≤ 1) {M η τ a : ℝ} (hM : ‖actM (smE ε π) Z (actM (smE ε π) Z x)‖ ≤ M)
    (hη : ∀ s ∈ Set.Icc (0 : ℝ) 2, ‖⟪π (uMat (c s)) (x : H), u⟫_ℂ‖ ≤ η) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    ‖⟪π (uMat (c a)) (x : H), u⟫_ℂ - ⟪π (uMat (c 0)) (x : H), u⟫_ℂ‖ ≤ (2 * η / τ + M * τ) * a := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  set y : smD ε π := actM (smE ε π) Z x with hy
  have hF : ∀ s, HasDerivAt (fun t : ℝ => π (uMat (c t)) (x : H)) (π (uMat (c s)) (y : H)) s :=
    orbit_deriv hπ x h0 hadd hc
  have hG : ∀ s, HasDerivAt (fun t : ℝ => π (uMat (c t)) (y : H))
      (π (uMat (c s)) (actM (smE ε π) Z y : H)) s :=
    orbit_deriv hπ y h0 hadd hc
  have hf : ∀ s, HasDerivAt (fun t : ℝ => ⟪π (uMat (c t)) (x : H), u⟫_ℂ)
      ⟪π (uMat (c s)) (y : H), u⟫_ℂ s := by
    intro s
    have h1 := (hF s).inner ℂ (hasDerivAt_const s u)
    simpa using h1
  have hL : ∀ s t, ‖⟪π (uMat (c s)) (y : H), u⟫_ℂ - ⟪π (uMat (c t)) (y : H), u⟫_ℂ‖ ≤ M * |s - t| := by
    intro s t
    rw [← inner_sub_left]
    have hmv : ‖π (uMat (c s)) (y : H) - π (uMat (c t)) (y : H)‖ ≤ M * ‖s - t‖ := by
      apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (fun r _ => (hG r).hasDerivWithinAt) _
        convex_univ (Set.mem_univ _) (Set.mem_univ _)
      intro r _
      rw [hπ.2.1 _ (c r).2 _]
      exact hM
    rw [Real.norm_eq_abs] at hmv
    calc _ ≤ ‖π (uMat (c s)) (y : H) - π (uMat (c t)) (y : H)‖ * ‖u‖ := norm_inner_le_norm _ _
      _ ≤ M * |s - t| * 1 := mul_le_mul hmv hu (norm_nonneg _) (mul_nonneg hM0 (abs_nonneg _))
      _ = M * |s - t| := mul_one _
  exact interp hf hM0 hL hη hτ hτ1 ha

theorem inner_move (hπ : IsURepOn (UJset ε) π) (g k : UJ ε) (a b : H) :
    ⟪π (uMat g) a, π (uMat k) b⟫_ℂ = ⟪a, π (uMat (g⁻¹ * k)) b⟫_ℂ := by
  have mem : ∀ h : UJ ε, uMat h ∈ UJset ε := fun h => h.2
  have hk : uMat k = uMat g * uMat (g⁻¹ * k) := by
    have e : k = g * (g⁻¹ * k) := (mul_inv_cancel_left g k).symm
    conv_lhs => rw [e]
    rfl
  rw [hk, hπ.1.2 _ (mem g) _ (mem _), ContinuousLinearMap.comp_apply]
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (π (uMat g)).toLinearMap, norm_map' := hπ.2.1 _ (mem g) }
  exact L.inner_map_map a _

theorem low_bounds {lam : Fin m → ℝ} {B : ℝ} (hm : 2 ≤ m) (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hDS : IsDS ε lam π)
    (hB : ∀ a, |lam a| ≤ B) (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam (100 * (m : ℝ) ^ 3)) {v : H} (hv : v ∈ lowKSub ε lam π)
    (hv1 : ‖v‖ = 1) : ∃ x : smD ε π, (x : H) = v ∧ (∀ X, hs X ≤ 1 → ‖actM (smE ε π) X x‖ ≤ 8 * Real.sqrt m * (B + 2)) ∧
      ∀ Z, ‖actM (smE ε π) Z (actM (smE ε π) Z x)‖ ≤ hs Z * (8 * Real.sqrt m * (B + 2)) ^ 2 := by
  obtain ⟨hv_s, hW⟩ := kFiniteWordBound_indefUnitary m ε lam B H π hm hl hDS hB hg v hv
  have hπ : IsURepOn (UJset ε) π := hDS.2.2.1
  have hsm : v ∈ smD ε π := by
    rw [mem_smD_iff]
    intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hfe⟩ := hv_s g₀ hg₀
    exact ⟨U, F, hU, hgU, hF, fun g hg hgi => hfe g hg hgi⟩
  set x : smD ε π := ⟨v, hsm⟩ with hx
  have hC : ∀ W : List (Matrix (Fin m) (Fin m) ℂ), W.length ≤ 2 → (∀ X ∈ W, hs X ≤ 1) →
      ‖PI.DSInfCharCap.dsigCW ε π W v‖ ≤ (8 * Real.sqrt m * (B + 2)) ^ W.length := by
    intro W hl1 hX
    have h := hW 2 W hl1 hX
    rw [hv1, mul_one] at h
    simpa using h
  have one : ∀ X, hs X ≤ 1 → ‖actM (smE ε π) X x‖ ≤ 8 * Real.sqrt m * (B + 2) := by
    intro X hX
    have h := hC [X] (by simp) (by simpa using hX)
    have e : PI.DSInfCharCap.dsigCW ε π [X] v = (actM (smE ε π) X x : H) := dsigC_eq_actM hπ X x
    rw [e] at h
    simpa using h
  have two : ∀ X, hs X ≤ 1 →
      ‖actM (smE ε π) X (actM (smE ε π) X x)‖ ≤ (8 * Real.sqrt m * (B + 2)) ^ 2 := by
    intro X hX
    have h := hC [X, X] (by simp) (by simp [hX])
    have e : PI.DSInfCharCap.dsigCW ε π [X, X] v = (actM (smE ε π) X (actM (smE ε π) X x) : H) := by
      show PI.DSInfCharCap.dsigC ε π X (PI.DSInfCharCap.dsigC ε π X (x : H)) = _
      rw [dsigC_eq_actM hπ X x, dsigC_eq_actM hπ X]
    rw [e] at h
    simpa using h
  refine ⟨x, rfl, one, ?_⟩
  intro Z
  have hnn : 0 ≤ hs Z := by
    unfold hs
    positivity
  rcases hnn.eq_or_lt with h0 | hpos
  · have hZ0 : Z = 0 := by
      ext i j
      have hsum : ∑ i, ∑ j, ‖Z i j‖ ^ 2 = 0 := h0.symm
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)] at hsum
      have hi := hsum i (Finset.mem_univ _)
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)] at hi
      have hij := hi j (Finset.mem_univ _)
      simpa using hij
    subst hZ0
    have hz := actM_smul (actM (smE ε π) 0 x) 0 (0 : Matrix (Fin m) (Fin m) ℂ)
    simp only [Complex.ofReal_zero, zero_smul] at hz
    rw [hz, ← h0]
    simp
  · set a := (Real.sqrt (hs Z))⁻¹ with ha
    have hsq : Real.sqrt (hs Z) ^ 2 = hs Z := Real.sq_sqrt hpos.le
    have hspos : 0 < Real.sqrt (hs Z) := Real.sqrt_pos.mpr hpos
    have ha0 : 0 ≤ a := by positivity
    have ha2 : a * a * hs Z = 1 := by
      rw [ha, ← sq, inv_pow, hsq, inv_mul_cancel₀ hpos.ne']
    have hY : hs ((a : ℂ) • Z) ≤ 1 := by
      rw [hs_smul, ← ha2, sq]
    have h := two _ hY
    rw [actM_smul, actM_smul, map_smul, norm_smul, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg ha0] at h
    have hw0 := norm_nonneg (actM (smE ε π) Z (actM (smE ε π) Z x))
    nlinarith [mul_le_mul_of_nonneg_left h hpos.le]

end CompanionTheory.Lime.T3
end
end

section
noncomputable section

open Matrix Finset MeasureTheory Formalism.REAL Formalism.MainNotions.S Filter Topology GlobalTheory.CompanionTheory.PairingAnalysis
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.Lime.T3

variable {n : ℕ} {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool} {e : Fin n ⊕ Unit ≃ Fin (n + 1)}

theorem emb_mul (a b : Matrix (Fin n) (Fin n) ℂ) : emb e (a * b) = emb e a * emb e b := by
  simp [emb, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem emb_one : emb e (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  simp [emb, Matrix.fromBlocks_one]

theorem emb_conjT (a : Matrix (Fin n) (Fin n) ℂ) : (emb e a)ᴴ = emb e aᴴ := by
  simp [emb, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]

theorem emb_J (hF : Fits ε ε' e) : emb e (Jm ε') = Jm ε := by
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  have h1 : ε (e (Sum.inr ())) = true := hF.1
  rcases i with i | i <;> rcases j with j | j <;> simp [emb, Jm, Matrix.diagonal_apply, hF.2, h1]

theorem hs_block (a : Matrix (Fin n) (Fin n) ℂ) (d : Matrix Unit Unit ℂ) :
    hs (Matrix.reindex e e (Matrix.fromBlocks a 0 0 d)) = hs a + ‖d () ()‖ ^ 2 := by
  unfold hs
  rw [← e.sum_comp]
  simp_rw [← e.sum_comp (fun j => ‖Matrix.reindex e e (Matrix.fromBlocks a 0 0 d) _ j‖ ^ 2)]
  simp [Fintype.sum_sum_type]

theorem col_emb (g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (a : Matrix (Fin n) (Fin n) ℂ) :
    colSq (g * emb e a) (zi e) = colSq g (zi e) := by
  unfold colSq
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply, ← e.sum_comp]
  simp [emb, zi, Fintype.sum_sum_type]

def embG (hF : Fits ε ε' e) : UJ ε' →* UJ ε where
  toFun h := ⟨⟨emb e (uMat h), emb e (uMat h⁻¹), by rw [← emb_mul, ← emb_one (e := e)]; congr 1; exact determinant_character_mul_inv h,
      by rw [← emb_mul, ← emb_one (e := e)]; congr 1; exact (show (h : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹.1 * _ = 1 from Units.inv_mul _)⟩, by
    have hh : (uMat h)ᴴ * Jm ε' * uMat h = Jm ε' := h.2
    show (emb e (uMat h))ᴴ * Jm ε * emb e (uMat h) = Jm ε
    rw [← emb_J hF, emb_conjT, ← emb_mul, ← emb_mul, hh]⟩
  map_one' := Subtype.ext (Units.ext emb_one)
  map_mul' a b := Subtype.ext (Units.ext (emb_mul _ _))

theorem uMat_embG (hF : Fits ε ε' e) (h : UJ ε') : uMat (embG hF h) = emb e (uMat h) := rfl

theorem nG_le_embG (hF : Fits ε ε' e) (h : UJ ε') : nG h ≤ nG (embG hF h) := by
  unfold nG
  rw [uMat_embG, emb, hs_block]
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (by positivity))

theorem colSq_le_hs {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) : colSq g j ≤ hs g :=
  Finset.sum_le_sum fun i _ =>
    Finset.single_le_sum (f := fun k => ‖g i k‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)

theorem colSq_pos {m : ℕ} {η : Fin m → Bool} (g : UJ η) (j : Fin m) : 0 < colSq (uMat g) j := by
  by_contra h
  have h0 : colSq (uMat g) j = 0 := le_antisymm (not_lt.1 h) (Finset.sum_nonneg fun _ _ => by positivity)
  have h1 : ∀ i, uMat g i j = 0 := fun i => by
    have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => by positivity).1 h0 i (Finset.mem_univ i)
    simpa using this
  have h2 : uMat g⁻¹ * uMat g = 1 := Units.inv_mul (g : (Matrix (Fin m) (Fin m) ℂ)ˣ)
  have h3 := congrFun (congrFun h2 j) j
  simp [Matrix.mul_apply, h1] at h3

theorem rpow_hs {m : ℕ} (hm : 1 ≤ m) {η : Fin m → Bool} (g : UJ η) (k : ℕ) {a : ℝ} (ha : (k : ℝ) ≤ 2 * a) :
    hs (uMat g) ^ (-a) ≤ (nG g)⁻¹ ^ k := by
  have h1 := one_le_nG hm g
  rw [← nG_sq, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith), inv_pow, ← Real.rpow_natCast,
    ← Real.rpow_neg (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le h1 (by push_cast; linarith)

theorem lint_le {m : ℕ} (hm : 1 ≤ m) {η : Fin m → Bool} (μ : Measure (UJ η)) [μ.IsHaarMeasure] {f : UJ η → ℂ} {C δ : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hd : ∀ g, ‖f g‖ ≤ C * (nG g)⁻¹ ^ (2 * m ^ 2 + 1)) :
    ∫⁻ g, ‖f g‖ₑ ∂μ ≤ ENNReal.ofReal (C * (2 * (16 * (m : ℝ) ^ 2 / δ) ^ (2 * m ^ 2))) * μ (nearSet η δ) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsq : Real.sqrt m ≤ m := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  calc ∫⁻ g, ‖f g‖ₑ ∂μ ≤ ∫⁻ g, ENNReal.ofReal C * ENNReal.ofReal ((Real.sqrt (hsG g))⁻¹ ^ (2 * m ^ 2 + 1)) ∂μ := by
        refine lintegral_mono fun g => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_mul hC]
        exact ENNReal.ofReal_le_ofReal (hd g)
    _ = ENNReal.ofReal C * ∫⁻ g, ENNReal.ofReal ((Real.sqrt (hsG g))⁻¹ ^ (2 * m ^ 2 + 1)) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (2 * (16 * (m : ℝ) ^ 2 / δ) ^ (2 * m ^ 2)) * μ (nearSet η δ)) := by
        refine mul_le_mul_right ((int_ratio hm η μ hδ (by linarith) le_rfl).trans (mul_le_mul_left ?_ _)) _
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) zero_le_two)
        exact div_le_div_of_nonneg_right (by nlinarith) hδ.le
    _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul hC]

theorem h_integrability : HInt := by
  intro n ε ε' e ν hν hF hn φ C δ hC hδ hδ1 hd g
  set b : ℕ := 2 * n ^ 2 + 1 with hb
  set a : ℕ := 2 * (n + 1) + 5 with ha
  have hn1 : 1 ≤ n + 1 := by omega
  have hbd : BddBelow (Set.range fun h => nG (g * embG hF h)) := ⟨1, by rintro _ ⟨h, rfl⟩; exact one_le_nG hn1 _⟩
  have hi1 : 1 ≤ ⨅ h, nG (g * embG hF h) := le_ciInf fun h => one_le_nG hn1 _
  obtain ⟨h1, hh1⟩ := exists_lt_of_ciInf_lt (show (⨅ h, nG (g * embG hF h)) < 2 * ⨅ h, nG (g * embG hF h) by linarith)
  set g1 := g * embG hF h1 with hg1
  set y := colSq (uMat g) (zi e) with hy
  have hy0 : 0 < y := colSq_pos g _
  have hG1 := one_le_nG hn1 g1
  have hyG : Real.sqrt y ≤ nG g1 := by
    refine Real.sqrt_le_sqrt ?_
    rw [hy, ← col_emb (e := e) (uMat g) (uMat h1)]
    exact colSq_le_hs _ _
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
  have hpt : ∀ h : UJ ε', ‖φ (um g * emb e (um (h1 * h)))‖ ≤
      (C * 2 ^ (a + b) * (Real.sqrt y)⁻¹ ^ a) * (nG h)⁻¹ ^ b := by
    intro h
    have e1 : um g * emb e (um (h1 * h)) = uMat (g1 * embG hF h) := by
      rw [hg1, mul_assoc, ← map_mul]; rfl
    set t := nG (g1 * embG hF h) with ht
    have ht1 : 1 ≤ t := one_le_nG hn1 _
    have hh := one_le_nG (by omega : 1 ≤ n) h
    have t1 : nG g1 ≤ 2 * t := by
      have := ciInf_le hbd (h1 * h)
      rw [map_mul, ← mul_assoc] at this
      linarith
    have t2 : nG h ≤ nG g1 * t := by
      refine (nG_le_embG hF h).trans ?_
      have := nG_mul g1⁻¹ (g1 * embG hF h)
      rwa [inv_mul_cancel_left, nG_inv] at this
    have s1 : t⁻¹ ≤ 2 * (nG g1)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by linarith), inv_mul_le_iff₀ (by linarith)]; linarith
    have s2 : t⁻¹ ≤ nG g1 * (nG h)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by linarith), inv_mul_le_iff₀ (by linarith)]; linarith
    have s3 := rpow_hs hn1 (g1 * embG hF h) (a + b + b) (a := 3 * ((n : ℝ) + 1) ^ 2) (by
      simp only [ha, hb]; push_cast; have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith)
    have s4 : t⁻¹ ^ (a + b + b) ≤ (2 * (nG g1)⁻¹) ^ (a + b) * (nG g1 * (nG h)⁻¹) ^ b := by
      rw [pow_add _ (a + b)]
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) s1 _) (pow_le_pow_left₀ (by positivity) s2 _) (by positivity)
        (by positivity)
    have s5 : (2 * (nG g1)⁻¹) ^ (a + b) * (nG g1 * (nG h)⁻¹) ^ b = 2 ^ (a + b) * (nG g1)⁻¹ ^ a * (nG h)⁻¹ ^ b := by
      have : (nG g1)⁻¹ ^ b * nG g1 ^ b = 1 := by rw [← mul_pow, inv_mul_cancel₀ (by linarith), one_pow]
      rw [mul_pow, mul_pow, pow_add (nG g1)⁻¹]
      linear_combination (2 ^ (a + b) * (nG g1)⁻¹ ^ a * (nG h)⁻¹ ^ b) * this
    have s6 : (nG g1)⁻¹ ^ a ≤ (Real.sqrt y)⁻¹ ^ a := pow_le_pow_left₀ (by positivity) (inv_anti₀ hsy hyG) a
    rw [e1]
    refine (hd _).trans ?_
    calc C * hs (uMat (g1 * embG hF h)) ^ (-(3 * ((n : ℝ) + 1) ^ 2))
        ≤ C * (2 ^ (a + b) * (Real.sqrt y)⁻¹ ^ a * (nG h)⁻¹ ^ b) := by
          refine mul_le_mul_of_nonneg_left (s3.trans (s4.trans (s5.le.trans ?_))) hC
          gcongr
      _ = _ := by ring
  rw [← lintegral_mul_left_eq_self (fun h : UJ ε' => ‖φ (um g * emb e (um h))‖ₑ) h1]
  refine (lint_le (by omega) ν (by positivity) hδ hδ1 hpt).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
  have e2 : (Real.sqrt y)⁻¹ ^ a = y ^ (-((2 * ((n : ℝ) + 1) + 5) / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hy0.le, ← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
    congr 1
    simp only [ha]; push_cast; ring
  set T : ℝ := 100 * ((n : ℝ) + 1) ^ 2 / δ with hT
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have T1 : 16 * (n : ℝ) ^ 2 / δ ≤ T := div_le_div_of_nonneg_right (by nlinarith) hδ.le
  have T2 : 2 ≤ T := by rw [hT, le_div_iff₀ hδ]; nlinarith
  have T3 : (2 : ℝ) ^ (a + b) * (2 * (16 * (n : ℝ) ^ 2 / δ) ^ (2 * n ^ 2)) ≤ T ^ (10 * (n + 1) ^ 2) := by
    calc _ ≤ T ^ (a + b) * (T * T ^ (2 * n ^ 2)) := by gcongr
      _ = T ^ (a + b + 1 + 2 * n ^ 2) := by ring
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by simp only [ha, hb]; nlinarith)
  rw [e2]
  calc _ = C * (2 ^ (a + b) * (2 * (16 * (n : ℝ) ^ 2 / δ) ^ (2 * n ^ 2))) * y ^ (-((2 * ((n : ℝ) + 1) + 5) / 2)) := by ring
    _ ≤ _ := by gcongr

end CompanionTheory.Lime.T3
end
end

section
noncomputable section

open Matrix Finset MeasureTheory Formalism.REAL Formalism.MainNotions.S Filter Topology GlobalTheory.CompanionTheory.PairingAnalysis
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.Lime.T3

open ReciprocityTheory.ChartRestriction.DS (smD smE actM)

theorem volume_ratio_bound : VolR := fun _ ε μ _ hm _ _ hδ hδ2 hR => vol_ratio hm ε μ hδ hδ2 hR

theorem decay_estimate : Decay := by
  intro m N ε lam A _ _ _ π hm hmN hl hDS hg v hv hv1 g₀ Y hY g
  have hN : 1 ≤ 12 * N ^ 2 := by have : 1 ≤ N := hm.trans hmN; nlinarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 := dec_conj hm hDS.2.2.1 (by positivity) (dec_low hm hmN hl hDS hg hv hv1 hN le_rfl) g₀ g
  have h2 := one_le_nG hm g
  have h3 : 0 ≤ hs (uMat g₀) := by rw [← nG_sq]; positivity
  have e1 : (Real.exp 1 * Real.sqrt m) ^ (12 * N ^ 2) =
      Real.exp (6 * (N : ℝ) ^ 2 * Real.log m + 12 * (N : ℝ) ^ 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hm0, ← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    push_cast; ring
  have e2 : (nG g)⁻¹ ^ (12 * N ^ 2) = hs (um g) ^ (-(6 * (N : ℝ) ^ 2)) := by
    change _ = hs (uMat g) ^ _
    rw [← nG_sq, ← Real.rpow_natCast (nG g) 2, ← Real.rpow_mul (by linarith), inv_pow, ← Real.rpow_natCast,
      ← Real.rpow_neg (by linarith)]
    congr 1
    push_cast; ring
  rw [e1, e2] at h1
  refine h1.trans ?_
  have h4 : 0 ≤ hs (um g) ^ (-(6 * (N : ℝ) ^ 2)) := by rw [← e2]; positivity
  gcongr

theorem integral_ratio_bound : IntR := by
  intro m ε μ hμ hm φ C a hφ ha hd
  have hC : 0 ≤ C := by
    have h1 := (norm_nonneg _).trans (hd 1)
    have h2 : 0 < hs (um (1 : UJ ε)) ^ (-a) := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (one_le_hsG hm 1)) _
    exact nonneg_of_mul_nonneg_left h1 h2
  have hd' : ∀ g, ‖φ g‖ ≤ C * (nG g)⁻¹ ^ (2 * m ^ 2 + 1) := fun g =>
    (hd g).trans (mul_le_mul_of_nonneg_left (rpow_hs hm g _ (by push_cast; linarith)) hC)
  have hI := integrable_of_dec hm μ hφ hC le_rfl hd'
  refine ⟨hI, ?_⟩
  have h1 := lint_le hm μ hC one_pos le_rfl hd'
  rw [integral_norm_eq_lintegral_enorm hI.1]
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (nearSet_lt_top ε μ).ne) h1).trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), div_one]
  rfl

theorem derivative_upper_bound : DUp := by
  intro m ε lam B A _ _ _ π μ d hμ hm hl hDS hB hg hd
  have hπ : IsURepOn (UJset ε) π := hDS.2.2.1
  obtain ⟨S, hS⟩ := hDS.2.2.2.2.2.1
  obtain ⟨v0, hv0, hne, -⟩ := hS.2.2.2.1
  have hn0 : 0 < ‖v0‖ := norm_pos_iff.2 hne
  set v : A := ((‖v0‖⁻¹ : ℝ) : ℂ) • v0 with hvd
  have hv : v ∈ lowKSub ε lam π := Submodule.smul_mem _ _ (le_sSup (s := {S | IsKTypeOf ε π (Formalism.QuantumDeterminants.lowK ε lam) S}) hS hv0)
  have hv1 : ‖v‖ = 1 := by
    rw [hvd, norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ hn0.ne']
  obtain ⟨x, hx, hb, -⟩ := low_bounds hm hl hDS hB hg hv hv1
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hB0 : 0 ≤ B := by have := le_four_mul hm hl hB; linarith
  set K : ℝ := 100 * m * (B + 1) with hK
  have hK1 : 200 ≤ K := by nlinarith
  have hsq : Real.sqrt m ≤ m := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hnear : ∀ g ∈ nearSet ε (K ^ 2)⁻¹, 1 / 4 ≤ ‖⟪v, π (uMat g) v⟫_ℂ‖ ^ 2 := by
    intro g hgn
    have hδ : (K ^ 2)⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
    have h1 := disp_le hπ x hb (by positivity) hδ hgn
    rw [hx] at h1
    have h2 : 7 * (K ^ 2)⁻¹ * (8 * Real.sqrt m * (B + 2)) ≤ 1 / 2 := by
      have a1 : 8 * Real.sqrt m * (B + 2) ≤ K := by
        have : Real.sqrt m * (B + 2) ≤ m * (2 * (B + 1)) := mul_le_mul hsq (by linarith) (by linarith) (by linarith)
        nlinarith
      rw [mul_assoc, ← div_eq_inv_mul, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith
    have h3 : ‖⟪v, π (uMat g) v - v⟫_ℂ‖ ≤ 1 / 2 := by
      refine (norm_inner_le_norm _ _).trans ?_
      rw [hv1, one_mul]
      exact h1.trans h2
    rw [inner_sub_right, inner_self_eq_norm_sq_to_K, hv1] at h3
    have h4 := norm_sub_norm_le (1 : ℂ) (1 - ⟪v, π (uMat g) v⟫_ℂ)
    rw [sub_sub_cancel, norm_one, norm_sub_rev] at h4
    have h5 : ‖⟪v, π (uMat g) v⟫_ℂ - 1‖ ≤ 1 / 2 := by simpa using h3
    nlinarith [norm_nonneg ⟪v, π (uMat g) v⟫_ℂ]
  obtain ⟨hI, hE⟩ := hd.2 v v v v
  have e1 : ∀ g : UJ ε, coefOn π v v g * star (coefOn π v v g) = ((‖⟪v, π (uMat g) v⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rfl
  simp only [e1] at hI hE
  have hI' : Integrable (fun g : UJ ε => ‖⟪v, π (uMat g) v⟫_ℂ‖ ^ 2) μ :=
    hI.re.congr (Filter.Eventually.of_forall fun g => Complex.ofReal_re _)
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K, hv1] at hE
  have hE' : ∫ g : UJ ε, ‖⟪v, π (uMat g) v⟫_ℂ‖ ^ 2 ∂μ = d⁻¹ := by
    have : ((∫ g : UJ ε, ‖⟪v, π (uMat g) v⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) = ((d⁻¹ : ℝ) : ℂ) := by rw [hE]; simp
    exact_mod_cast this
  have hmeas : MeasurableSet (nearSet ε (K ^ 2)⁻¹) :=
    (isClosed_le (continuous_hs_real_place_taylor.comp ((continuous_coeMatrix ε).sub continuous_const)) continuous_const).measurableSet
  have h6 : ENNReal.ofReal (1 / 4) * μ (nearSet ε (K ^ 2)⁻¹) ≤ ENNReal.ofReal d⁻¹ := by
    rw [← hE', ofReal_integral_eq_lintegral_ofReal hI' (Filter.Eventually.of_forall fun g => by positivity),
      ← lintegral_indicator_const hmeas]
    refine lintegral_mono fun g => ?_
    by_cases hg' : g ∈ nearSet ε (K ^ 2)⁻¹
    · rw [Set.indicator_of_mem hg']; exact ENNReal.ofReal_le_ofReal (hnear g hg')
    · rw [Set.indicator_of_notMem hg']; exact bot_le
  have hd0 := hd.1
  calc ENNReal.ofReal d * μ (nearSet ε (K ^ 2)⁻¹)
      = ENNReal.ofReal (4 * d) * (ENNReal.ofReal (1 / 4) * μ (nearSet ε (K ^ 2)⁻¹)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]; congr 2; ring
    _ ≤ ENNReal.ofReal (4 * d) * ENNReal.ofReal d⁻¹ := mul_le_mul_right h6 _
    _ = 4 := by
        rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, mul_inv_cancel₀ hd0.ne', mul_one]; simp

end CompanionTheory.Lime.T3
end
end

section
noncomputable section

open Matrix Finset MeasureTheory Formalism.REAL Formalism.MainNotions.S Filter Topology GlobalTheory.CompanionTheory.PairingAnalysis
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.Lime.T3

open ReciprocityTheory.ChartRestriction.DS (smD smE actM)

theorem exists_onePar {m : ℕ} {η : Fin m → Bool} {X : Matrix (Fin m) (Fin m) ℂ} (hX : inG η X) :
    ∃ c : ℝ → UJ η, (∀ s, uMat (c s) = NormedSpace.exp ((s : ℂ) • X)) ∧ c 0 = 1 ∧ ∀ s t, c (s + t) = c s * c t := by
  have : ∀ s : ℝ, ∃ u : UJ η, uMat u = NormedSpace.exp ((s : ℂ) • X) := fun s => by
    have h : NormedSpace.exp ((s : ℂ) • X) ∈ Set.range fun g : UJ η => uMat g := by
      rw [(isClosedEmbeddingMatrix m η).2]; exact exp_indefinite_unitary_holds m η X hX s
    exact h
  choose c hc using this
  refine ⟨c, hc, Subtype.ext (Units.ext ?_), fun s t => Subtype.ext (Units.ext ?_)⟩
  · change uMat (c 0) = 1
    rw [hc]; simp
  · change uMat (c (s + t)) = uMat (c s) * uMat (c t)
    rw [hc, hc, hc, one_parameter_subgroup_holds]

variable {n : ℕ} {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool} {e : Fin n ⊕ Unit ≃ Fin (n + 1)}

def embL (e : Fin n ⊕ Unit ≃ Fin (n + 1)) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ where
  toFun h := Matrix.reindex e e (Matrix.fromBlocks h 0 0 0)
  map_add' a b := by
    ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    rcases i with i | i <;> rcases j with j | j <;> simp
  map_smul' c a := by
    ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    rcases i with i | i <;> rcases j with j | j <;> simp

theorem emb_eq (h : Matrix (Fin n) (Fin n) ℂ) : emb e h = embL e h + emb e 0 := by
  ext i j
  obtain ⟨i, rfl⟩ := e.surjective i
  obtain ⟨j, rfl⟩ := e.surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp [emb, embL]

open scoped Matrix.Norms.Frobenius in
theorem deriv_conj (X : Matrix (Fin n) (Fin n) ℂ) (a b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    HasDerivAt (fun t : ℝ => a * emb e (NormedSpace.exp ((t : ℂ) • X)) * b) (a * embL e X * b) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) (NormedSpace.exp ((0 : ℝ) • X) * X) 0 :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  rw [zero_smul, NormedSpace.exp_zero, Matrix.one_mul] at h1
  have h2 := (LinearMap.toContinuousLinearMap (embL e)).hasFDerivAt.comp_hasDerivAt 0 h1
  have h3 := ((h2.add_const (emb e 0)).const_mul a).mul_const b
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  simp only [emb_eq (e := e) (NormedSpace.exp ((t : ℂ) • X))]
  rfl

set_option maxHeartbeats 1600000 in
theorem lipschitz_estimate : Lip := by
  intro n ε lam ε' B e A _ _ _ π ν hν hF hn hl hDS hB hg v hv hv1 g₀ Y δ hY hδ hδ1 X hX
  have hπ : IsURepOn (UJset ε) π := hDS.2.2.1
  have hn1 : 1 ≤ n := by omega
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set b : ℕ := 2 * n ^ 2 + 1 with hb
  have hg' : Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * ((n + 1 : ℕ) : ℝ) ^ 3) := by push_cast; exact hg
  have hY1 : 1 ≤ Y := (one_le_hsG (by omega) g₀).trans hY
  have hY0 : 0 ≤ hs (uMat g₀) := by rw [← nG_sq]; positivity
  have hNB : (n : ℝ) + 1 ≤ 4 * B := by have := le_four_mul (by omega) hl hB; push_cast at this; exact this
  have hB0 : 0 ≤ B := by linarith
  set T : ℝ := 8 * ((n : ℝ) + 1) * B * Y / δ with hT
  have T0 : 8 * ((n : ℝ) + 1) * B * Y ≤ T := by
    rw [hT, le_div_iff₀ hδ]
    exact mul_le_of_le_one_right (by have : 0 ≤ B := by linarith
                                     positivity) hδ1
  have T1 : 6 * (((n : ℝ) + 1) * Y) ≤ T := by
    have : 6 * (((n : ℝ) + 1) * Y) ≤ (8 * B) * (((n : ℝ) + 1) * Y) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have T2 : 18 ≤ T := by nlinarith
  have T3 : 16 * (n : ℝ) ^ 2 / δ ≤ T ^ 2 := by
    have : 16 * (n : ℝ) ^ 2 / δ ≤ 8 * T := by
      rw [hT, ← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ hδ.le
      have : ((n : ℝ) + 1) * (n + 1) * 1 ≤ (n + 1) * (4 * B) * Y := by gcongr
      nlinarith
    nlinarith
  clear_value T
  have hsN : Real.sqrt ((n + 1 : ℕ) : ℝ) * Real.sqrt n ≤ n + 1 := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_le_iff]
    push_cast
    exact ⟨by linarith, by nlinarith⟩
  have hs1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.2 (by linarith)
  set P : ℝ := Real.exp 1 * Real.sqrt ((n + 1 : ℕ) : ℝ) * Y with hP
  set Q : ℝ := Real.sqrt n * Real.exp 2 with hQ
  have hP0 : 0 ≤ P := by positivity
  have hQ1 : 1 ≤ Q := one_le_mul_of_one_le_of_one_le hs1 (Real.one_le_exp (by norm_num))
  have T4 : P * Q ≤ T ^ 2 := by
    have e3 : Real.exp 1 * Real.exp 2 ≤ 27 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      have := Real.exp_one_lt_three
      have := Real.exp_pos 1
      nlinarith
    calc P * Q = (Real.exp 1 * Real.exp 2) * (Real.sqrt ((n + 1 : ℕ) : ℝ) * Real.sqrt n) * Y := by rw [hP, hQ]; ring
      _ ≤ 27 * (n + 1) * Y := by gcongr
      _ ≤ T ^ 2 := by nlinarith
  set D : ℝ := (P * Q) ^ (2 * b) with hD
  have hD0 : 0 ≤ D := by positivity
  have hDT : D ≤ T ^ (4 * b) := by
    rw [show 4 * b = 2 * (2 * b) by ring, pow_mul T]
    exact pow_le_pow_left₀ (by positivity) T4 _

  let f : UJ ε' → ℂ := fun k => ⟪π (uMat g₀) v, π (uMat (embG hF k)) (π (uMat g₀) v)⟫_ℂ
  have hf : ∀ k, ‖f k‖ ≤ P ^ (2 * b) * (nG k)⁻¹ ^ (2 * b) := by
    intro k
    have h1 := dec_conj (by omega) hπ (by positivity)
      (dec_low (by omega) le_rfl hl hDS hg' hv hv1 (A := 2 * b) (by omega) (by simp only [hb]; nlinarith)) g₀ (embG hF k)
    refine h1.trans (mul_le_mul ?_ (pow_le_pow_left₀ (by unfold nG; positivity)
      (inv_anti₀ (by linarith [one_le_nG hn1 k]) (nG_le_embG hF k)) _) (by unfold nG; positivity) (by positivity))
    rw [hP, mul_pow _ Y]
    gcongr
  have hτ : ∀ k : UJ ε', 0 < (nG k)⁻¹ ^ b ∧ (nG k)⁻¹ ^ b ≤ 1 := fun k =>
    ⟨by have := one_le_nG hn1 k; positivity,
      pow_le_one₀ (by unfold nG; positivity) (inv_le_one_of_one_le₀ (one_le_nG hn1 k))⟩
  set r := Real.sqrt (hs X) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hfin : ∀ C : ℝ, 0 ≤ C → C ≤ 3 * T ^ (4 * b) * r →
      ENNReal.ofReal (C * (2 * (16 * (n : ℝ) ^ 2 / δ) ^ (2 * n ^ 2))) ≤ ENNReal.ofReal (T ^ (20 * (n + 1) ^ 2) * r) := by
    intro C hC hC'
    refine ENNReal.ofReal_le_ofReal ?_
    calc _ ≤ (3 * T ^ (4 * b) * r) * (2 * (T ^ 2) ^ (2 * n ^ 2)) := by gcongr
      _ = 6 * T ^ (4 * b + 4 * n ^ 2) * r := by
          rw [← pow_mul, pow_add T, show 2 * (2 * n ^ 2) = 4 * n ^ 2 by ring]; ring
      _ ≤ T * T ^ (4 * b + 4 * n ^ 2) * r := by gcongr; linarith
      _ = T ^ (4 * b + 4 * n ^ 2 + 1) * r := by rw [← pow_succ']
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) (by simp only [hb]; nlinarith)) hr0
  have hs0 : 0 ≤ hs X := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  set X' : Matrix (Fin n) (Fin n) ℂ := ((r⁻¹ : ℝ) : ℂ) • X with hX'd
  have hX' : inG ε' X' := by
    have : Xᴴ * Jm ε' + Jm ε' * X = 0 := hX
    unfold inG
    rw [hX'd, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul,
      ← smul_add, this, smul_zero]
  have hX1 : hs X' ≤ 1 := by
    rw [hX'd, hs_smul, inv_pow, hr, Real.sq_sqrt hs0]
    exact inv_mul_le_one_of_le₀ le_rfl hs0
  have hXr : ((-r : ℝ) : ℂ) • X' = -X := by
    rcases hr0.eq_or_lt with h | h
    · have : X = 0 := eq_zero_of_hs (by rw [← Real.sq_sqrt hs0, ← hr, ← h]; ring)
      simp [hX'd, this]
    · rw [hX'd, smul_smul, ← Complex.ofReal_mul, neg_mul, mul_inv_cancel₀ h.ne']; simp
  obtain ⟨c, hc, hc0, hadd⟩ := exists_onePar hX'
  have hinv : ∀ s, (c s)⁻¹ = c (-s) := fun s => by
    rw [inv_eq_iff_mul_eq_one, ← hadd, add_neg_cancel, hc0]
  have hgoal : ∀ h : UJ ε', emb e (NormedSpace.exp (-X) * um h) = uMat (embG hF ((c r)⁻¹ * h)) := by
    intro h
    rw [hinv, ← hXr, ← hc]
    rfl
  simp only [hgoal]
  change ∫⁻ h, ‖f ((c r)⁻¹ * h) - f h‖ₑ ∂ν ≤ _ * ν (nearSet ε' δ)
  have hPD : P ^ (2 * b) ≤ D := pow_le_pow_left₀ hP0 (le_mul_of_one_le_right hP0 hQ1) _
  rcases le_total 1 r with hr1 | hr1
  · let F : UJ ε' → ℂ := fun k => ((D * (nG k)⁻¹ ^ b : ℝ) : ℂ)
    have hFn : ∀ k, ‖F k‖ = D * (nG k)⁻¹ ^ b := fun k => by
      rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hD0 (hτ k).1.le)]
    have hfF : ∀ k, ‖f k‖ₑ ≤ ‖F k‖ₑ := fun k => by
      rw [enorm_le_iff_norm_le, hFn]
      refine (hf k).trans (mul_le_mul hPD ?_ (by unfold nG; positivity) hD0)
      rw [two_mul, pow_add]
      exact mul_le_of_le_one_right (hτ k).1.le (hτ k).2
    have hFm : Measurable fun k => ‖F k‖ₑ := by
      have : Continuous (nG (ε := ε')) := (continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε')).sqrt
      exact (Complex.measurable_ofReal.comp (measurable_const.mul (this.measurable.inv.pow_const b))).enorm
    have h1 := lint_le hn1 ν hD0 hδ hδ1 (f := F) fun k => (hFn k).le
    calc _ ≤ ∫⁻ h, ‖F ((c r)⁻¹ * h)‖ₑ + ‖F h‖ₑ ∂ν :=
          lintegral_mono fun h => enorm_sub_le.trans (add_le_add (hfF _) (hfF _))
      _ = 2 * ∫⁻ h, ‖F h‖ₑ ∂ν := by
          rw [lintegral_add_right _ hFm, lintegral_mul_left_eq_self (fun h => ‖F h‖ₑ), two_mul]
      _ ≤ 2 * (ENNReal.ofReal (D * (2 * (16 * (n : ℝ) ^ 2 / δ) ^ (2 * n ^ 2))) * ν (nearSet ε' δ)) :=
          mul_le_mul_right h1 _
      _ = ENNReal.ofReal ((2 * D) * (2 * (16 * (n : ℝ) ^ 2 / δ) ^ (2 * n ^ 2))) * ν (nearSet ε' δ) := by
          rw [← mul_assoc, mul_assoc 2 D, ENNReal.ofReal_mul zero_le_two]; simp
      _ ≤ _ := by
          refine mul_le_mul_left (hfin _ (by positivity) ?_) _
          have : 0 ≤ T ^ (4 * b) := by positivity
          nlinarith
  · obtain ⟨x, hx, -, hb2⟩ := low_bounds (by omega) hl hDS hB
      (fun a a' h => le_trans (by push_cast; have : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := by positivity
                                  linarith) (hg a a' h)) hv hv1
    let d : ℝ → UJ ε := fun s => g₀⁻¹ * embG hF (c s) * g₀
    have d0 : d 0 = 1 := by simp [d, hc0]
    have dadd : ∀ s t, d (s + t) = d s * d t := fun s t => by simp only [d, hadd, map_mul]; group
    have dd : HasDerivAt (fun t => uMat (d t)) (uMat g₀⁻¹ * embL e X' * uMat g₀) 0 := by
      have e0 : (fun t => uMat (d t)) = fun t : ℝ => uMat g₀⁻¹ * emb e (NormedSpace.exp ((t : ℂ) • X')) * uMat g₀ := by
        funext t
        rw [← hc]
        rfl
      rw [e0]
      exact deriv_conj X' _ _
    set Z := uMat g₀⁻¹ * embL e X' * uMat g₀ with hZ
    have hZ1 : Real.sqrt (hs Z) ≤ Y := by
      have a1 : Real.sqrt (hs (embL e X')) ≤ 1 := by
        refine Real.sqrt_le_one.2 ?_
        change hs (Matrix.reindex e e (Matrix.fromBlocks X' 0 0 0)) ≤ 1
        rw [hs_block]; simpa using hX1
      have a2 : Real.sqrt (hs (uMat g₀⁻¹)) = nG g₀ := nG_inv g₀
      have a3 : 0 ≤ nG g₀ := Real.sqrt_nonneg _
      calc _ ≤ Real.sqrt (hs (uMat g₀⁻¹ * embL e X')) * nG g₀ := sqrt_frobenius_mul_le _ _
        _ ≤ (nG g₀ * 1) * nG g₀ := by
            refine mul_le_mul_of_nonneg_right ((sqrt_frobenius_mul_le _ _).trans ?_) a3
            rw [a2]; gcongr
        _ = hs (uMat g₀) := by rw [← nG_sq]; ring
        _ ≤ Y := hY
    clear_value Z
    have hM : ‖actM (smE ε π) Z (actM (smE ε π) Z x)‖ ≤ T ^ (4 * b) := by
      refine (hb2 Z).trans ?_
      have hZ0 : 0 ≤ hs Z := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
      have a1 : Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ n + 1 :=
        (le_mul_of_one_le_right (Real.sqrt_nonneg _) hs1).trans hsN
      have a2 : Real.sqrt (hs Z) * (8 * Real.sqrt ((n + 1 : ℕ) : ℝ) * (B + 2)) ≤ T ^ 2 := by
        calc _ ≤ Y * (8 * (n + 1) * (4 * B)) := by gcongr <;> linarith
          _ = 4 * (8 * ((n : ℝ) + 1) * B * Y) := by ring
          _ ≤ 4 * T := by linarith
          _ ≤ T ^ 2 := by nlinarith
      calc _ = (Real.sqrt (hs Z) * (8 * Real.sqrt ((n + 1 : ℕ) : ℝ) * (B + 2))) ^ 2 := by
            rw [mul_pow (Real.sqrt (hs Z)), Real.sq_sqrt hZ0]
        _ ≤ (T ^ 2) ^ 2 := pow_le_pow_left₀ (by have : 0 ≤ B := by linarith
                                                positivity) a2 2
        _ = T ^ 4 := by ring
        _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
    refine (lint_le hn1 ν (C := 3 * T ^ (4 * b) * r) (by positivity) hδ hδ1 fun h => ?_).trans
      (mul_le_mul_left (hfin _ (by positivity) le_rfl) _)
    set u : A := π (uMat (g₀⁻¹ * embG hF h * g₀)) v with hu
    have hid : ∀ s, ⟪π (uMat (d s)) (x : A), u⟫_ℂ = f ((c s)⁻¹ * h) := by
      intro s
      have a1 := hπ.1.2 _ (embG hF ((c s)⁻¹ * h)).2 _ g₀.2
      have a2 : π (uMat (embG hF ((c s)⁻¹ * h))) (π (uMat g₀) v) = π (uMat (embG hF ((c s)⁻¹ * h) * g₀)) v := by
        change _ = π (uMat (embG hF ((c s)⁻¹ * h)) * uMat g₀) v
        rw [a1]; rfl
      simp only [f]
      rw [hx, hu, a2, inner_move hπ, inner_move hπ]
      congr 3
      simp only [d, map_mul, map_inv]
      group
    have hη : ∀ s ∈ Set.Icc (0 : ℝ) 2, ‖⟪π (uMat (d s)) (x : A), u⟫_ℂ‖ ≤ D * ((nG h)⁻¹ ^ b) ^ 2 := by
      intro s hs'
      rw [hid]
      refine (hf _).trans ?_
      have a1 : nG (c s) ≤ Q := by
        unfold nG
        rw [hc, Real.sqrt_le_iff]
        refine ⟨by positivity, (ReciprocityTheory.ChartRestriction.DS.S7.hs_exp_leVG _).trans ?_⟩
        have a2 : Real.sqrt (ReciprocityTheory.ChartRestriction.DS.S7.hs ((s : ℂ) • X')) ≤ 2 := by
          change Real.sqrt (hs _) ≤ 2
          rw [hs_smul, Real.sqrt_le_iff]
          refine ⟨by norm_num, ?_⟩
          have : 0 ≤ hs X' := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
          have : s ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ hs'.1 hs'.2 2
          nlinarith
        rw [hQ, mul_pow, Real.sq_sqrt (by linarith), ← Real.exp_nat_mul]
        gcongr
        push_cast
        linarith
      have a3 : nG h ≤ Q * nG ((c s)⁻¹ * h) := by
        have := nG_mul (c s) ((c s)⁻¹ * h)
        rw [mul_inv_cancel_left] at this
        exact this.trans (mul_le_mul_of_nonneg_right a1 (Real.sqrt_nonneg _))
      have a4 := one_le_nG hn1 h
      have a5 := one_le_nG hn1 ((c s)⁻¹ * h)
      have a6 : (nG ((c s)⁻¹ * h))⁻¹ ≤ Q * (nG h)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by linarith), inv_mul_le_iff₀ (by linarith)]; linarith
      calc _ ≤ P ^ (2 * b) * (Q * (nG h)⁻¹) ^ (2 * b) := by gcongr
        _ = _ := by rw [hD]; ring
    have h1 := coef_interp hπ x d0 dadd dd (by rw [hu, hπ.2.1 _ (g₀⁻¹ * embG hF h * g₀).2, hv1]) hM hη (hτ h).1 (hτ h).2
      ⟨hr0, hr1⟩
    rw [hid, hid, hc0, inv_one, one_mul] at h1
    refine h1.trans ?_
    have a1 := (hτ h).1
    have e1 : 2 * (D * ((nG h)⁻¹ ^ b) ^ 2) / (nG h)⁻¹ ^ b = 2 * D * (nG h)⁻¹ ^ b := by field_simp
    rw [e1]
    have : 0 ≤ (nG h)⁻¹ ^ b * r := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hDT this]

theorem analytic_estimates : Analysis := ⟨volume_ratio_bound, decay_estimate, integral_ratio_bound, h_integrability, derivative_upper_bound, lipschitz_estimate⟩

end CompanionTheory.Lime.T3
end
end
