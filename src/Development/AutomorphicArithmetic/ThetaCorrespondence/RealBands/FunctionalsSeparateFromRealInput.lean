import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCuspFormPeriodNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodNonvanishingOfArchimedeanInputs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesCuspidal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesMultiplicity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClosedParabolicSubgroups
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.DecaysZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Abstract
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SchurOrthogonalityIndefiniteUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanSignatureFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealVectorsAllPlacesOfLocalData
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchDefs
import Development.AutomorphicArithmetic.ThetaCorrespondence.BesselModels.Separate

section
open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

theorem UpperTheory.Lit.Cusp.conv_coef :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d : ℝ), IsURepOn (UJset ε) σ → IsFdeg (muG ε) σ d → ∀ v a : H,
        Continuous (coefOn (ε := ε) σ a v) ∧
          ∀ x, conv (muG ε) (coefOn σ v v) (coefOn σ a v) x = ((‖v‖ ^ 2 / d : ℝ) : ℂ) * coefOn σ a v x := by
  intro n ε H _ _ σ d hrep hF v a
  obtain ⟨⟨_, hmul⟩, hiso, hcont⟩ := hrep
  have hinner : ∀ g ∈ UJset ε, ∀ x y : H, ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g hg x y =>
    LinearIsometry.inner_map_map ⟨(σ g).toLinearMap, hiso g hg⟩ x y
  have hmem : ∀ g : UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hcoef : ∀ w z : H, Continuous (coefOn (ε := ε) σ w z) := by
    intro w z
    have hu : Continuous fun g : UJ ε => umat g :=
      Units.continuous_val.comp continuous_subtype_val
    have hs : Continuous fun g : UJ ε => σ (umat g) w :=
      (hcont w).comp_continuous hu hmem
    exact continuous_const.inner hs
  refine ⟨hcoef a v, fun x => ?_⟩
  have hback : ∀ (g : UJ ε) (y : H), σ (umat g) (σ (umat g⁻¹) y) = y := by
    intro g y
    have h := hmul _ (hmem g) _ (hmem g⁻¹)
    have hone : umat g * umat g⁻¹ = 1 := by
      show ((g * g⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ).val = 1
      rw [mul_inv_cancel]
      rfl
    rw [hone] at h
    have h1 : σ 1 = 1 := by assumption
    rw [h1] at h
    exact (congrArg (fun f : H →L[ℂ] H => f y) h).symm
  have key : ∀ g : UJ ε, coefOn σ v v g * coefOn σ a v (g⁻¹ * x) =
      coefOn σ v v g * star (coefOn σ v (σ (umat x) a) g) := by
    intro g
    congr 1
    simp only [coefOn]
    have hsplit : σ (umat (g⁻¹ * x)) a = σ (umat g⁻¹) (σ (umat x) a) := by
      rw [show umat (g⁻¹ * x) = umat g⁻¹ * umat x from rfl, hmul _ (hmem _) _ (hmem _)]
      rfl
    rw [hsplit]
    calc ⟪v, σ (umat g⁻¹) (σ (umat x) a)⟫_ℂ
        = ⟪σ (umat g) v, σ (umat g) (σ (umat g⁻¹) (σ (umat x) a))⟫_ℂ :=
          (hinner _ (hmem g) _ _).symm
      _ = ⟪σ (umat g) v, σ (umat x) a⟫_ℂ := by rw [hback]
      _ = star ⟪σ (umat x) a, σ (umat g) v⟫_ℂ := by
          rw [← inner_conj_symm]
          rfl
  show ∫ g, coefOn σ v v g * coefOn σ a v (g⁻¹ * x) ∂(muG ε) = _
  rw [show (fun g => coefOn σ v v g * coefOn σ a v (g⁻¹ * x)) =
      fun g => coefOn σ v v g * star (coefOn σ v (σ (umat x) a) g) from funext key,
    (hF.2 v v v (σ (umat x) a)).2, inner_self_eq_norm_sq_to_K]
  show _ = _ * ⟪v, σ (umat x) a⟫_ℂ
  push_cast
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc, mul_comm]
  rw [mul_comm (_ * _) _, mul_comm ⟪v, σ (umat x) a⟫_ℂ, ← mul_assoc]
  rfl
end

section
open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

theorem UpperTheory.Lit.Cusp.isCompact_ball :
    ∀ (n : ℕ) (ε : Fin n → Bool), (∀ R : ℝ, IsCompact {g : UJ ε | hs (umat g) ≤ R}) ∧
      (∀ x y : Matrix (Fin n) (Fin n) ℂ, Real.sqrt (hs (x * y)) ≤ Real.sqrt (hs x) * Real.sqrt (hs y)) ∧
      (∀ g : UJ ε, hs (umat g⁻¹) = hs (umat g)) ∧ Continuous (fun g : UJ ε => hs (umat g)) := by
  intro n ε
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro R
    obtain ⟨hemb, -⟩ := isClosedEmbeddingMatrix n ε
    have hK := (hermitian_small_ball n ε).1 R
    have hpre := hemb.isCompact_preimage hK
    convert hpre using 1
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · intro h
      exact ⟨g.2, h⟩
    · intro h
      exact h.2
  · intro x y
    rw [← Real.sqrt_mul (frobenius_nonneg x)]
    exact Real.sqrt_le_sqrt (frobenius_mul_le x y)
  · intro g
    have h1 : umat g⁻¹ = Jm ε * (coeMatrixAlt ε g)ᴴ * Jm ε := coeMatrix_inv_eq ε g
    have h2 : coeMatrixAlt ε g = umat g := rfl
    rw [h1, h2]
    have hd : ∀ i, ‖(if ε i = true then (1 : ℂ) else -1)‖ = 1 := by
      intro i
      split <;> simp
    simp only [hs, Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, norm_mul, hd,
      one_mul, mul_one, norm_star]
    exact Finset.sum_comm
  · exact continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)
end

section
open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

private lemma wt_le {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) (x : MatrixCoordinates n)
    (h : hs (coeMatrixAlt ε g⁻¹ * Matrix.of x - 1) < 1 / 4) :
    (wt g)⁻¹ ≤ (Real.sqrt n + 1) ^ (2 * n ^ 2 + 1) * (1 + ‖x‖) ^ (-((2 * n ^ 2 + 1 : ℕ) : ℝ)) := by
  set R : ℝ := Real.sqrt (hs (umat g)) with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hs0 : 0 ≤ hs (umat g) := by unfold hs; positivity
  have hg : hs (coeMatrixAlt ε g) ≤ R ^ 2 := by rw [hR, Real.sq_sqrt hs0]; exact le_rfl
  have hn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hρ0 : 0 ≤ R * (Real.sqrt n + 1) := by positivity
  have hx : ‖x‖ ≤ R * (Real.sqrt n + 1) := by
    rw [pi_norm_le_iff_of_nonneg hρ0]
    intro i
    rw [pi_norm_le_iff_of_nonneg hρ0]
    intro j
    have := norm_entry_mul_near_one_le (g := coeMatrixAlt ε g) hR0 hg h i j
    rw [← Matrix.mul_assoc, determinant_character_mul_inv, Matrix.one_mul] at this
    exact this
  have h1 : 1 + ‖x‖ ≤ (Real.sqrt n + 1) * (1 + R) := by nlinarith
  have h2 : (1 + ‖x‖) ^ (2 * n ^ 2 + 1) ≤ (Real.sqrt n + 1) ^ (2 * n ^ 2 + 1) * wt g := by
    unfold wt
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 _
  have hw : 0 < wt g := by unfold wt; positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, inv_eq_one_div,
    div_le_div_iff₀ hw (by positivity), one_mul]
  exact h2

private lemma slice_le {n : ℕ} {ε : Fin n → Bool} (S : Subgroup (UJ ε)) (ν : Measure (UJ ε))
    (hν : IsHaarSub (S : Set (UJ ε)) ν) (x : MatrixCoordinates n) :
    ν {g | hs (coeMatrixAlt ε g⁻¹ * Matrix.of x - 1) < 1 / 4} ≤
      ν {k | hsG k ≤ (2 * Real.sqrt n + 1) ^ 2} := by
  obtain ⟨-, -, h0, hinv⟩ := hν
  set A : Set (UJ ε) := {g | hs (coeMatrixAlt ε g⁻¹ * Matrix.of x - 1) < 1 / 4} with hA
  set W : Set (UJ ε) := {k | hsG k ≤ (2 * Real.sqrt n + 1) ^ 2} with hW
  have hWm : MeasurableSet W :=
    (isClosed_le (continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)) continuous_const).measurableSet
  by_cases hne : (A ∩ (S : Set (UJ ε))).Nonempty
  · obtain ⟨h, hh, hS⟩ := hne
    calc ν A ≤ ν ((fun g => h⁻¹ * g) ⁻¹' W) := by
          refine measure_mono fun g hg => ?_
          show hs (coeMatrixAlt ε (h⁻¹ * g)) ≤ _
          refine frobenius_bound_of_mul_near_one hg hh ?_
          rw [determinant_character_mul, ← Matrix.mul_assoc, Matrix.mul_assoc (coeMatrixAlt ε h⁻¹),
            determinant_character_mul_inv, Matrix.mul_one]
      _ = ν.map (fun g => h⁻¹ * g) W := (Measure.map_apply (measurable_const_mul _) hWm).symm
      _ = ν W := by rw [hinv h⁻¹ (S.inv_mem hS)]
  · have : ν A = 0 := measure_mono_null (fun g hg hS => hne ⟨g, hg, hS⟩) h0
    rw [this]
    exact bot_le

theorem UpperTheory.Lit.Cusp.integrable_wt :
    ∀ (n : ℕ) (ε : Fin n → Bool) (S : Subgroup (UJ ε)) (ν : Measure (UJ ε)), IsHaarSub (S : Set (UJ ε)) ν →
      Integrable (fun g : UJ ε => (wt g)⁻¹) ν := by
  intro n ε S ν hν
  classical
  haveI : IsFiniteMeasureOnCompacts ν := hν.2.1
  let lam : Measure (MatrixCoordinates n) := Measure.addHaar
  let O : Set (MatrixCoordinates n) := {x | hs (Matrix.of x - 1) < 1 / 4}
  let W : Set (UJ ε) := {k | hsG k ≤ (2 * Real.sqrt n + 1) ^ 2}
  have hof : Continuous (fun x : MatrixCoordinates n => Matrix.of x) := continuous_id
  have hO_open : IsOpen O :=
    isOpen_lt (continuous_hs_real_place_taylor.comp (hof.sub continuous_const)) continuous_const
  have hO_pos : 0 < lam O := hO_open.measure_pos lam ⟨Matrix.of.symm 1, by simp [O, hs]⟩
  have hW_fin : ν W < ⊤ := by
    have hc : IsCompact W := by
      have := (isClosedEmbeddingMatrix n ε).1.isCompact_preimage
        ((hermitian_small_ball n ε).1 ((2 * Real.sqrt n + 1) ^ 2))
      convert this using 1
      ext g
      exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
    exact hc.measure_lt_top
  have hwpos : ∀ g : UJ ε, 0 < wt g := fun g => by unfold wt; positivity
  have hwc : Continuous fun g : UJ ε => (wt g)⁻¹ := by
    refine Continuous.inv₀ ?_ fun g => (hwpos g).ne'
    exact (continuous_const.add (continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)).sqrt).pow _
  let w : UJ ε → ENNReal := fun g => ENNReal.ofReal (wt g)⁻¹
  have hwm : Measurable w := hwc.measurable.ennreal_ofReal
  let U : Set (UJ ε × MatrixCoordinates n) := {p | hs (coeMatrixAlt ε p.1⁻¹ * Matrix.of p.2 - 1) < 1 / 4}
  have hU : MeasurableSet U :=
    (isOpen_lt (continuous_hs_real_place_taylor.comp ((((continuous_coeMatrix ε).comp (continuous_inv.comp continuous_fst)).matrix_mul
      (hof.comp continuous_snd)).sub continuous_const)) continuous_const).measurableSet
  let f : UJ ε → MatrixCoordinates n → ENNReal := fun g x => U.indicator (fun p => w p.1) (g, x)
  have hf : Measurable (Function.uncurry f) := (hwm.comp measurable_fst).indicator hU
  have h1 : ∫⁻ g, ∫⁻ x, f g x ∂lam ∂ν = (∫⁻ g, w g ∂ν) * lam O := by
    rw [← lintegral_mul_const _ hwm]
    refine lintegral_congr fun g => ?_
    have hdet : LinearMap.det (leftMulReal (coeMatrixAlt ε g⁻¹)) = 1 := det_leftMulReal_eq_one (g⁻¹).2
    have e : f g = (leftMulReal (coeMatrixAlt ε g⁻¹) ⁻¹' O).indicator fun _ => w g := by
      funext x
      rfl
    have hm : MeasurableSet (leftMulReal (coeMatrixAlt ε g⁻¹) ⁻¹' O) :=
      (hO_open.preimage (LinearMap.continuous_of_finiteDimensional _)).measurableSet
    rw [e, lintegral_indicator_const hm,
      Measure.addHaar_preimage_linearMap lam (by rw [hdet]; exact one_ne_zero), hdet]
    simp
  let c : ENNReal := ENNReal.ofReal ((Real.sqrt n + 1) ^ (2 * n ^ 2 + 1))
  let b : MatrixCoordinates n → ENNReal := fun x => ENNReal.ofReal ((1 + ‖x‖) ^ (-((2 * n ^ 2 + 1 : ℕ) : ℝ)))
  have hfr : Module.finrank ℝ (MatrixCoordinates n) = 2 * n ^ 2 := by
    simp [MatrixCoordinates, Module.finrank_pi_fintype, Complex.finrank_real_complex]; ring
  have hb : ∫⁻ x, b x ∂lam < ⊤ :=
    finite_integral_one_add_norm (by rw [hfr]; exact_mod_cast Nat.lt_succ_self _)
  have h2 : ∀ x, ∫⁻ g, f g x ∂ν ≤ (c * ν W) * b x := by
    intro x
    have hm : MeasurableSet {g : UJ ε | hs (coeMatrixAlt ε g⁻¹ * Matrix.of x - 1) < 1 / 4} :=
      measurable_prodMk_right hU
    calc ∫⁻ g, f g x ∂ν
        ≤ ∫⁻ g, {g : UJ ε | hs (coeMatrixAlt ε g⁻¹ * Matrix.of x - 1) < 1 / 4}.indicator
            (fun _ => c * b x) g ∂ν := by
          refine lintegral_mono fun g => ?_
          by_cases hg : hs (coeMatrixAlt ε g⁻¹ * Matrix.of x - 1) < 1 / 4
          · have hgU : (g, x) ∈ U := hg
            simp only [f]
            rw [Set.indicator_of_mem hgU, Set.indicator_of_mem (by exact hg)]
            simp only [w, c, b]
            rw [← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal (wt_le g x hg)
          · have hgU : (g, x) ∉ U := hg
            simp only [f]
            rw [Set.indicator_of_notMem hgU]
            exact bot_le
      _ = c * b x * ν {g : UJ ε | hs (coeMatrixAlt ε g⁻¹ * Matrix.of x - 1) < 1 / 4} :=
          lintegral_indicator_const hm _
      _ ≤ c * b x * ν W := mul_le_mul' le_rfl (slice_le S ν hν x)
      _ = (c * ν W) * b x := by ring
  have hcW : c * ν W ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hW_fin.ne
  have h3 : (∫⁻ g, w g ∂ν) * lam O < ⊤ := by
    rw [← h1, lintegral_lintegral_swap hf.aemeasurable]
    refine (lintegral_mono h2).trans_lt ?_
    rw [lintegral_const_mul' _ _ hcW]
    exact ENNReal.mul_lt_top hcW.lt_top hb
  have h4 : ∫⁻ g, w g ∂ν < ⊤ := ENNReal.lt_top_of_mul_ne_top_left h3.ne hO_pos.ne'
  refine ⟨hwc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun g => inv_nonneg.2 (hwpos g).le)]
  exact h4
end

section
open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

private theorem wt_pos' {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : 0 < wt g := by
  unfold wt; positivity

private theorem wt_mul_le {n : ℕ} {ε : Fin n → Bool} (g h : UJ ε) : wt (g * h) ≤ wt g * wt h := by
  unfold wt
  rw [← mul_pow]
  have h1 := (isCompact_ball n ε).2.1 (umat g) (umat h)
  have e : umat (g * h) = umat g * umat h := rfl
  rw [e]
  have a := Real.sqrt_nonneg (hs (umat g))
  have b := Real.sqrt_nonneg (hs (umat h))
  refine pow_le_pow_left₀ (by positivity) ?_ _
  nlinarith

private theorem wt_inv' {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : wt g⁻¹ = wt g := by
  unfold wt
  rw [(isCompact_ball n ε).2.2.1 g]

private theorem continuous_wt' {n : ℕ} (ε : Fin n → Bool) : Continuous fun g : UJ ε => wt g := by
  unfold wt
  exact (continuous_const.add (isCompact_ball n ε).2.2.2.sqrt).pow _

private theorem norm_translate_le {n : ℕ} {ε : Fin n → Bool} {f : UJ ε → ℂ} {C : ℝ}
    (hC : ∀ g, ‖f g‖ * wt g ≤ C) (x m y : UJ ε) : ‖f (x * m * y)‖ ≤ C * wt x * wt y * (wt m)⁻¹ := by
  have h1 : wt m ≤ wt x * wt (x * m * y) * wt y := by
    calc wt m = wt (x⁻¹ * (x * m * y) * y⁻¹) := by congr 1; group
      _ ≤ wt (x⁻¹ * (x * m * y)) * wt y⁻¹ := wt_mul_le _ _
      _ ≤ wt x⁻¹ * wt (x * m * y) * wt y⁻¹ :=
        mul_le_mul_of_nonneg_right (wt_mul_le _ _) (wt_pos' _).le
      _ = _ := by rw [wt_inv', wt_inv']
  rw [← div_eq_mul_inv, le_div_iff₀ (wt_pos' m)]
  calc ‖f (x * m * y)‖ * wt m ≤ ‖f (x * m * y)‖ * (wt x * wt (x * m * y) * wt y) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖f (x * m * y)‖ * wt (x * m * y) * (wt x * wt y) := by ring
    _ ≤ C * (wt x * wt y) :=
        mul_le_mul_of_nonneg_right (hC _) (mul_pos (wt_pos' _) (wt_pos' _)).le
    _ = _ := by ring

theorem UpperTheory.Lit.Cusp.continuous_average :
    ∀ (n : ℕ) (ε : Fin n → Bool) (f : UJ ε → ℂ), Continuous f → Decays f → Integrable f (muG ε) ∧
      ∀ (S : Subgroup (UJ ε)) (ν : Measure (UJ ε)), IsHaarSub (S : Set (UJ ε)) ν →
        ∀ x, Continuous fun y => ∫ m, f (x * m * y) ∂ν := by
  intro n ε f hf ⟨C, hC⟩
  have hC0 : 0 ≤ C := le_trans (mul_nonneg (norm_nonneg _) (wt_pos' _).le) (hC 1)
  refine ⟨?_, fun S ν hν x => ?_⟩
  · have hH : IsHaarSub ((⊤ : Subgroup (UJ ε)) : Set (UJ ε)) (muG ε) := by
      haveI : (muG ε).IsHaarMeasure := by unfold muG; infer_instance
      exact GlobalTheory.Dec.isHaarSub_univ (muG ε)
    refine ((integrable_wt n ε ⊤ _ hH).const_mul C).mono' hf.aestronglyMeasurable
      (Eventually.of_forall fun g => ?_)
    rw [← div_eq_mul_inv, le_div_iff₀ (wt_pos' g)]
    exact hC g
  · rw [continuous_iff_continuousAt]
    intro y₀
    refine continuousAt_of_dominated (bound := fun m => C * wt x * (wt y₀ + 1) * (wt m)⁻¹) ?_ ?_
      ((integrable_wt n ε S ν hν).const_mul _) ?_
    · exact Eventually.of_forall fun y =>
        (hf.comp ((continuous_const.mul continuous_id).mul continuous_const)).aestronglyMeasurable
    · have hn : ∀ᶠ y in 𝓝 y₀, wt y < wt y₀ + 1 :=
        (continuous_wt' ε).continuousAt.eventually (gt_mem_nhds (lt_add_one _))
      filter_upwards [hn] with y hy
      refine Eventually.of_forall fun m => (norm_translate_le hC x m y).trans ?_
      have := wt_pos' x
      have := wt_pos' m
      gcongr
    · exact Eventually.of_forall fun m => (hf.comp (continuous_const.mul continuous_id)).continuousAt
end

section
open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

theorem UpperTheory.Lit.Cusp.exists_split :
    ∀ (n : ℕ) (ε : Fin n → Bool) (j : Fin 1 → ℕ) (W : Flag n 1), IsIsoFlag ε j W →
      ∃ a : ℝ → UJ ε, Continuous a ∧ (∀ s t, a (s + t) = a s * a t) ∧ ∀ t, IsSplit ε W (fun _ => t) (a t) := by
  intro n ε j W hW
  obtain ⟨P, h0, h1, h2⟩ := GlobalTheory.RealIwasawa.exists_proj (W (Fin.last 1))
  have hJ := Jm_mul_self ε
  have hPP : P * P = P := Matrix.ext_iff_mulVec.2 fun y => by rw [← mulVec_mulVec, h2 _ (h1 y)]
  have hi : P * Jm ε * P = 0 := GlobalTheory.RealIwasawa.proj_iso hW h0 fun y => h1 y
  have key : ∀ r : ℝ, ∃ t : UJ ε,
      uMat t = GlobalTheory.IsoTorus.tor P (Jm ε * P * Jm ε) (Real.exp r) (Real.exp (-r)) := by
    intro r
    set Q := Jm ε * P * Jm ε with hQ
    have hQQ : Q * Q = Q := by
      simp only [hQ, mul_assoc]; rw [← mul_assoc (Jm ε) (Jm ε), hJ, one_mul, ← mul_assoc P P, hPP]
    have hPQ : P * Q = 0 := by rw [hQ, ← mul_assoc, ← mul_assoc, hi, zero_mul]
    have hQP : Q * P = 0 := by rw [hQ, mul_assoc, mul_assoc, ← mul_assoc P, hi, mul_zero]
    set c : ℂ := (Real.exp r : ℂ) with hc
    set d : ℂ := (Real.exp (-r) : ℂ) with hd
    have hH : (GlobalTheory.IsoTorus.tor P Q c d)ᴴ = GlobalTheory.IsoTorus.tor P Q c d := by
      simp [GlobalTheory.IsoTorus.tor, hQ, h0, Jm_conjTranspose, hc, hd, mul_assoc, -Complex.ofReal_exp]
    have hm : (GlobalTheory.IsoTorus.tor P Q c d)ᴴ * Jm ε * GlobalTheory.IsoTorus.tor P Q c d = Jm ε := by
      have e : GlobalTheory.IsoTorus.tor P Q c d * Jm ε = Jm ε * GlobalTheory.IsoTorus.tor P Q d c := by
        simp only [GlobalTheory.IsoTorus.tor, hQ, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
          mul_assoc, hJ, ← mul_assoc (Jm ε) (Jm ε)]
        abel
      rw [hH, e, mul_assoc, GlobalTheory.IsoTorus.tor_tor hPP hQQ hPQ hQP, hc, hd, ← Complex.ofReal_mul,
        ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
      simp [GlobalTheory.IsoTorus.tor_one]
    obtain ⟨t, ht, -⟩ := GlobalTheory.RealIwasawa.exists_uMat _ hm
    exact ⟨t, ht⟩
  choose a ha using key
  have hs : ∀ t, IsSplit ε W (fun _ => t) (a t) := fun t => by
    convert isSplit_of_tor hW h0 h1 h2 (ha t) using 2 with i
    rw [if_pos (Fin.le_last _)]
  refine ⟨a, ?_, fun s t => ?_, hs⟩
  · refine (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isInducing.continuous_iff.2 ?_
    refine Continuous.congr (f := fun r : ℝ => GlobalTheory.IsoTorus.tor P (Jm ε * P * Jm ε) (Real.exp r) (Real.exp (-r)))
      ?_ fun r => (ha r).symm
    unfold GlobalTheory.IsoTorus.tor
    fun_prop
  · exact (existsUnique_isSplit hW (fun _ => s + t)).unique (hs _) ((hs s).mul (hs t))
end

section
open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

private theorem act_mul {n : ℕ} {ε : Fin n → Bool} (g h : UJ ε) (y : Fin n → ℂ) :
    uMat (g * h) *ᵥ y = uMat g *ᵥ (uMat h *ᵥ y) := by
  rw [mulVec_mulVec]; rfl

private theorem act_inv {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) (y : Fin n → ℂ) :
    uMat g⁻¹ *ᵥ (uMat g *ᵥ y) = y := by
  rw [← act_mul, inv_mul_cancel]; exact one_mulVec y

private theorem act_inv' {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) (y : Fin n → ℂ) :
    uMat g *ᵥ (uMat g⁻¹ *ᵥ y) = y := by
  rw [← act_mul, mul_inv_cancel]; exact one_mulVec y

private theorem keeps_perp {n a : ℕ} {ε : Fin n → Bool} {W : Flag n a} {p : UJ ε} (hp : p ∈ parab ε W)
    {y : Fin n → ℂ} (hy : ∀ z ∈ W (Fin.last a), star z ⬝ᵥ (Jm ε *ᵥ y) = 0) :
    ∀ z ∈ W (Fin.last a), star z ⬝ᵥ (Jm ε *ᵥ (uMat p *ᵥ y)) = 0 := by
  intro z hz
  have hpiS : ∀ i, ∀ y ∈ W i, uMat p⁻¹ *ᵥ y ∈ W i := (parab ε W).inv_mem hp
  have h1 : Jm ε *ᵥ (uMat p *ᵥ y) = (uMat p⁻¹)ᴴ *ᵥ (Jm ε *ᵥ y) := by
    rw [mulVec_mulVec, mulVec_mulVec, conjTranspose_inv_mul_Jm]
  rw [h1, dotProduct_mulVec, ← star_mulVec]
  exact hy _ (hpiS _ _ hz)

private theorem conj_mem {n a : ℕ} {ε : Fin n → Bool} {W : Flag n a} {p m : UJ ε} (hp : p ∈ parab ε W)
    (hm : m ∈ flagN ε W) : p⁻¹ * m * p ∈ flagN ε W := by
  have e : ∀ y, uMat (p⁻¹ * m * p) *ᵥ y - y = uMat p⁻¹ *ᵥ (uMat m *ᵥ (uMat p *ᵥ y) - uMat p *ᵥ y) := fun y => by
    rw [mulVec_sub, act_inv, act_mul, act_mul]
  have hi := (parab ε W).inv_mem hp
  refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
  · rw [e]; exact hi _ _ (hm.1 i _ (hp _ y hy))
  · rw [e]; exact hi _ _ (hm.2 _ (keeps_perp hp hy))

private theorem comm_mem {n a : ℕ} {ε : Fin n → Bool} {W : Flag n a} {p t : UJ ε} {x : Fin a → ℝ}
    (hp : p ∈ parab ε W) (ht : IsSplit ε W x t) : t⁻¹ * (p * t * p⁻¹) ∈ flagN ε W := by
  have hpS : ∀ i, ∀ y ∈ W i, uMat p *ᵥ y ∈ W i := hp
  have hpiS : ∀ i, ∀ y ∈ W i, uMat p⁻¹ *ᵥ y ∈ W i := (parab ε W).inv_mem hp
  have htS : ∀ i, ∀ y ∈ W i, uMat t *ᵥ y ∈ W i := fun i y hy => (ht.1 i y hy).1
  have htiS : ∀ i, ∀ y ∈ W i, uMat t⁻¹ *ᵥ y ∈ W i :=
    (parab ε W).inv_mem (show t ∈ parab ε W from htS)
  simp only [flagN, Set.mem_setOf_eq]
  refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
  · have e : uMat (t⁻¹ * (p * t * p⁻¹)) *ᵥ y - y =
        uMat t⁻¹ *ᵥ (uMat p *ᵥ (uMat t *ᵥ (uMat p⁻¹ *ᵥ y) -
          (Real.exp (x i) : ℂ) • (uMat p⁻¹ *ᵥ y))) -
          uMat t⁻¹ *ᵥ (uMat t *ᵥ y - (Real.exp (x i) : ℂ) • y) := by
      simp only [act_mul, mulVec_sub, mulVec_smul, act_inv, act_inv']
      abel
    rw [e]
    exact Submodule.sub_mem _ (htiS _ _ (hpS _ _ (ht.2.1 i _ (hpiS _ _ hy))))
      (htiS _ _ (ht.2.1 i y hy))
  · have e : uMat (t⁻¹ * (p * t * p⁻¹)) *ᵥ y - y =
        uMat t⁻¹ *ᵥ (uMat p *ᵥ (uMat t *ᵥ (uMat p⁻¹ *ᵥ y) - uMat p⁻¹ *ᵥ y)) -
          uMat t⁻¹ *ᵥ (uMat t *ᵥ y - y) := by
      simp only [act_mul, mulVec_sub, act_inv, act_inv']
      abel
    rw [e]
    exact Submodule.sub_mem _
      (htiS _ _ (hpS _ _ (ht.2.2 _ (keeps_perp ((parab ε W).inv_mem hp) hy))))
      (htiS _ _ (ht.2.2 y hy))

theorem UpperTheory.Lit.Cusp.exists_isRay :
    ∀ (n : ℕ) (ε : Fin n → Bool) (j : Fin 1 → ℕ) (W : Flag n 1), IsIsoFlag ε j W → (∀ i, 1 ≤ j i) →
      ∃ (a : ℝ → UJ ε) (H : UJ ε → ℝ), IsRay (flagN ε W) a H := by
  intro n ε j W hW hj
  obtain ⟨a, ha_cont, ha_add, ha_split⟩ := exists_split n ε j W hW
  obtain ⟨h, hh_cont, hh1, hhK, hhP⟩ := exists_height hW hj
  obtain ⟨⟨N, hN⟩, -, -⟩ := UnipRad.flagN_subgroup_closed_keeps n ε 1 j W hW
  have hone_levi : (1 : UJ ε) ∈ leviOne ε W := (leviOne ε W).one_mem
  have hone_N : (1 : UJ ε) ∈ flagN ε W := hN ▸ N.one_mem
  have hN_inv : ∀ m ∈ flagN ε W, m⁻¹ ∈ flagN ε W := by
    intro m hm
    rw [← hN] at hm ⊢
    exact N.inv_mem hm
  have hsplit_par : ∀ t, a t ∈ parab ε W := fun t =>
    show ∀ i, ∀ y ∈ W i, uMat (a t) *ᵥ y ∈ W i from fun i y hy => ((ha_split t).1 i y hy).1
  have hheight : ∀ x t g, IsSplit ε W x t → h (t * g) = x + h g := by
    intro x t g hs
    have := hhP 1 hone_N 1 hone_levi x t hs g
    rwa [one_mul, one_mul] at this
  have ha0 : a 0 = 1 := by
    have h0 := congrArg (fun g => (a 0)⁻¹ * g) (ha_add 0 0)
    simp only [add_zero, inv_mul_cancel, ← mul_assoc, one_mul] at h0
    exact h0.symm
  have hainv : ∀ t, (a t)⁻¹ = a (-t) := fun t => by
    have h2 : a t * a (-t) = 1 := by rw [← ha_add, add_neg_cancel, ha0]
    exact (eq_inv_of_mul_eq_one_right h2).symm
  have hK : IsCompact (KG ε : Set (UJ ε)) := isCompact_iff_compactSpace.2 (instCompactKG n ε)
  have hkmem : ∀ k ∈ maxK ε, k ∈ KG ε := fun k hk => by
    rw [← SetLike.mem_coe, KG_eq]
    exact hk
  have hshift : ∀ y g : UJ ε, ∃ k ∈ KG ε, h (y * g) = h y + h (k * g) := by
    intro y g
    obtain ⟨k, hkK, hk⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact hW y
    obtain ⟨u, hu, m, hm, x, t, hs, hp⟩ := exists_langlands_decomp hW hj hk
    have hkG := hkmem k hkK
    refine ⟨k, hkG, ?_⟩
    have e1 : y * g = u * m * t * (k * g) := by
      rw [← hp]
      group
    have e2 : y = u * m * t * k := by
      rw [← hp]
      group
    have hk0 : h k = 0 := by
      have := hhK 1 k hkG
      rwa [one_mul, hh1] at this
    rw [e1, hhP u hu m hm x t hs, e2, hhP u hu m hm x t hs, hk0, add_zero]
  refine ⟨a, fun g => -(h g⁻¹ 0), ha_cont, ha_add, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t m hm
    exact conj_mem (hsplit_par t) hm
  · exact ((continuous_apply 0).comp (hh_cont.comp continuous_inv)).neg
  · intro g m hm
    show -(h (g * m)⁻¹ 0) = -(h g⁻¹ 0)
    have := hhP m⁻¹ (hN_inv m hm) 1 hone_levi 0 1 isSplit_one g⁻¹
    rw [mul_one, mul_one, zero_add] at this
    rw [_root_.mul_inv_rev, this]
  · intro g t
    show -(h (g * a t)⁻¹ 0) = -(h g⁻¹ 0) + t
    rw [_root_.mul_inv_rev, hainv, hheight _ _ _ (ha_split (-t))]
    simp only [Pi.add_apply]
    ring
  · intro D hD
    have hS : IsCompact ((fun q : UJ ε × UJ ε => q.1 * q.2) '' ((KG ε : Set (UJ ε)) ×ˢ D)) :=
      (hK.prod hD).image continuous_mul
    obtain ⟨c, hc⟩ := hS.exists_bound_of_continuousOn (f := fun g => h g 0)
      ((continuous_apply 0).comp hh_cont).continuousOn
    refine ⟨c, fun g hg x => ?_⟩
    obtain ⟨k, hk, hyg⟩ := hshift x⁻¹ g
    show |-(h (g⁻¹ * x)⁻¹ 0) - -(h x⁻¹ 0)| ≤ c
    rw [_root_.mul_inv_rev, _root_.inv_inv, hyg]
    have hb := hc (k * g) ⟨(k, g), ⟨hk, hg⟩, rfl⟩
    rw [Real.norm_eq_abs] at hb
    have e : -((h x⁻¹ + h (k * g)) 0) - -(h x⁻¹ 0) = -(h (k * g) 0) := by
      simp only [Pi.add_apply]
      ring
    rw [e, abs_neg]
    exact hb
  · refine ⟨(KG ε : Set (UJ ε)), hK, fun x => ?_⟩
    obtain ⟨k, hkK, hk⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact hW x⁻¹
    have hkG := hkmem k hkK
    refine ⟨k⁻¹, (KG ε).inv_mem hkG, fun t => ?_⟩
    have hq : x⁻¹ * k⁻¹ ∈ parab ε W := hk
    refine ⟨(a t)⁻¹ * ((x⁻¹ * k⁻¹) * a t * (x⁻¹ * k⁻¹)⁻¹), comm_mem hq (ha_split t), ?_⟩
    group
end

section
open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

private theorem herm_eq_zero_iff {n : ℕ} (ε : Fin n → Bool) (x y : Fin n → ℂ) :
    Formalism.QuantumDeterminants.herm (Jm ε) x y = 0 ↔ star x ⬝ᵥ (Jm ε *ᵥ y) = 0 := by
  have e : Formalism.QuantumDeterminants.herm (Jm ε) x y = star (star x ⬝ᵥ (Jm ε *ᵥ y)) := by
    simp only [Formalism.QuantumDeterminants.herm, Jm, dotProduct, Matrix.mulVec_diagonal, star_sum, Pi.star_apply, star_mul', star_star]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases ε i <;> simp <;> ring
  rw [e, star_eq_zero]

private theorem herm_keep {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * H * g = H) (x y : Fin n → ℂ) :
    Formalism.QuantumDeterminants.herm H (g *ᵥ x) (g *ᵥ y) = Formalism.QuantumDeterminants.herm H x y := by
  simp only [Formalism.QuantumDeterminants.herm]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

theorem UpperTheory.Lit.Cusp.flagN_eq_NW :
    ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)), IsIsoC ε W →
      IsIsoFlag ε ![Module.finrank ℂ W] ![⊥, W] ∧ 1 ≤ Module.finrank ℂ W ∧ flagN ε ![⊥, W] = NW ε W ∧
        ∃ S : Subgroup (UJ ε), (S : Set (UJ ε)) = NW ε W := by
  intro n ε W hW
  have hl : (![⊥, W] : Fin (1 + 1) → Submodule ℂ (Fin n → ℂ)) (Fin.last 1) = W := rfl
  refine ⟨⟨rfl, ?_, ?_, ?_⟩, ?_, ?_, GlobalTheory.Dec.nwSub ε W, rfl⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i
    show Module.finrank ℂ W = Module.finrank ℂ (⊥ : Submodule ℂ (Fin n → ℂ)) + Module.finrank ℂ W
    rw [finrank_bot, zero_add]
  · rw [hl]
    intro x hx y hy
    exact (herm_eq_zero_iff ε x y).1 (hW.2 x hx y hy)
  · exact Submodule.one_le_finrank_iff.2 hW.1
  · ext g
    have e : ∀ y, (umat g - 1) *ᵥ y = uMat g *ᵥ y - y := fun y => by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    simp only [flagN, NW, Set.mem_setOf_eq, hl, e]
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : ∀ x ∈ W, uMat g *ᵥ x - x = 0 := fun x hx => (Submodule.mem_bot ℂ).1 (h1 0 x hx)
      refine ⟨h1', fun y hy => h2 y fun x hx => (herm_eq_zero_iff ε x y).1 (hy x hx), fun y x hx => ?_⟩
      have hg : (uMat g)ᴴ * Jm ε * uMat g = Jm ε := g.2
      have k := herm_keep hg x y
      rw [sub_eq_zero.1 (h1' x hx)] at k
      simp only [Formalism.QuantumDeterminants.herm, star_sub, sub_dotProduct] at k ⊢
      rw [k, sub_self]
    · rintro ⟨h1, h2, -⟩
      refine ⟨fun i y hy => ?_, fun y hy => h2 y fun x hx => (herm_eq_zero_iff ε x y).2 (hy x hx)⟩
      fin_cases i
      exact (Submodule.mem_bot ℂ).2 (h1 y hy)
end

section
open MeasureTheory Filter Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd UpperTheory.Lit.Cusp
open GlobalTheory.Dec (IsHaarSub IsIsoC NW IsSqIntIrr)
open scoped Topology InnerProductSpace

theorem UpperTheory.Lit.Cusp.integral_coef_eq_zero :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsSqIntIrr ε σ → ∀ v a : H,
        Decays (coefOn (ε := ε) σ v v) → Decays (coefOn (ε := ε) σ a v) →
        ∀ W, IsIsoC ε W → ∀ ν : Measure (UJ ε), IsHaarSub (NW ε W) ν → ∀ x y : UJ ε,
          ∫ m, ⟪v, σ (umat (x * m * y)) a⟫_ℂ ∂ν = 0 := by
  intro n ε H _ _ σ hσ v a hvv hav W hW ν hν x y
  obtain ⟨hc, hn, hU, hI, hS⟩ := hσ
  obtain ⟨d, hd⟩ := GlobalTheory.T.schur_orthogonality_indefiniteUnitaryGroup n ε H σ hU hI hS
  have hd0 : 0 < d := hd.1
  by_cases hv : v = 0
  · subst hv
    simp
  have hv2 : (‖v‖ : ℝ) ^ 2 ≠ 0 := by positivity
  obtain ⟨hcvv, hconvvv⟩ := conv_coef n ε H σ d hU hd v v
  obtain ⟨hcav, hconvav⟩ := conv_coef n ε H σ d hU hd v a
  obtain ⟨hivv, -⟩ := continuous_average n ε _ hcvv hvv
  obtain ⟨hiav, hcontav⟩ := continuous_average n ε _ hcav hav
  obtain ⟨hν0, hνf, hνN, hνinv⟩ := hν
  haveI := hνf
  obtain ⟨hflag, h1, hNeq, S, hS⟩ := flagN_eq_NW n ε W hW
  obtain ⟨r, Hr, hr⟩ := exists_isRay n ε _ _ hflag (fun i => by fin_cases i; simpa using h1)
  rw [hNeq] at hr
  set k : ℂ := ((d / ‖v‖ ^ 2 : ℝ) : ℂ) with hk
  have hkc : k * ((‖v‖ ^ 2 / d : ℝ) : ℂ) = 1 := by
    rw [hk, ← Complex.ofReal_mul]
    rw [div_mul_div_comm, mul_comm d, div_self (mul_ne_zero hv2 hd0.ne')]
    simp
  have key := average_eq_zero (UJ ε) (muG ε) (NW ε W) r Hr ν hνN hνinv hr
    (fun g => k * coefOn σ v v g) (coefOn σ a v)
    (continuous_const.mul hcvv) (hivv.const_mul k) hcav hiav
    (by
      intro z
      simp only [conv] at hconvvv ⊢
      have := hconvvv z
      simp only [mul_assoc]
      rw [show (fun g => k * (coefOn σ v v g * (k * coefOn σ v v (g⁻¹ * z))))
          = fun g => (k * k) * (coefOn σ v v g * coefOn σ v v (g⁻¹ * z)) by
            funext g; ring]
      rw [MeasureTheory.integral_const_mul, this]
      linear_combination (k * coefOn σ v v z) * hkc)
    (by
      intro z
      simp only [conv] at hconvav ⊢
      have := hconvav z
      simp only [mul_assoc]
      rw [MeasureTheory.integral_const_mul, this]
      linear_combination (coefOn σ a v z) * hkc)
    x (hcontav S ν (by rw [hS]; exact ⟨hν0, hνf, hνN, hνinv⟩) x) y
  exact key
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace UpperTheory.Lit.Cusp

open GlobalTheory.FibreAtTau

theorem decays_of_decayAt {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (v a : M.H τ)
    (h : DecayAt M τ v a (2 * V.rank ^ 2 + 1)) : Decays (Formalism.MainNotions.S.coefOn (ε := M.ε τ) (M.σ τ) a v) := by
  obtain ⟨C, hC⟩ := h
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  obtain ⟨-, hmul, -, -⟩ := isCompact_ball V.rank (M.ε τ)
  set c : ℝ := 1 + Real.sqrt (Formalism.REAL.hs (M.fr τ)) * Real.sqrt (Formalism.REAL.hs (M.fr τ)⁻¹) with hc
  refine ⟨c ^ (2 * V.rank ^ 2 + 1) * C, fun u => ?_⟩
  set g := (M.fr τ)⁻¹ * Formalism.MainNotions.S.umat u * M.fr τ with hg
  have hu : M.fr τ * g * (M.fr τ)⁻¹ = Formalism.MainNotions.S.umat u := by
    rw [hg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ hd]
  have hJ : (Formalism.MainNotions.S.umat u)ᴴ * Formalism.REAL.Jm (M.ε τ) * Formalism.MainNotions.S.umat u = Formalism.REAL.Jm (M.ε τ) := u.2
  have hfg : M.fr τ * g = Formalism.MainNotions.S.umat u * M.fr τ := by
    rw [hg, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  have hmem : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
    show gᴴ * gramAt D V τ * g = gramAt D V τ
    rw [← M.fr_gram τ]
    calc gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g
        = (M.fr τ * g)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * g) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (M.fr τ)ᴴ * ((Formalism.MainNotions.S.umat u)ᴴ * Formalism.REAL.Jm (M.ε τ) * Formalism.MainNotions.S.umat u) * M.fr τ := by
          rw [hfg]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hJ]
  have h1 := hC g hmem
  have he : M.rep τ g = M.σ τ (Formalism.MainNotions.S.umat u) := by rw [DSModel.rep, hu]
  rw [he] at h1
  have hn : Real.sqrt (Formalism.REAL.hs (Formalism.MainNotions.S.umat u)) ≤
      Real.sqrt (Formalism.REAL.hs (M.fr τ)) * hsn g * Real.sqrt (Formalism.REAL.hs (M.fr τ)⁻¹) := by
    rw [← hu]
    exact (hmul _ _).trans (mul_le_mul_of_nonneg_right (hmul _ _) (Real.sqrt_nonneg _))
  have h0 : 0 ≤ hsn g := Real.sqrt_nonneg _
  have hp : 0 ≤ Real.sqrt (Formalism.REAL.hs (M.fr τ)) * Real.sqrt (Formalism.REAL.hs (M.fr τ)⁻¹) := by positivity
  have h2 : 1 + Real.sqrt (Formalism.REAL.hs (Formalism.MainNotions.S.umat u)) ≤ c * (1 + hsn g) := by rw [hc]; nlinarith
  have h3 : wt u ≤ c ^ (2 * V.rank ^ 2 + 1) * (1 + hsn g) ^ (2 * V.rank ^ 2 + 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2 _
  calc _ ≤ ‖⟪v, M.σ τ (Formalism.MainNotions.S.umat u) a⟫_ℂ‖ * (c ^ (2 * V.rank ^ 2 + 1) * (1 + hsn g) ^ (2 * V.rank ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ = c ^ (2 * V.rank ^ 2 + 1) * (‖⟪v, M.σ τ (Formalism.MainNotions.S.umat u) a⟫_ℂ‖ * (1 + hsn g) ^ (2 * V.rank ^ 2 + 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)

theorem fibre_integral_eq_zero : ∀ (D : D7) (θ : InfFam D), IsInfFam θ →
    ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (v a : ∀ τ, M.H τ), (∀ τ, DecayAt M τ (v τ) (v τ) (2 * V.rank ^ 2 + 1)) → (∀ τ, DecayAt M τ (v τ) (a τ) (2 * V.rank ^ 2 + 1)) →
    ∀ (τ : D.what₂.Tau) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C →
    ∃ P Q : Subgroup (NI V C), IsClosed (P : Set (NI V C)) ∧ IsClosed (Q : Set (NI V C)) ∧
      (∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) ∧ (∀ h, ∃ p ∈ P, ∃ q ∈ Q, h = p * q) ∧ (∀ h, h ∈ P → h ∈ Q → h = 1) ∧
      ∀ ν : Measure P, ν.IsHaarMeasure → ∀ q ∈ Q, ∀ x y : GA D V,
        ∫ p, coef θ M K v a (x * (((p : NI V C) * q : NI V C) : GA D V) * y) ∂ν = 0 := by
  intro D θ hθ V S M K v a hv ha τ r C hC
  refine ⟨atP θ V C τ, offP θ V C τ, (L_closed θ hθ V C τ).1, (L_closed θ hθ V C τ).2, (L_comm θ hθ V C τ).1,
    L_decomp θ hθ V C hC τ, (L_comm θ hθ V C τ).2, ?_⟩
  intro ν hν q hq x y
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : BorelSpace (Formalism.REAL.UJ (M.ε τ)) := ⟨rfl⟩
  obtain ⟨E, hE⟩ := L_hom θ hθ V S M τ
  obtain ⟨W, hW, hemb, hrange⟩ := L_emb θ hθ V S M τ C hC E hE
  obtain ⟨R, hR⟩ := L_factor θ hθ V S M K v a τ C q hq x y
  let ι : atP θ V C τ →* Formalism.REAL.UJ (M.ε τ) := E.comp ((NI V C).subtype.comp (atP θ V C τ).subtype)
  have hι : Topology.IsClosedEmbedding ι := hemb
  have hmap := isHaarSub_map_closedEmb ι hι ⊤ isClosed_univ ν (isHaarSub_top ν)
  have hr : (((⊤ : Subgroup (atP θ V C τ)).map ι : Subgroup _) : Set _) = GlobalTheory.Dec.NW (M.ε τ) W := by
    rw [← MonoidHom.range_eq_map, MonoidHom.coe_range]
    exact hrange
  rw [hr] at hmap
  have hsq : GlobalTheory.Dec.IsSqIntIrr (M.ε τ) (M.σ τ) := by
    have hDS := M.ds τ
    exact ⟨hDS.1, hDS.2.1, hDS.2.2.1, hDS.2.2.2.1, hDS.2.2.2.2.1⟩
  have h0 := integral_coef_eq_zero V.rank (M.ε τ) (M.H τ) (M.σ τ) hsq (v τ) (a τ)
    (decays_of_decayAt M τ _ _ (hv τ)) (decays_of_decayAt M τ _ _ (ha τ)) W hW (ν.map ι) hmap (E x) (E y)
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have key : ∀ p : atP θ V C τ, coef θ M K v a (x * (((p : NI V C) * q : NI V C) : GA D V) * y) =
      ⟪v τ, M.σ τ (Formalism.MainNotions.S.umat (E x * ι p * E y)) (a τ)⟫_ℂ * R := by
    intro p
    rw [hR p p.2]
    congr 2
    show M.σ τ (M.fr τ * _ * (M.fr τ)⁻¹) (a τ) = M.σ τ _ (a τ)
    congr 2
    change M.fr τ * _ * (M.fr τ)⁻¹ = Formalism.MainNotions.S.umat (E x) * Formalism.MainNotions.S.umat (E ((p : NI V C) : GA D V)) * Formalism.MainNotions.S.umat (E y)
    rw [hE, hE, hE]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  simp_rw [key]
  have hint := hι.measurableEmbedding.integral_map (μ := ν)
    (fun m => ⟪v τ, M.σ τ (Formalism.MainNotions.S.umat (E x * m * E y)) (a τ)⟫_ℂ)
  rw [integral_mul_const, ← hint, h0, zero_mul]

end UpperTheory.Lit.Cusp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace UpperTheory.Lit.Cusp

theorem poin_isCuspFun : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v : ∀ τ, M.H τ), KDecay M v → ∀ c : GA D V, Nonempty D.what₂.Tau → ∀ a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, IsCuspFun V (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) := by
  intro D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c hT a
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  intro r C hC μ 𝓕 hμ h𝓕 g
  haveI := i1; haveI := i2; haveI := i3; haveI := i4; haveI := i5; haveI := i7
  haveI : LocallyCompactSpace (NI V C) := (GlobalTheory.CuspDecay.Model.isClosed_NI V hC).locallyCompactSpace
  haveI : SecondCountableTopology (NI V C) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI := hμ
  set K := congLev D.sp.cm V.gram Λ 𝔪 with hK
  have hm : Measurable (coef θ M K v fun τ => (a τ : M.H τ)) := GlobalTheory.T.measurable_level_indicator_coefficient_test_function D θ hθ V S M Λ 𝔪 hΛ h𝔪 v _
  set f : GA D V → ℂ := fun y => coef θ M K v (fun τ => (a τ : M.H τ)) (c * y * g) with hf
  have hfm : ∀ γ : GA D V, Measurable fun h : NI V C => f (γ * (NI V C).subtype h) := fun γ =>
    hm.comp ((continuous_const.mul (continuous_const.mul continuous_subtype_val)).mul continuous_const).measurable
  obtain ⟨-, Kc, hKc, hcov⟩ := GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V r C ⟨hC.2.1, hC.2.2⟩
  have hcov' : ∀ h : NI V C, ∃ δ ∈ (GQ V).comap (NI V C).subtype, δ * h ∈ Kc := fun h => by
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov h
    exact ⟨γ⁻¹, Subgroup.inv_mem _ hγ, by simpa using hk⟩
  obtain ⟨B, hB⟩ := GlobalTheory.T.poincareSeries_partialSums_bounded_compact D θ hθ V S M Λ 𝔪 hΛ v hv hT c a ((fun h : NI V C => (h : GA D V) * g) '' Kc)
    (hKc.image (continuous_subtype_val.mul continuous_const))
  have hpt : ∀ h ∈ Kc, ∑' γ : GQ V, ‖f (γ * (NI V C).subtype h) * 1‖ₑ ≤ ENNReal.ofReal B := by
    intro h hh
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    have e : ∀ γ : GQ V, f (↑γ * (NI V C).subtype h) * 1 =
        coef θ M K v (fun τ => (a τ : M.H τ)) (c * (γ : GA D V) * ((h : GA D V) * g)) := fun γ => by
      simp only [hf, mul_one, Subgroup.coe_subtype, mul_assoc]
    simp only [e, ← ofReal_norm_eq_enorm]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hB _ ⟨h, hh, rfl⟩ s)
  have hfin : (∑' q : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V),
      ∫⁻ h, ‖f ((q.out : GQ V) * (NI V C).subtype h) * 1‖ₑ ∂μ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (GlobalTheory.T.lintegral_unfolding_le_of_translate_cover (GA D V) (NI V C) μ (NI V C).subtype Subtype.val_injective (GQ V) Kc hcov'
      (fun y => ‖f y * 1‖ₑ) (fun γ => ((hfm γ).mul_const 1).enorm))
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := B)) (hKc.measure_lt_top (μ := μ)).ne) ?_
    calc _ ≤ ∫⁻ _ in Kc, ENNReal.ofReal B ∂μ := setLIntegral_mono measurable_const hpt
      _ = ENNReal.ofReal B * μ Kc := setLIntegral_const _ _
  have hunf := GlobalTheory.T.integrableOn_and_hasSum_tsum_subgroup (GA D V) (NI V C) μ (NI V C).subtype Subtype.val_injective (GQ V) 𝓕 h𝓕 f (fun _ => 1)
    hfm measurable_const (fun _ _ _ => rfl) hfin
  have hzero : ∀ q : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V),
      ∫ h, f ((q.out : GQ V) * (NI V C).subtype h) * 1 ∂μ = 0 := by
    intro q
    obtain ⟨τ⟩ := hT
    obtain ⟨P, Q, hPc, hQc, hcomm, hgen, htriv, hvan⟩ := fibre_integral_eq_zero D θ hθ V S M K v (fun τ => (a τ : M.H τ))
      (fun τ => (hv τ).2 _ (hv τ).1) (fun τ => (hv τ).2 _ (a τ).2) τ r C hC
    have := GlobalTheory.T.integral_haar_eq_zero_of_fibre_integrals_eq_zero_alt (NI V C) μ hμ P Q hPc hQc hcomm hgen htriv
      (fun n => coef θ M K v (fun τ => (a τ : M.H τ)) ((c * (q.out : GQ V)) * (n : GA D V) * g))
      (fun ν hν q' hq' => hvan ν hν q' hq' _ g)
    simpa [hf, mul_assoc] using this
  have hsum0 : HasSum (fun q : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V) =>
      ∫ h, f ((q.out : GQ V) * (NI V C).subtype h) * 1 ∂μ) 0 := by
    simpa only [hzero] using (hasSum_zero : HasSum (fun _ : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V) => (0:ℂ)) 0)
  have h0 := hunf.2.unique hsum0
  rw [← h0]
  refine integral_congr_ae (.of_forall fun n => ?_)
  simp only [poin, hf, mul_one, Subgroup.coe_subtype, mul_assoc]

open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension

open Classical in

theorem exists_multT_eq_poin : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v : ∀ τ, M.H τ), KDecay M v → ∀ c : GA D V, Nonempty D.what₂.Tau → ∃ y ∈ MultT θ M (Lev.levA V (congLev D.sp.cm V.gram Λ 𝔪) : Set _) 1, ∀ a : M.Vec, (∀ τ, (a τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → y (PiTensorProduct.tprod ℂ a) = poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ := by
  intro hHC hCW hRD D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c hτ
  obtain ⟨haut, ⟨T₀, hT₀⟩, hKeq⟩ := GlobalTheory.T.coefficientPoincareSeries_isAutomorphic D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c
  have hder := GlobalTheory.T.poincareSeries_smooth_moderateGrowth_deriv hHC D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c
  have hcusp := poin_isCuspFun D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c hτ
  obtain ⟨vol⟩ := (GlobalTheory.Unf.VolExist.measures_exist D).1 V
  have hGK : IsGKMap θ M (Lev.levA V (congLev D.sp.cm V.gram Λ 𝔪) : Set _) 1 vol.μ vol.𝓕 T₀ := by
    refine ⟨fun u => ?_, fun u => ?_, fun u => ?_, fun u => ?_, fun u => ?_, fun u k hk g => ?_, ?_, ?_⟩
    · rw [hT₀]; exact (haut u).1
    · rw [hT₀]; exact (hder u).1
    · rw [hT₀]; exact hcusp u
    · rw [hT₀]
      have hr := GlobalTheory.Grow.rapidDec_of_unifModGrowth hRD hθ (haut u).1 (hder u).1 (hder u).2.1 (hcusp u)
      exact GlobalTheory.CuspDecay.memLp_of_bounded hr.continuous hr.bounded _ _ vol.haar vol.fund 2
    · rw [hT₀]; exact (hder u).2.1
    · rw [hT₀, (haut u).2.2.2 k hk g]; simp
    · intro τ k hk u w hw
      rw [hT₀, hT₀]
      have e : (fun τ' => ((Function.update u τ w τ' : kFin M τ') : M.H τ')) =
          Function.update (fun τ' => (u τ' : M.H τ')) τ (M.rep τ k (u τ)) := by
        funext τ'
        by_cases h : τ' = τ
        · subst h; simp [hw]
        · simp [Function.update_of_ne h]
      rw [e]
      exact hKeq _ τ k (maxCpt_subset M τ hk)
    · intro τ X hX u w hw
      rw [hT₀, hT₀]
      exact (hder u).2.2 τ X hX w hw
  obtain ⟨T, ⟨hTm, hTe⟩, -⟩ := (GlobalTheory.GKExtensionToSmoothVectors.gkExtension hHC hCW D).1 θ hθ V S M _ 1 vol.μ vol.𝓕 vol.haar vol.fund T₀ hGK
  refine ⟨PiTensorProduct.lift T, ?_, fun a ha => ?_⟩
  · rw [mem_multT, LinearEquiv.symm_apply_apply]
    exact Submodule.subset_span hTm
  · rw [PiTensorProduct.lift.tprod, hTe a (fun τ => ⟨a τ, ha τ⟩) (fun τ => rfl), hT₀]

end UpperTheory.Lit.Cusp

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace UpperTheory.Lit.Cusp

set_option maxHeartbeats 1000000 in
open GlobalTheory.SepPer.PerNe in

theorem exists_cusp_form_theta_period_ne_zero : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    GlobalTheory.Published.CuspRapidDecay → PackEx → DepthPays →
    Ev fun {D} _ {L} {sc} {G} W M => ∀ (M₀ : DSModel (Yc D 0) (parB (Ptw D) 0))
      (MP : DSModel (G.V (.core 0)) (Node.par D sc.cGap (.core 0))), ∀ t ∈ Rows L W.θ M₀, t ≠ 0 →
        ∃ y ∈ CoreForms G W.θ 0 MP, ∃ v w, per0 G M (y v) (t w) ≠ 0 := by
  intro hHC hCW hCRD hPE hDP
  obtain ⟨C, hC, hPack⟩ := hPE
  intro ε CF hCF
  obtain ⟨x₁, hx₁⟩ := hPack ε CF hCF
  obtain ⟨x₂, hx₂⟩ := hDP C hC ε CF hCF
  refine ⟨max x₁ x₂, ?_⟩
  intro D large₂ hε hx hSz T L μ0 hL G W M hM M₀ MP t ht ht0
  obtain ⟨p, hp⟩ := hx₁ D large₂ hε (le_trans (le_max_left _ _) hx) hSz T L μ0 hL G W M hM M₀ MP
  obtain ⟨s, hs0, hs1, hsLip, hsN1, hsN2⟩ := hx₂ D large₂ hε (le_trans (le_max_right _ _) hx) hSz T L μ0 hL G W M hM
  obtain ⟨hsdY, hsdV, hlam, hz0, hJ, hrY, hrV, hmY⟩ :=
    GlobalTheory.T.thetaRowGrid_bottom_selfDual_lattices D (offQ_of_sizeRows hSz) T L μ0 hL _ G W M hM

  have hθ : IsInfFam W.θ := W.θ_is
  have hmod : G.modul ≠ ⊥ := G.pl.modul_ne_bot _
  have hRow := (hM.row 0 (Nat.zero_le _)).haar_fund
  obtain ⟨v, hvμ, hv𝓕⟩ : ∃ v : GlobalTheory.Unf.Vol (Yc D 0), v.μ = M.ν (.grid 0 0) ∧ v.𝓕 = M.fd (.grid 0 0) :=
    ⟨⟨_, _, hRow.1, hRow.2⟩, rfl, rfl⟩
  obtain ⟨b, x, hb, hbx⟩ := GlobalTheory.T.exists_bound_multiplicity_value_exceeds_half hCRD D W.θ hθ (Yc D 0) (parB (Ptw D) 0) M₀ (levRow L : Set (GA D (Yc D 0))) v t ht ht0 p.w hp.1.ne
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb x)
  obtain ⟨hAutSm, hCusp, -⟩ := GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hCRD D (Yc D 0) _ M₀ W.θ hθ _ 1 t ht
    (PiTensorProduct.tprod ℂ p.w)
  have hLip := GlobalTheory.T.unipotentPeriod_value_lipschitz_realOneParameter hCRD D W.θ hθ (Yc D 0) (G.V (.core 0)) G.sp.dec0 _ _ M₀ MP p (loss D C large₂.sc.b) hp (levRow L : Set (GA D (Yc D 0))) 1 t ht b hb
  have hInv : ∀ k ∈ Lev.levA (Yc D 0) (congLev D.sp.cm (Yc D 0).gram (L.ΛY 0)
      (Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)})), ∀ y, t (PiTensorProduct.tprod ℂ p.w) (y * k) = t (PiTensorProduct.tprod ℂ p.w) y := by
    intro k hk y
    rw [multT_apply_mul_lev ht _ k hk y, Pi.one_apply, one_mul]
  have hLong : Long W.θ p.A (L.ΛY 0) x s := by
    by_contra hn
    have hg1 : 1 ≤ D.host.g 0 * D.host.g 1 := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
    have hm1 : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    have hr1 : 1 ≤ (Yc D 0).rank := by rw [hrY]; exact (odd_r D).pos
    have hmin : ∀ τ, min (Finset.univ.filter fun a => p.A.ε τ a = true).card
        (Finset.univ.filter fun a => p.A.ε τ a = false).card ≤ D.R.m := fun τ => min_le_of_right_le (hmY p.A τ)
    have h := GlobalTheory.T.norm_cuspForm_le_of_shortLine D W.θ hθ (Yc D 0) p.A (L.ΛY 0) hsdY (D.host.g 0 * D.host.g 1) D.R.m hg1 hm1 hr1 hmin (t (PiTensorProduct.tprod ℂ p.w))
      hAutSm.toIsAutFun hCusp hInv (Real.exp (loss D C large₂.sc.b) * b) (by positivity) hLip x s hs0 hs1 hn
    rw [hrY] at h
    have : ‖t (PiTensorProduct.tprod ℂ p.w) x‖ ≤ b / 2 := by
      refine h.trans ?_
      have := mul_le_mul_of_nonneg_left hsLip hb0
      nlinarith
    linarith
  rw [hlam] at hsdV hz0
  have hJ' : ∀ k ∈ GfC (Yc D 0), Lev.finE (G.V (.core 0)) (stabilizerEmbedding G.sp.dec0 k) ∈
      congLev D.sp.cm (G.V (.core 0)).gram (G.sp.dec0.lat (L.ΛY 0) fun _ => 1) G.modul → k ∈ (levRow L : Set (GA D (Yc D 0))) := by
    rw [← hlam]; exact hJ
  obtain ⟨c, hc⟩ := GlobalTheory.T.unipotentPeriod_adelic_clauses_of_real hCRD D W.θ hθ (Yc D 0) (G.V (.core 0)) G.sp.dec0 _ _ M₀ MP p (loss D C large₂.sc.b) hp
    (G.sp.dec0.lat (L.ΛY 0) fun _ => 1) G.modul hsdV hmod hz0 (levRow L : Set (GA D (Yc D 0))) hJ' t ht v.μ v.haar
  have hN1 : 2 * Real.exp (loss D C large₂.sc.b + (6 * ((G.V (.core 0)).rank : ℝ) + 9) * Fintype.card D.what₂.Tau) ≤
      s ^ Fintype.card D.what₂.Tau * Real.sqrt (Ideal.absNorm G.modul) := by
    rw [hrV]; push_cast; exact hsN1
  have hne := GlobalTheory.T.poincareSeries_pairing_ne_zero_of_large_level D W.θ hθ (Yc D 0) (G.V (.core 0)) G.sp.dec0 _ _ M₀ MP p (loss D C large₂.sc.b) hp.1 (L.ΛY 0) G.modul hsdY hmod v (t (PiTensorProduct.tprod ℂ p.w)) c b s
    x (GlobalTheory.Core.Mi.BotPin.isContAut_multT ht _) hb hbx hs0.le (by linarith) hLong hc hN1 hsN2
  have hKD : KDecay MP p.v₀ := fun τ => ⟨(hp.1.dec τ).1, fun a ha =>
    GlobalTheory.T.coefficientDecay_kFinite_second_vector hHC D _ _ MP τ (p.v₀ τ) _ (hp.1.dec τ).1 (hp.1.dec τ).2 a ha⟩
  obtain ⟨y, hy, hyv⟩ := exists_multT_eq_poin hHC hCW hCRD D W.θ hθ (G.V (.core 0)) _ MP (G.sp.dec0.lat (L.ΛY 0) fun _ => 1)
    G.modul hsdV hmod p.v₀ hKD (p.g₀⁻¹ * stabilizerEmbedding G.sp.dec0 x⁻¹) ⟨D.eTau.symm 1⟩
  obtain ⟨v₀', hv₀'⟩ : ∃ v₀' : MP.Vec, ∀ τ, (v₀' τ : MP.H τ) = p.v₀ τ :=
    ⟨fun τ => ⟨p.v₀ τ, GlobalTheory.Core.Mi.kFin_le_sm hHC MP τ (hp.1.dec τ).1⟩, fun _ => rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a' : MP.Vec, ∀ τ, (a' τ : MP.H τ) = MP.rep τ (cmp W.θ τ p.g₀) (v₀' τ) :=
    ⟨fun τ => ⟨MP.rep τ (cmp W.θ τ p.g₀) (v₀' τ),
      GlobalTheory.UnifEvery.rep_mem_sm MP τ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ _ p.g₀ τ) (v₀' τ).2⟩, fun _ => rfl⟩
  have hv₀f : (fun τ => (v₀' τ : MP.H τ)) = p.v₀ := funext hv₀'
  have hU := (mem_multT W.θ MP _ 1 y).1 hy
  have key := GlobalTheory.RealEquiv.mult_realElt D (G.V (.core 0)) _ W.θ MP _ 1 _ hU (fun τ => cmp W.θ τ p.g₀)
    (fun τ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ _ p.g₀ τ) v₀' a' ha'
  rw [← GlobalTheory.RealTransSm.eq_realElt hθ hp.1.real] at key
  have hyg : ∀ g, y (PiTensorProduct.tprod ℂ a') g =
      poin W.θ MP (congLev D.sp.cm (G.V (.core 0)).gram (G.sp.dec0.lat (L.ΛY 0) fun _ => 1) G.modul) (p.v W.θ)
        (stabilizerEmbedding G.sp.dec0 x⁻¹) (p.v W.θ) g := by
    intro g
    rw [apply_tprod_eq, key]
    show PiTensorProduct.lift.symm y v₀' (g * p.g₀) = _
    rw [← apply_tprod_eq, hyv v₀' (fun τ => (hv₀' τ).symm ▸ (hp.1.dec τ).1), hv₀f]
    exact GlobalTheory.T.coefficientPoincareSeries_move_real_point D W.θ hθ (G.V (.core 0)) _ MP _ p.v₀ p.g₀ hp.1.real _ g
  have hmem : y ∈ CoreForms G W.θ 0 MP := by
    show y ∈ MultT W.θ MP (Lev.levA (G.V (.core 0)) (G.levCong (.core 0)) : Set (GA D (G.V (.core 0)))) 1
    unfold GridData.levCong
    rw [hlam]
    exact hy
  have hper : per0 G M (y (PiTensorProduct.tprod ℂ a')) (t (PiTensorProduct.tprod ℂ p.w)) ≠ 0 := by
    unfold per0
    simp_rw [hyg]
    rw [hvμ, hv𝓕] at hne
    exact hne
  exact ⟨y, hmem, _, _, hper⟩

end UpperTheory.Lit.Cusp

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace UpperTheory.Lit.Branch

open GlobalTheory.PackLoc

theorem realInputE_transport : RealInputE → ∃ C : ℝ, 0 < C ∧
  ∀ (m k N : ℕ) (hk : m = k) (hN : N = k + 1) (e : Option (Fin k) ≃ Fin (k + 1)) (ε : Fin N → Bool) (lam : Fin N → ℝ)
    (ε' : Fin m → Bool) (mu : Fin m → ℝ) (B : ℝ),
    GlobalTheory.SepReal.Par e (fun i => ε (Fin.cast hN.symm i)) (fun i => lam (Fin.cast hN.symm i))
      (fun i => ε' (Fin.cast hk.symm i)) (fun i => mu (Fin.cast hk.symm i)) B →
    ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
      (π : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (σ : Matrix (Fin m) (Fin m) ℂ → (H' →L[ℂ] H')),
      Formalism.MainNotions.S.IsDS ε lam π → Formalism.MainNotions.S.IsDS ε' mu σ →
      ∃ (v₀ v : H) (g₀ : Matrix (Fin N) (Fin N) ℂ) (w' : H') (c : ℝ),
        Formalism.MainNotions.S.IsLowUnit ε lam π v₀ ∧ g₀ ∈ Formalism.MainNotions.S.UJset ε ∧ v = π g₀ v₀ ∧
        GlobalTheory.Ell.SmV (GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε)) π v ∧ GlobalTheory.Ell.SmV (GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε')) σ w' ∧
        ‖w'‖ = 1 ∧ 0 < c ∧
        (ε (((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) none) = true ∧ ∀ i, ε (((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) (some i)) = ε' i) ∧
        (∀ b : H', ∫ h, star ⟪v, π (GlobalTheory.PackLoc.embOpt ((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) (Formalism.MainNotions.S.umat h)) v⟫_ℂ *
            ⟪b, σ (Formalism.MainNotions.S.umat h) w'⟫_ℂ ∂(Formalism.REAL.muG ε') = (c : ℂ) * (⟪w', w'⟫_ℂ * ⟪b, w'⟫_ℂ)) ∧
        (∀ g ∈ Formalism.MainNotions.S.UJset ε,
          Integrable (fun h => ⟪v, π (g * GlobalTheory.PackLoc.embOpt ((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) (Formalism.MainNotions.S.umat h)) v⟫_ℂ)
            (Formalism.REAL.muG ε') ∧
          ∫ h, ‖⟪v, π (g * GlobalTheory.PackLoc.embOpt ((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ε') ≤
            c * GlobalTheory.SepReal.big C k B *
              Real.sqrt (∑ a, ‖g a (((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) none)‖ ^ 2) ^ (-(2 * (k : ℝ) + 7))) ∧
        (∀ X ∈ GlobalTheory.Ell.lieOf (Formalism.REAL.Jm ε'), GlobalTheory.SepReal.hsn X ≤ 1 →
          Integrable (fun h => ⟪GlobalTheory.Ell.dR π (GlobalTheory.PackLoc.embOptL ((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) X) v,
            π (GlobalTheory.PackLoc.embOpt ((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) (Formalism.MainNotions.S.umat h)) v⟫_ℂ) (Formalism.REAL.muG ε') ∧
          ∫ h, ‖⟪GlobalTheory.Ell.dR π (GlobalTheory.PackLoc.embOptL ((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) X) v,
            π (GlobalTheory.PackLoc.embOpt ((finCongr hk).optionCongr.trans (e.trans (finCongr hN.symm))) (Formalism.MainNotions.S.umat h)) v⟫_ℂ‖ ∂(Formalism.REAL.muG ε') ≤
            c * GlobalTheory.SepReal.big C k B) ∧
        ∃ A : ℝ, ∀ g ∈ Formalism.MainNotions.S.UJset ε, ‖⟪v, π g v⟫_ℂ‖ ≤ A * GlobalTheory.SepReal.hsn g ^ (-(20 * ((k : ℝ) + 1) ^ 2)) := by
  rintro ⟨C, hC, hF⟩
  refine ⟨C, hC, ?_⟩
  intro m k N hk hN e ε lam ε' mu B hP H H' _ _ _ _ π σ hπ hσ
  subst hk
  subst hN
  have he : ((finCongr (rfl : m = m)).optionCongr.trans (e.trans (finCongr (rfl : m + 1 = m + 1).symm))) = e := by
    ext x
    cases x <;> simp
  rw [he]
  have hP' : GlobalTheory.SepReal.Par e ε lam ε' mu B := hP
  obtain ⟨v₀, v, g₀, w', c, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    hF m e ε lam ε' mu B hP' H H' π σ hπ hσ
  exact ⟨v₀, v, g₀, w', c, h1, h2, h3, h4, h5, h6, h7, hP'.signs, h8, h9, h10, h11⟩

theorem act_of_eigen : ∀ (D : D7) (θ : InfFam D) (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (S S' : D.what₂.Tau → SPar) (M₀ : DSModel Y S')
  (MP : DSModel V S) (τ : D.what₂.Tau) (e : Option (Fin Y.rank) ≃ Fin V.rank) (v₀ v : MP.H τ)
  (g₀ : Matrix (Fin V.rank) (Fin V.rank) ℂ) (w' : (GlobalTheory.ConjDS.conjModel M₀).H τ) (c₁ lam : ℝ),
  (∀ u, GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)) =
    ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ) →
  (∀ u, M₀.rep τ (GlobalTheory.PackLoc.ptY M₀ τ u) = M₀.σ τ (Formalism.MainNotions.S.umat u)) →
  (∀ F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℂ, ∫ u, F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) ∂(Formalism.REAL.muG (M₀.ε τ)) =
    lam • ∫ h, F (Formalism.MainNotions.S.umat h) ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ))) →
  ‖w'‖ = 1 →
  (∀ b : (GlobalTheory.ConjDS.conjModel M₀).H τ, ∫ h, star ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ *
      ⟪b, (GlobalTheory.ConjDS.conjModel M₀).σ τ (Formalism.MainNotions.S.umat h) w'⟫_ℂ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)) =
    (c₁ : ℂ) * (⟪w', w'⟫_ℂ * ⟪b, w'⟫_ℂ)) →
  ∀ b : M₀.H τ, ∫ u, GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)) *
      ⟪b, M₀.rep τ (GlobalTheory.PackLoc.ptY M₀ τ u) (GlobalTheory.ConjDS.cj (M₀.H τ) w')⟫_ℂ ∂(Formalism.REAL.muG (M₀.ε τ)) =
    ((lam * c₁ : ℝ) : ℂ) * ⟪b, GlobalTheory.ConjDS.cj (M₀.H τ) w'⟫_ℂ := by
  intro D θ Y V d S S' M₀ MP τ e v₀ v g₀ w' c₁ lam h1 h2 hH hw ha b
  set b' : (GlobalTheory.ConjDS.conjModel M₀).H τ := (GlobalTheory.ConjDS.cj (M₀.H τ)).symm b with hb'
  have key : ∀ x : Matrix (Fin Y.rank) (Fin Y.rank) ℂ,
      ⟪b, M₀.σ τ (GlobalTheory.ConjDS.rv x) (GlobalTheory.ConjDS.cj (M₀.H τ) w')⟫_ℂ =
        star ⟪b', (GlobalTheory.ConjDS.conjModel M₀).σ τ x w'⟫_ℂ := by
    intro x
    exact (inner_conj_symm (𝕜 := ℂ) b (M₀.σ τ (GlobalTheory.ConjDS.rv x) (GlobalTheory.ConjDS.cj (M₀.H τ) w'))).symm
  let F : Matrix (Fin Y.rank) (Fin Y.rank) ℂ → ℂ := fun x => ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e x) v⟫_ℂ *
        ⟪b, M₀.σ τ (GlobalTheory.ConjDS.rv x) (GlobalTheory.ConjDS.cj (M₀.H τ) w')⟫_ℂ
  have e1 : ∀ u, GlobalTheory.PackLoc.mco MP τ g₀ v₀ (GlobalTheory.PackLoc.embAt θ d τ (GlobalTheory.PackLoc.ptY M₀ τ u)) *
      ⟪b, M₀.rep τ (GlobalTheory.PackLoc.ptY M₀ τ u) (GlobalTheory.ConjDS.cj (M₀.H τ) w')⟫_ℂ =
      F (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u)) := by
    intro u
    simp only [F, h1, h2, GlobalTheory.ConjDS.rv_rv]
  have e2 : ∀ h : Formalism.REAL.UJ ((GlobalTheory.ConjDS.conjModel M₀).ε τ), F (Formalism.MainNotions.S.umat h) =
      star (star ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ *
        ⟪b', (GlobalTheory.ConjDS.conjModel M₀).σ τ (Formalism.MainNotions.S.umat h) w'⟫_ℂ) := by
    intro h; simp only [F, key, star_mul, star_star, mul_comm]
  have hww : ⟪w', w'⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw]; simp
  have e4 : star ⟪b', w'⟫_ℂ = ⟪b, GlobalTheory.ConjDS.cj (M₀.H τ) w'⟫_ℂ :=
    inner_conj_symm (𝕜 := ℂ) b (GlobalTheory.ConjDS.cj (M₀.H τ) w')
  rw [integral_congr_ae (ae_of_all _ e1), hH F, integral_congr_ae (ae_of_all _ e2)]
  rw [show (∫ h : Formalism.REAL.UJ ((GlobalTheory.ConjDS.conjModel M₀).ε τ), star (star ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ *
        ⟪b', (GlobalTheory.ConjDS.conjModel M₀).σ τ (Formalism.MainNotions.S.umat h) w'⟫_ℂ) ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)))
      = star (∫ h : Formalism.REAL.UJ ((GlobalTheory.ConjDS.conjModel M₀).ε τ), star ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e (Formalism.MainNotions.S.umat h)) v⟫_ℂ *
        ⟪b', (GlobalTheory.ConjDS.conjModel M₀).σ τ (Formalism.MainNotions.S.umat h) w'⟫_ℂ ∂(Formalism.REAL.muG ((GlobalTheory.ConjDS.conjModel M₀).ε τ)))
      from integral_conj]
  rw [ha b', hww, one_mul, star_mul, e4]
  simp [Complex.real_smul]
  ring

theorem locOK_of_eigen : RealInputE → ∃ C : ℝ, 0 ≤ C ∧ Ev fun {D} _ _ {sc} {G} W _ => ∀ (M₀ : DSModel (Yc D 0) (parB (Ptw D) 0))
  (MP : DSModel (G.V (.core 0)) (Node.par D sc.cGap (.core 0))) (τ : D.what₂.Tau),
  ∃ (εA : Fin (Yc D 0).rank → Bool) (A : Matrix (Fin (Yc D 0).rank) (Fin (Yc D 0).rank) ℂ) (εB : Fin (G.V (.core 0)).rank → Bool)
    (B : Matrix (Fin (G.V (.core 0)).rank) (Fin (G.V (.core 0)).rank) ℂ) (v₀ : MP.H τ)
    (g₀ : Matrix (Fin (G.V (.core 0)).rank) (Fin (G.V (.core 0)).rank) ℂ) (w : M₀.H τ) (c : ℂ),
    GlobalTheory.PackLoc.LocOK W.θ G.sp.dec0 M₀ MP τ (6 * C * ((D.R.r : ℝ) + 1) ^ 4 * Real.log sc.b) εA A εB B v₀ g₀ w c := by
  intro hRI
  obtain ⟨C, hC, hT1⟩ := realInputE_transport hRI
  refine ⟨C, hC.le, ?_⟩
  intro ε0 CF hCF
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.T.branchingHypotheses_gridParameters_largeScale ε0 CF hCF
  refine ⟨x₀, fun D large₂ h1 h2 h3 T L μ0 hL G W M hM => ?_⟩
  have hP := hx₀ D large₂ h1 h2 h3 T L μ0 hL G W M hM
  intro M₀ MP τ
  have hY : (Yc D 0).rank = D.R.r := by
    have h := D.sp.Y_rank 0 (Nat.zero_le _)
    simpa [Yc, Ranks.rankY] using h
  have hN : (G.V (.core 0)).rank = D.R.r + 1 := by
    have h : (Yc D 0).rank + 1 = (G.V (.core 0)).rank := G.sp.dec0.rank
    omega
  obtain ⟨⟨e, hPar⟩, hlog, -⟩ := hP τ (fun i => MP.ε τ (Fin.cast hN.symm i)) (fun i => MP.lam τ (Fin.cast hN.symm i))
    (fun i => (GlobalTheory.ConjDS.conjModel M₀).ε τ (Fin.cast hY.symm i)) (fun i => (GlobalTheory.ConjDS.conjModel M₀).lam τ (Fin.cast hY.symm i))
    (isEnum_cast' hN.symm (MP.enum τ)) (isEnum_cast' hY.symm ((GlobalTheory.ConjDS.conjModel M₀).enum τ))
  obtain ⟨v₀, v, g₀', w', c₁, hlow, hg₀', hv, hsmv, hsmw, hw1, hc₁, ⟨hs0, hs1⟩, ha, hb, hc, A₀, hA₀⟩ :=
    hT1 (Yc D 0).rank D.R.r (G.V (.core 0)).rank hY hN e (MP.ε τ) (MP.lam τ) ((GlobalTheory.ConjDS.conjModel M₀).ε τ)
      ((GlobalTheory.ConjDS.conjModel M₀).lam τ) (large₂.sc.b ^ 2) hPar (MP.H τ) ((GlobalTheory.ConjDS.conjModel M₀).H τ) (MP.σ τ)
      ((GlobalTheory.ConjDS.conjModel M₀).σ τ) (MP.ds τ) ((GlobalTheory.ConjDS.conjModel M₀).ds τ)
  set e' : Option (Fin (Yc D 0).rank) ≃ Fin (G.V (.core 0)).rank :=
    (finCongr hY).optionCongr.trans (e.trans (finCongr hN.symm)) with he'
  obtain ⟨B, hBu, hBg, hBad, hBz, hBmem, hBemb⟩ := GlobalTheory.T.exists_signature_matrix_extension D W.θ W.θ_is (Yc D 0) (G.V (.core 0)) G.sp.dec0 τ
    ((GlobalTheory.ConjDS.conjModel M₀).ε τ) ((GlobalTheory.ConjDS.conjModel M₀).fr τ) (MP.ε τ) e'
    ((GlobalTheory.ConjDS.conjModel M₀).fr_unit τ) ((GlobalTheory.ConjDS.conjModel M₀).fr_gram τ) hs0 hs1
  obtain ⟨lam, hlam, hH⟩ := GlobalTheory.T.unitary_haar_coordinate_reversal_positive_multiple _ (M₀.ε τ)
  obtain ⟨hreal, hmco⟩ := GlobalTheory.T.translated_matrix_coefficient_in_adapted_frame D _ _ MP τ B g₀' v₀ hBu hBg hg₀'
  obtain ⟨hpt, hlieX⟩ := GlobalTheory.T.conjugate_model_frame_matrix_facts_at_place D W.θ W.θ_is (Yc D 0) _ M₀ τ
  have hAu := (GlobalTheory.ConjDS.conjModel M₀).fr_unit τ
  have hbig : GlobalTheory.SepReal.big C D.R.r (large₂.sc.b ^ 2) ≤ Real.exp (6 * C * ((D.R.r : ℝ) + 1) ^ 4 * Real.log large₂.sc.b) := by
    unfold GlobalTheory.SepReal.big
    apply Real.exp_le_exp.2
    have h := mul_le_mul_of_nonneg_left hlog (show 0 ≤ C * ((D.R.r : ℝ) + 1) ^ 4 by positivity)
    calc C * ((D.R.r : ℝ) + 1) ^ 4 * Real.log (8 * ((D.R.r : ℝ) + 1) * large₂.sc.b ^ 2)
        ≤ C * ((D.R.r : ℝ) + 1) ^ 4 * (6 * Real.log large₂.sc.b) := h
      _ = 6 * C * ((D.R.r : ℝ) + 1) ^ 4 * Real.log large₂.sc.b := by ring
  have hm0 : ∀ u, GlobalTheory.PackLoc.mco MP τ (B⁻¹ * g₀' * MP.fr τ) v₀ (GlobalTheory.PackLoc.embAt W.θ G.sp.dec0 τ (GlobalTheory.PackLoc.ptY M₀ τ u)) =
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e' (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ := fun u => by
    rw [hmco _ (hBmem _ (hpt u).1), hBemb _ (hpt u).1, (hpt u).2.1, ← hv]
  have hmg : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V (.core 0)) τ), ∀ u,
      GlobalTheory.PackLoc.mco MP τ (B⁻¹ * g₀' * MP.fr τ) v₀ (g * GlobalTheory.PackLoc.embAt W.θ G.sp.dec0 τ (GlobalTheory.PackLoc.ptY M₀ τ u)) =
      ⟪v, MP.σ τ (B * g * B⁻¹ * GlobalTheory.PackLoc.embOpt e' (GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ := by
    intro g hg u
    rw [hmco _ (UH_mul' hg (hBmem _ (hpt u).1)), conj_mul' hBu, hBemb _ (hpt u).1, (hpt u).2.1, ← hv]
  have hm1 : ∀ X ∈ lieAt (Yc D 0) τ, ∀ (s : ℝ) u,
      GlobalTheory.PackLoc.mco MP τ (B⁻¹ * g₀' * MP.fr τ) v₀
        (GlobalTheory.PackLoc.embAt W.θ G.sp.dec0 τ (cmp W.θ τ (oneP W.θ (Yc D 0) τ X s) * GlobalTheory.PackLoc.ptY M₀ τ u)) =
      ⟪v, MP.σ τ (GlobalTheory.PackLoc.embOpt e'
        (NormedSpace.exp (s • ((GlobalTheory.ConjDS.conjModel M₀).fr τ * X * ((GlobalTheory.ConjDS.conjModel M₀).fr τ)⁻¹)) *
          GlobalTheory.ConjDS.rv (Formalism.MainNotions.S.umat u))) v⟫_ℂ := by
    intro X hX s u
    have hmem := UH_mul' ((hlieX X hX).2 s).1 (hpt u).1
    rw [hmco _ (hBmem _ hmem), hBemb _ hmem, conj_mul' hAu, ((hlieX X hX).2 s).2, (hpt u).2.1, ← hv]
  have hK : lam * (c₁ * GlobalTheory.SepReal.big C D.R.r (large₂.sc.b ^ 2)) ≤
      Real.exp (6 * C * ((D.R.r : ℝ) + 1) ^ 4 * Real.log large₂.sc.b) * ‖((lam * c₁ : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hlam hc₁)]
    calc lam * (c₁ * GlobalTheory.SepReal.big C D.R.r (large₂.sc.b ^ 2)) = (lam * c₁) * GlobalTheory.SepReal.big C D.R.r (large₂.sc.b ^ 2) := by ring
      _ ≤ (lam * c₁) * Real.exp (6 * C * ((D.R.r : ℝ) + 1) ^ 4 * Real.log large₂.sc.b) :=
        mul_le_mul_of_nonneg_left hbig (mul_pos hlam hc₁).le
      _ = _ := by ring
  have hL := GlobalTheory.T.smooth_vector_matrixCoeff_integrable (Yc D 0).rank (G.V (.core 0)).rank e' (MP.ε τ) ((GlobalTheory.ConjDS.conjModel M₀).ε τ)
    (MP.H τ) (MP.σ τ) v (c₁ * GlobalTheory.SepReal.big C D.R.r (large₂.sc.b ^ 2)) (MP.ds τ).2.2.1 hs0 hs1 hsmv
    (fun g hg => (hb g hg).1) hc
  obtain ⟨Cd, hCd⟩ := GlobalTheory.T.matrix_coefficient_decay_in_frame_of_translate_decay D.R.r (G.V (.core 0)).rank hN (MP.ε τ) (MP.H τ) (MP.σ τ) v₀ g₀' (MP.fr τ)
    (gramAt D (G.V (.core 0)) τ) A₀ (MP.ds τ).2.2.1 hg₀' (MP.fr_unit τ) (MP.fr_gram τ)
    (fun g hg => by rw [← hv]; exact hA₀ g hg)
  refine ⟨(GlobalTheory.ConjDS.conjModel M₀).ε τ, (GlobalTheory.ConjDS.conjModel M₀).fr τ, MP.ε τ, B, v₀, B⁻¹ * g₀' * MP.fr τ,
    GlobalTheory.ConjDS.cj (M₀.H τ) w', ((lam * c₁ : ℝ) : ℂ), ?_⟩
  exact
    { unitA := hAu
      gramA := (GlobalTheory.ConjDS.conjModel M₀).fr_gram τ
      unitB := hBu
      gramB := hBg
      adapted := hBad
      real := hreal
      kfin := GlobalTheory.isKFin_of_mem_lowKSub _ _ _ _ _ _ hlow.2
      dec := ⟨Cd, hCd⟩
      sm := GlobalTheory.T.conj_smooth_vector_conjugate_model_mem_smooth D _ _ M₀ τ w' hsmw
      ne := by
        intro h
        have h' : ‖GlobalTheory.ConjDS.cj (M₀.H τ) w'‖ = 1 := (GlobalTheory.ConjDS.cj (M₀.H τ)).norm_map w' ▸ hw1
        rw [h, norm_zero] at h'
        exact zero_ne_one h'
      cne := Complex.ofReal_ne_zero.2 (mul_pos hlam hc₁).ne'
      act := act_of_eigen D W.θ _ _ G.sp.dec0 _ _ M₀ MP τ e' v₀ v (B⁻¹ * g₀' * MP.fr τ) w' c₁ lam
        hm0 (fun u => (hpt u).2.2) (fun F => (hH ℂ F).2) hw1 ha
      far := GlobalTheory.T.transversal_coefficient_decay_at_real_place D W.θ _ _ G.sp.dec0 _ _ M₀ MP τ e' v₀ v (B⁻¹ * g₀' * MP.fr τ) B c₁ lam
        _ _ D.R.r hBu hBg hBz hN hmg (fun F => (hH ℂ F).1) (fun F => (hH ℝ F).2) hc₁ hlam hbig hb
      lip := GlobalTheory.T.matrix_coefficient_lipschitz_at_real_place D W.θ _ _ G.sp.dec0 _ _ M₀ MP τ e' v₀ v (B⁻¹ * g₀' * MP.fr τ)
        ((GlobalTheory.ConjDS.conjModel M₀).fr τ) _ lam _ _ hm0 hm1 (fun X hX => (hlieX X hX).1) hL (fun F => hH ℝ F) hlam hK }

theorem packEx_of_eigen : RealInputE → PackEx := by
  intro hRI
  obtain ⟨C, hC, hloc⟩ := locOK_of_eigen hRI
  refine ⟨6 * C, by positivity, ?_⟩
  intro ε CF hCF
  obtain ⟨x₀, hx⟩ := hloc ε CF hCF
  refine ⟨x₀, ?_⟩
  intro D large₂ hε hx0 hS T L μ0 hL G W M hM M₀ MP
  have h := hx D large₂ hε hx0 hS T L μ0 hL G W M hM M₀ MP
  choose εA A εB B v₀ g₀ w c hOK using h
  obtain ⟨p, hp⟩ := GlobalTheory.T.realVectors_allPlaces_of_localData W.θ W.θ_is G.sp.dec0 M₀ MP _ εA A εB B v₀ g₀ w c hOK
  refine ⟨p, ?_⟩
  have e : loss D (6 * C) large₂.sc.b = Fintype.card D.what₂.Tau * (6 * C * ((D.R.r : ℝ) + 1) ^ 4 * Real.log large₂.sc.b) := by
    unfold loss; ring
  rw [e]
  exact hp

end UpperTheory.Lit.Branch

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace UpperTheory.Lit.Branch

theorem periodNe_of_eigen : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    GlobalTheory.Published.CuspRapidDecay → RealInputE → PeriodNe := by
  intro hHC hCW hCR hR
  have h0 := Cusp.exists_cusp_form_theta_period_ne_zero hHC hCW hCR (packEx_of_eigen hR) GlobalTheory.T.gridDepth_pays_every_loss
  intro ε CF hCF
  obtain ⟨x, hx⟩ := h0 ε CF hCF
  refine ⟨x, fun D large₂ e a b T L μ0 hL G W M hM M₀ MP t ht t0 w w0 => ?_⟩
  obtain ⟨y, hy, v, w', hp⟩ := hx D large₂ e a b T L μ0 hL G W M hM M₀ MP t ht t0
  obtain ⟨a', ha', hp'⟩ := GlobalTheory.PeriodNePf.exists_kf W M hM hCR hHC M₀ MP ht hy v w' hp w w0
  exact ⟨y, hy, a', ha', hp'⟩

end UpperTheory.Lit.Branch

end
end

section
namespace UpperTheory.Lit

theorem functionalsSeparate_of_input
    (P : GlobalTheory.FunPr.Hypotheses₂) (hHowe : GlobalTheory.Hk3.HoweUnram)
    (hSW : GlobalTheory.Published.SiegelWeilUnitaryConvergent)
    (realIn : Branch.RealInputE) :
    GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate := by
  have rowModels := GlobalTheory.T.level_models_of_functoriality P
  have rowStep := GlobalTheory.T.level_induction_from_pairs P (GlobalTheory.T.pair_existence_of_functoriality P) rowModels
  have rowTower := GlobalTheory.T.firstRowTower_multiplicitySpaces_of_arrow rowModels rowStep
  have conv := GlobalTheory.T.level_tower_convergence P rowTower
  have per := Branch.periodNe_of_eigen P.harishChandraModules P.casselmanWallach P.cuspRapidDecay realIn
  have onto := GlobalTheory.T.theta_surjective_definite_level P P.harishChandraFinite P.cuspRapidDecay P.discreteSeriesCover
    P.harishChandraModules P.casselmanWallach hHowe P.weilRepresentationUnitaryPair
    P.weilSiegelFormulaUnitary hSW P.doublingMethod P.unramifiedDoublingGL
  have weak := GlobalTheory.T.rowSeparation_by_realFunctionals_of_chain_steps GlobalTheory.T.largeScaleSizes_imply_gapConditions (GlobalTheory.T.basic_models_of_functoriality P) (GlobalTheory.T.level_tower_rapid_decay P rowTower) per onto
    (GlobalTheory.T.bessel_period_nonvanishing_ascent_of_depth_data GlobalTheory.T.dependence_fixed)
  exact separate_of_steps_gap P rowTower GlobalTheory.T.largeScaleSizes_imply_gapConditions GlobalTheory.T.goodRows_principalLevel_are_rows conv weak

end UpperTheory.Lit
end
