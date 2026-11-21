import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatC
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolumeStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterArchimedeanForm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanOrbitalIntegralHuaBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousBlkM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexCoordinatesExistAtInfinityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement

section
section
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Cont

theorem continuous_phaseM_X {W : Type} [Fintype W] {n M : ℕ}
    (J : W → Matrix (Fin M) (Fin M) ℂ) (B : W → Matrix (Fin n) (Fin n) ℂ) :
    Continuous (phaseM J B) := by
  unfold phaseM
  refine continuous_finset_sum _ fun w _ => Complex.continuous_re.comp ?_
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, gramC]
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun c _ => ?_
  refine continuous_const.mul ?_
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  have h1 : Continuous fun X : W → Fin n → Fin M → ℂ => X w c i := by fun_prop
  have h2 : Continuous fun X : W → Fin n → Fin M → ℂ => X w a j := by fun_prop
  first
    | exact ((Complex.continuous_conj.comp h1).mul continuous_const).mul (by fun_prop)
    | exact ((Complex.continuous_conj.comp h2).mul continuous_const).mul (by fun_prop)

theorem continuous_phaseM_b {W : Type} [Fintype W] {n M : ℕ}
    (J : W → Matrix (Fin M) (Fin M) ℂ) (X : W → Fin n → Fin M → ℂ) :
    Continuous fun b : W → hermC n =>
      phaseM J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)) X := by
  unfold phaseM
  refine continuous_finset_sum _ fun w _ => Complex.continuous_re.comp ?_
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun c _ => ?_
  refine Continuous.mul ?_ continuous_const
  have h0 : Continuous fun b : W → hermC n => (b w : Matrix (Fin n) (Fin n) ℂ) :=
    continuous_subtype_val.comp (continuous_apply w)
  have h1 : Continuous fun m : Matrix (Fin n) (Fin n) ℂ => m a c :=
    (continuous_apply c).comp (continuous_apply a)
  exact h1.comp h0

theorem integrable_comp {E : Type} [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [MeasurableSpace E] [BorelSpace E]
    (N : ℕ) (e : E ≃+ (Fin N → ℝ)) (he : Continuous e) (hes : Continuous e.symm)
    (f : SchwartzMap (Fin N → ℝ) ℂ) (μ : Measure E) [μ.IsAddHaarMeasure] :
    Integrable (fun X => f (e X)) μ := by
  haveI : (Measure.map e μ).IsAddHaarMeasure := e.isAddHaarMeasure_map μ he hes
  have hs := Measure.isAddLeftInvariant_eq_smul (Measure.map e μ)
    (volume : Measure (Fin N → ℝ))
  have hi : Integrable f (Measure.map e μ) := by
    rw [hs]
    exact (f.integrable (μ := volume)).smul_measure_nnreal
  exact hi.comp_measurable he.measurable

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Cont

theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.continuous_coreC_schwartz
    (W : Type) [Fintype W] (n M : ℕ) (J : W → Matrix (Fin M) (Fin M) ℂ)
    (N : ℕ) (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)) (he : Continuous e)
    (hes : Continuous e.symm) (f : SchwartzMap (Fin N → ℝ) ℂ)
    (μ : Measure (W → Fin n → Fin M → ℂ)) (hμ : μ.IsAddHaarMeasure) :
    Continuous (coreC J μ (fun X => f (e X))) := by
  have hint := Cont.integrable_comp N e he hes f μ
  have hg : Continuous fun X => f (e X) := f.continuous.comp he
  have hnorm : ∀ t : ℝ, ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))‖ = 1 := by
    intro t
    have : (2 * Real.pi * Complex.I * (t : ℂ)) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  unfold coreC
  refine continuous_of_dominated (bound := fun X => ‖f (e X)‖) ?_ ?_ hint.norm ?_
  · intro b
    refine Continuous.aestronglyMeasurable (hg.mul ?_)
    have := Cont.continuous_phaseM_X J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ))
    exact Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp this))
  · intro b
    refine Filter.Eventually.of_forall fun X => ?_
    rw [norm_mul, hnorm, mul_one]
  · refine Filter.Eventually.of_forall fun X => ?_
    exact continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp (Cont.continuous_phaseM_b J X))))
end

open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_orbital_integral_continuous : ∀ (W : Type) [Fintype W] (n M : ℕ) (J : W → Matrix (Fin M) (Fin M) ℂ)
  (N : ℕ) (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm →
  ∀ (f : SchwartzMap (Fin N → ℝ) ℂ) (μ : Measure (W → Fin n → Fin M → ℂ)), μ.IsAddHaarMeasure →
  Continuous (coreC J μ (fun X => f (e X))) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.continuous_coreC_schwartz
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

open MeasureTheory Matrix

theorem detW_eq_normSq_det_one_add_I_smul :
    ∀ (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian →
      detW b = Complex.normSq (Matrix.det (1 + Complex.I • b)) := by
  intro n b hb
  unfold detW
  have h1 : (1 + b * b : Matrix (Fin n) (Fin n) ℂ) = (1 + Complex.I • b) * (1 + Complex.I • b)ᴴ := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hb.eq,
      Complex.star_def, Complex.conj_I]
    simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_neg,
      Complex.I_mul_I, one_smul, neg_smul]
    abel
  rw [h1, Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end
end

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detW_eq_normSq_det_one_add_I : ∀ (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian →
    detW b = Complex.normSq (Matrix.det (1 + Complex.I • b)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.detW_eq_normSq_det_one_add_I_smul
end

section
section
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem det_one_add_sq_eq_prod_eigenvalues (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) :
    Matrix.det (1 + b * b) = ((∏ i, (1 + hb.eigenvalues i ^ 2) : ℝ) : ℂ) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hb.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun i => ((hb.eigenvalues i : ℝ) : ℂ)) with hD
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self hb.eigenvectorUnitary
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self hb.eigenvectorUnitary
  have hs : b = U * D * star U := by
    have := hb.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, hU, hD, Function.comp_def] using this
  have h1 : 1 + b * b = U * (1 + D * D) * star U := by
    rw [hs]
    calc 1 + U * D * star U * (U * D * star U)
        = U * star U + U * D * (star U * U) * D * star U := by
          rw [hUU']; simp only [Matrix.mul_assoc]
      _ = U * (1 + D * D) * star U := by
          rw [hUU]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
  have hdet : (star U).det * U.det = 1 := by
    rw [← Matrix.det_mul, hUU, Matrix.det_one]
  have h2 : 1 + D * D = Matrix.diagonal (fun i => (((1 + hb.eigenvalues i ^ 2 : ℝ)) : ℂ)) := by
    rw [hD, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one, Matrix.diagonal_add]
    congr 1
    ext i
    push_cast
    ring
  rw [h1, Matrix.det_mul, Matrix.det_mul, h2, Matrix.det_diagonal]
  push_cast
  calc U.det * (∏ i, (1 + ((hb.eigenvalues i : ℝ) : ℂ) ^ 2)) * (star U).det
      = ((star U).det * U.det) * ∏ i, (1 + ((hb.eigenvalues i : ℝ) : ℂ) ^ 2) := by ring
    _ = _ := by rw [hdet, one_mul]

theorem one_le_detW : ∀ (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → 1 ≤ detW b := by
  intro n b hb
  unfold detW
  rw [det_one_add_sq_eq_prod_eigenvalues n b hb, Complex.ofReal_re]
  have : ∀ i ∈ (Finset.univ : Finset (Fin n)), (1 : ℝ) ≤ 1 + hb.eigenvalues i ^ 2 := fun i _ => by
    nlinarith [sq_nonneg (hb.eigenvalues i)]
  calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) this

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_le_detW_of_isHermitian : ∀ (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian → 1 ≤ detW b := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.one_le_detW
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

open MeasureTheory Matrix

theorem one_add_I_blkM_eq {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) + Complex.I • blkM b u d =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (1 + Complex.I • b) (Complex.I • Matrix.replicateCol (Fin 1) u)
          (Complex.I • Matrix.replicateRow (Fin 1) (star u))
          (Matrix.of fun _ _ => 1 + Complex.I * (d : ℂ))) := by
  ext i j
  obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
  rcases i' with i' | i' <;> rcases j' with j' | j'
  · simp [blkM, Matrix.one_apply]
  · have h : ¬Fin.castAdd 1 i' = Fin.natAdd n j' := by
      rw [Fin.ext_iff]; simp; omega
    simp [blkM, Matrix.one_apply, h]
  · have h : ¬Fin.natAdd n i' = Fin.castAdd 1 j' := by
      rw [Fin.ext_iff]; simp; omega
    simp [blkM, Matrix.one_apply, h]
  · obtain rfl := Subsingleton.elim i' j'
    simp [blkM]

theorem det_one_add_I_blkM {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (d : ℝ) :
    Matrix.det (1 + Complex.I • blkM b ((1 + Complex.I • b) *ᵥ v) d) =
      Matrix.det (1 + Complex.I • b) *
        (1 + Complex.I * (d : ℂ) + star ((1 + Complex.I • b) *ᵥ v) ⬝ᵥ v) := by
  rw [one_add_I_blkM_eq, Matrix.det_reindex_self]
  set D : Matrix (Fin n) (Fin n) ℂ := 1 + Complex.I • b with hD
  set u : Fin n → ℂ := D *ᵥ v with hu
  have hcol : D * Matrix.replicateCol (Fin 1) v = Matrix.replicateCol (Fin 1) u := by
    ext i j
    simp [hu, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hmul :
      Matrix.fromBlocks D (Complex.I • Matrix.replicateCol (Fin 1) u)
          (Complex.I • Matrix.replicateRow (Fin 1) (star u))
          (Matrix.of fun _ _ => 1 + Complex.I * (d : ℂ)) *
        Matrix.fromBlocks 1 (-Complex.I • Matrix.replicateCol (Fin 1) v) 0
          (1 : Matrix (Fin 1) (Fin 1) ℂ) =
      Matrix.fromBlocks D 0 (Complex.I • Matrix.replicateRow (Fin 1) (star u))
        (Matrix.of fun _ _ => 1 + Complex.I * (d : ℂ) + star u ⬝ᵥ v) := by
    rw [Matrix.fromBlocks_multiply]
    congr 1
    · simp
    · simp [Matrix.mul_smul, hcol]
    · simp
    · ext i j
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      simp [Matrix.mul_apply, dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm]
      simp only [← mul_assoc, hI, neg_mul, one_mul, Finset.sum_neg_distrib, neg_neg]
      ring
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂] at hdet
  simpa using hdet

theorem quad_real {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (v : Fin n → ℂ) :
    ((star v ⬝ᵥ (b *ᵥ v)).re : ℂ) = star v ⬝ᵥ (b *ᵥ v) := by
  have h : star (star v ⬝ᵥ (b *ᵥ v)) = star v ⬝ᵥ (b *ᵥ v) := by
    rw [← Matrix.star_dotProduct, Matrix.star_mulVec, hb.eq, Matrix.dotProduct_mulVec]
  exact Complex.conj_eq_iff_re.1 h

theorem star_mulVec_dot {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian)
    (v : Fin n → ℂ) :
    star ((1 + Complex.I • b) *ᵥ v) ⬝ᵥ v =
      ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) - Complex.I * ((star v ⬝ᵥ (b *ᵥ v)).re : ℂ) := by
  rw [quad_real hb, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  have hH : (1 + Complex.I • b)ᴴ = 1 - Complex.I • b := by
    simp [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hb.eq, sub_eq_add_neg]
  rw [hH, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul]
  congr 1
  simp [dotProduct, Complex.normSq_eq_conj_mul_self]

theorem normSq_det_one_add_I_blkM (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian)
    (_hdet : Matrix.det (1 + Complex.I • b) ≠ 0) (v : Fin n → ℂ) (d : ℝ) :
    Complex.normSq (Matrix.det (1 + Complex.I • blkM b ((1 + Complex.I • b) *ᵥ v) d)) =
      Complex.normSq (Matrix.det (1 + Complex.I • b)) *
        ((1 + ∑ i, Complex.normSq (v i)) ^ 2 + (d - (star v ⬝ᵥ (b *ᵥ v)).re) ^ 2) := by
  rw [det_one_add_I_blkM, map_mul, star_mulVec_dot hb]
  congr 1
  set r : ℝ := ∑ i, Complex.normSq (v i)
  set m : ℝ := (star v ⬝ᵥ (b *ᵥ v)).re
  have : (1 + Complex.I * (d : ℂ) + ((r : ℂ) - Complex.I * (m : ℂ))) =
      (((1 + r : ℝ) : ℂ)) + (((d - m : ℝ) : ℂ)) * Complex.I := by
    push_cast; ring
  rw [this, Complex.normSq_add_mul_I]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end
end

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detW_block_matrix_formula : ∀ (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian →
    Matrix.det (1 + Complex.I • b) ≠ 0 → ∀ (v : Fin n → ℂ) (d : ℝ),
    Complex.normSq (Matrix.det (1 + Complex.I • blkM b ((1 + Complex.I • b) *ᵥ v) d)) =
      Complex.normSq (Matrix.det (1 + Complex.I • b)) *
        ((1 + ∑ i, Complex.normSq (v i)) ^ 2 + (d - (star v ⬝ᵥ (b *ᵥ v)).re) ^ 2) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.normSq_det_one_add_I_blkM
end

section
section
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem lintegral_sq_add_sq_rpow_neg :
    ∀ s : ℝ, 1 / 2 < s → ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ a : ℝ, 0 < a → ∀ m : ℝ,
    ∫⁻ d : ℝ, ENNReal.ofReal ((a ^ 2 + (d - m) ^ 2) ^ (-s)) = C * ENNReal.ofReal (a ^ (1 - 2 * s)) := by
  intro s hs
  have hint : Integrable (fun t : ℝ => (1 + t ^ 2) ^ (-s)) := by
    have h0 := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * s)
      (by simp; linarith)
    have e : -(2 * s) / 2 = -s := by ring
    simpa [Real.norm_eq_abs, sq_abs, e] using h0
  refine ⟨∫⁻ t, ENNReal.ofReal ((1 + t ^ 2) ^ (-s)), hint.lintegral_lt_top.ne, ?_⟩
  intro a ha m
  have hF : Measurable fun d : ℝ => ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s)) := by fun_prop
  rw [lintegral_sub_right_eq_self (fun d : ℝ => ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s))) m]
  have hpt : ∀ t : ℝ, ENNReal.ofReal ((a ^ 2 + (a * t) ^ 2) ^ (-s)) =
      ENNReal.ofReal (a ^ ((2 : ℕ) * -s : ℝ)) * ENNReal.ofReal ((1 + t ^ 2) ^ (-s)) := by
    intro t
    rw [← ENNReal.ofReal_mul (by positivity), show a ^ 2 + (a * t) ^ 2 = a ^ 2 * (1 + t ^ 2) by ring,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast a 2,
      ← Real.rpow_mul ha.le]
  have hpow : a ^ (1 - 2 * s) = a * a ^ ((2 : ℕ) * -s : ℝ) := by
    rw [show (1 - 2 * s) = 1 + ((2 : ℕ) * -s : ℝ) by push_cast; ring, Real.rpow_add ha,
      Real.rpow_one]
  calc ∫⁻ d, ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s))
      = ∫⁻ d, ENNReal.ofReal ((a ^ 2 + d ^ 2) ^ (-s))
          ∂(ENNReal.ofReal |a| • Measure.map (a * ·) volume) := by
        rw [Real.smul_map_volume_mul_left ha.ne']
    _ = ENNReal.ofReal |a| * ∫⁻ t, ENNReal.ofReal ((a ^ 2 + (a * t) ^ 2) ^ (-s)) := by
        rw [lintegral_smul_measure, lintegral_map hF (measurable_const_mul a), smul_eq_mul]
    _ = ENNReal.ofReal a * (ENNReal.ofReal (a ^ ((2 : ℕ) * -s : ℝ)) *
          ∫⁻ t, ENNReal.ofReal ((1 + t ^ 2) ^ (-s))) := by
        rw [abs_of_pos ha]
        simp_rw [hpt]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul ha.le, ← hpow, mul_comm]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_power_line_scaling : ∀ s : ℝ, 1 / 2 < s → ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ a : ℝ, 0 < a → ∀ m : ℝ,
    ∫⁻ d : ℝ, ENNReal.ofReal ((a ^ 2 + (d - m) ^ 2) ^ (-s)) = C * ENNReal.ofReal (a ^ (1 - 2 * s)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_sq_add_sq_rpow_neg
end

section
section
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem det_restrictScalars_toLin' {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det ((Matrix.toLin' D).restrictScalars ℝ) = Complex.normSq (Matrix.det D) := by
  rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]

theorem lintegral_eq_normSq_det_mul_lintegral_mulVec (n : ℕ) (D : Matrix (Fin n) (Fin n) ℂ)
    (hD : Matrix.det D ≠ 0) (g : (Fin n → ℂ) → ENNReal) (hg : Measurable g) :
    ∫⁻ u, g u = ENNReal.ofReal (Complex.normSq (Matrix.det D)) * ∫⁻ v, g (D *ᵥ v) := by
  set f : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) := (Matrix.toLin' D).restrictScalars ℝ with hf
  have hdet : LinearMap.det f = Complex.normSq (Matrix.det D) := det_restrictScalars_toLin' D
  have hpos : 0 < Complex.normSq (Matrix.det D) := Complex.normSq_pos.mpr hD
  have hne : LinearMap.det f ≠ 0 := by
    rw [hdet]
    exact hpos.ne'
  have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (Fin n → ℂ)) hne
  have hfm : Measurable f := f.continuous_of_finiteDimensional.measurable
  have key : ∫⁻ v, g (D *ᵥ v) = ENNReal.ofReal (Complex.normSq (Matrix.det D))⁻¹ * ∫⁻ u, g u := by
    have e : ∀ v, D *ᵥ v = f v := fun v => by simp [hf, Matrix.toLin'_apply]
    simp_rw [e]
    rw [← lintegral_map hg hfm, hmap, lintegral_smul_measure, hdet, abs_of_pos (inv_pos.mpr hpos), smul_eq_mul]
  rw [key, ← mul_assoc, ← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ hpos.ne', ENNReal.ofReal_one,
    one_mul]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_linear_change_variables_complex : ∀ (n : ℕ) (D : Matrix (Fin n) (Fin n) ℂ), Matrix.det D ≠ 0 →
    ∀ g : (Fin n → ℂ) → ENNReal, Measurable g →
    ∫⁻ u, g u = ENNReal.ofReal (Complex.normSq (Matrix.det D)) * ∫⁻ v, g (D *ᵥ v) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_eq_normSq_det_mul_lintegral_mulVec
end

section
section
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem lintegral_one_add_normSq_rpow_ne_top :
    ∀ (n : ℕ) (t : ℝ), (n : ℝ) < t →
    ∫⁻ v : Fin n → ℂ, ENNReal.ofReal ((1 + ∑ i, Complex.normSq (v i)) ^ (-t)) ≠ ⊤ := by
  intro n t ht
  have ht0 : 0 < t := lt_of_le_of_lt n.cast_nonneg ht
  have hdim : (Module.finrank ℝ (Fin n → ℂ) : ℝ) < 2 * t := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
    linarith
  have hint := integrable_rpow_neg_one_add_norm_sq (E := Fin n → ℂ) (μ := volume) hdim
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun v => ?_) hint.lintegral_lt_top)
  apply ENNReal.ofReal_le_ofReal

  have hS0 : 0 ≤ ∑ i, Complex.normSq (v i) := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hnorm : ‖v‖ ≤ Real.sqrt (∑ i, Complex.normSq (v i)) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    have h1 : ‖v i‖ ^ 2 ≤ ∑ j, Complex.normSq (v j) := by
      rw [← Complex.normSq_eq_norm_sq]
      exact Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j)) (Finset.mem_univ i)
    simpa [abs_of_nonneg (norm_nonneg _)] using Real.abs_le_sqrt h1
  have hab : 1 + ‖v‖ ^ 2 ≤ 1 + ∑ i, Complex.normSq (v i) := by
    have h2 := pow_le_pow_left₀ (norm_nonneg v) hnorm 2
    rw [Real.sq_sqrt hS0] at h2
    linarith
  have ha : 0 < 1 + ‖v‖ ^ 2 := by positivity
  rw [show -(2 * t) / 2 = -t by ring, Real.rpow_neg (by linarith), Real.rpow_neg ha.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos ha t) (Real.rpow_le_rpow ha.le hab ht0.le)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_complex_power_finite : ∀ (n : ℕ) (t : ℝ), (n : ℝ) < t →
    ∫⁻ v : Fin n → ℂ, ENNReal.ofReal ((1 + ∑ i, Complex.normSq (v i)) ^ (-t)) ≠ ⊤ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_one_add_normSq_rpow_ne_top
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

theorem blkM_castSucc_castSucc {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ)
    (i j : Fin n) : blkM b u d i.castSucc j.castSucc = b i j := by
  have h : ∀ k : Fin n, finSumFinEquiv.symm k.castSucc = (Sum.inl k : Fin n ⊕ Fin 1) :=
    fun k => finSumFinEquiv_symm_apply_castAdd k
  simp [blkM, Matrix.reindex_apply, Matrix.submatrix_apply, h]

theorem blkM_castSucc_last {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ)
    (i : Fin n) : blkM b u d i.castSucc (Fin.last n) = u i := by
  have h : ∀ k : Fin n, finSumFinEquiv.symm k.castSucc = (Sum.inl k : Fin n ⊕ Fin 1) :=
    fun k => finSumFinEquiv_symm_apply_castAdd k
  simp [blkM, Matrix.reindex_apply, Matrix.submatrix_apply, h, finSumFinEquiv_symm_last]

theorem blkM_last_last {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ) :
    blkM b u d (Fin.last n) (Fin.last n) = d := by
  simp [blkM, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_last]

theorem blkM_last_castSucc {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ)
    (j : Fin n) : blkM b u d (Fin.last n) j.castSucc = star (u j) := by
  have h : ∀ k : Fin n, finSumFinEquiv.symm k.castSucc = (Sum.inl k : Fin n ⊕ Fin 1) :=
    fun k => finSumFinEquiv_symm_apply_castAdd k
  simp [blkM, Matrix.reindex_apply, Matrix.submatrix_apply, h, finSumFinEquiv_symm_last]

theorem blkM_add {n : ℕ} (b b' : Matrix (Fin n) (Fin n) ℂ) (u u' : Fin n → ℂ) (d d' : ℝ) :
    blkM (b + b') (u + u') (d + d') = blkM b u d + blkM b' u' d' := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [blkM_last_last]
    | cast j => simp [blkM_last_castSucc]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [blkM_castSucc_last]
    | cast j => simp [blkM_castSucc_castSucc]

def upperLeftHermBlock {n : ℕ} (b : hermC (n + 1)) : hermC n :=
  ⟨(b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).submatrix Fin.castSucc Fin.castSucc,
    mem_hermC.2 ((mem_hermC.1 b.2).submatrix _)⟩

def blkEquiv (n : ℕ) : (hermC n × (Fin n → ℂ) × ℝ) ≃+ hermC (n + 1) where
  toFun x := blk x.1 x.2.1 x.2.2
  invFun b := (upperLeftHermBlock b, fun i => (b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) i.castSucc (Fin.last n),
    ((b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Fin.last n) (Fin.last n)).re)
  left_inv x := by
    obtain ⟨b, u, d⟩ := x
    refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ ?_)
    · ext i j
      simp [upperLeftHermBlock, blk, blkM_castSucc_castSucc]
    · ext i
      simp [blk, blkM_castSucc_last]
    · simp [blk, blkM_last_last]
  right_inv b := by
    have hb := mem_hermC.1 b.2
    apply Subtype.ext
    ext i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last =>
        simp only [blk, blkM_last_last]
        have := hb.apply (Fin.last n) (Fin.last n)
        exact (Complex.conj_eq_iff_real.1 this).choose_spec ▸ by simp
      | cast j =>
        simp only [blk, blkM_last_castSucc]
        exact hb.apply _ _
    | cast i =>
      induction j using Fin.lastCases with
      | last => simp [blk, blkM_castSucc_last]
      | cast j => simp [blk, blkM_castSucc_castSucc, upperLeftHermBlock]
  map_add' x y := by
    apply Subtype.ext
    simp [blk, blkM_add]

theorem continuous_blkEquiv (n : ℕ) : Continuous (blkEquiv n) := by
  refine Continuous.subtype_mk (f := fun x : hermC n × (Fin n → ℂ) × ℝ =>
    blkM (x.1 : Matrix (Fin n) (Fin n) ℂ) x.2.1 x.2.2) ?_ _
  exact continuous_blkM.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem continuous_blkEquiv_symm (n : ℕ) : Continuous (blkEquiv n).symm := by
  have h : ∀ i j : Fin (n + 1), Continuous fun b : hermC (n + 1) =>
      (b : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) i j := fun i j =>
    (continuous_apply_apply i j).comp continuous_subtype_val
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
  · refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
    exact h _ _
  · exact continuous_pi fun i => h _ _
  · exact Complex.continuous_re.comp (h _ _)

theorem haar_blocks (n : ℕ) (ν : Measure (hermC (n + 1))) (ν' : Measure (hermC n))
    (hν : ν.IsAddHaarMeasure) (hν' : ν'.IsAddHaarMeasure) :
    ∃ c : ENNReal, c ≠ ⊤ ∧ ∀ F : hermC (n + 1) → ENNReal, Measurable F →
      ∫⁻ b, F b ∂ν = c * ∫⁻ b', ∫⁻ u : Fin n → ℂ, ∫⁻ d : ℝ, F (blk b' u d) ∂volume ∂volume ∂ν' := by
  haveI := hν
  haveI := hν'
  haveI : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hp : (ν'.prod ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hm : (Measure.map (blkEquiv n)
      (ν'.prod ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℝ)))).IsAddHaarMeasure :=
    (blkEquiv n).isAddHaarMeasure_map _ (continuous_blkEquiv n) (continuous_blkEquiv_symm n)
  have he : Measurable (blkEquiv n) := (continuous_blkEquiv n).measurable
  refine ⟨(Measure.addHaarScalarFactor ν (Measure.map (blkEquiv n)
      (ν'.prod ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℝ)))) : ENNReal),
    ENNReal.coe_ne_top, fun F hF => ?_⟩
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul ν (Measure.map (blkEquiv n)
      (ν'.prod ((volume : Measure (Fin n → ℂ)).prod (volume : Measure ℝ))))]
  rw [lintegral_smul_measure, lintegral_map hF he, lintegral_prod (fun a => F (blkEquiv n a)) (hF.comp he).aemeasurable]
  simp only [ENNReal.smul_def, smul_eq_mul]
  congr 1
  refine lintegral_congr fun b' => ?_
  rw [lintegral_prod]
  · rfl
  · exact ((hF.comp he).comp measurable_prodMk_left).aemeasurable

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end
end

open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_haar_block_decomposition : ∀ (n : ℕ) (ν : Measure (hermC (n + 1))) (ν' : Measure (hermC n)),
    ν.IsAddHaarMeasure → ν'.IsAddHaarMeasure →
    ∃ c : ENNReal, c ≠ ⊤ ∧ ∀ F : hermC (n + 1) → ENNReal, Measurable F →
      ∫⁻ b, F b ∂ν = c * ∫⁻ b', ∫⁻ u : Fin n → ℂ, ∫⁻ d : ℝ, F (blk b' u d) ∂volume ∂volume ∂ν' := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.haar_blocks
end

section
section
noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

theorem continuous_detW (n : ℕ) : Continuous (fun b : Matrix (Fin n) (Fin n) ℂ => detW b) := by
  unfold detW
  exact Complex.continuous_re.comp (Continuous.matrix_det (by fun_prop))

theorem measurable_term (n : ℕ) (s : ℝ) :
    Measurable (fun b : hermC n => ENNReal.ofReal (detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s))) := by
  have h : Continuous (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ)) :=
    (continuous_detW n).comp continuous_subtype_val
  exact (h.measurable.pow_const _).ennreal_ofReal

theorem inner_eq (n : ℕ) (s : ℝ) (hs : (n : ℝ) + 1 / 2 < s) : ∃ K : ENNReal, K ≠ ⊤ ∧
    ∀ b' : hermC n, ∫⁻ u : Fin n → ℂ, ∫⁻ d : ℝ,
      ENNReal.ofReal (detW (blk b' u d : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s)) =
      K * ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-(s - 1))) := by
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨C, hC, hD⟩ := GlobalTheory.T.lintegral_power_line_scaling s (by linarith)
  have hL := GlobalTheory.T.lintegral_complex_power_finite n (2 * s - 1) (by linarith)
  set L := ∫⁻ v : Fin n → ℂ, ENNReal.ofReal ((1 + ∑ i, Complex.normSq (v i)) ^ (-(2 * s - 1))) with hLdef
  refine ⟨C * L, ENNReal.mul_ne_top hC hL, fun b' => ?_⟩
  have hB : (b' : Matrix (Fin n) (Fin n) ℂ).IsHermitian := mem_hermC.1 b'.2
  have hw1 := GlobalTheory.T.one_le_detW_of_isHermitian n _ hB
  have hwA := GlobalTheory.T.detW_eq_normSq_det_one_add_I n _ hB
  have hdet : Matrix.det (1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) ≠ 0 := by
    intro h0
    rw [h0] at hwA
    simp at hwA
    linarith
  have hgm : Measurable (fun u : Fin n → ℂ => ∫⁻ d : ℝ,
      ENNReal.ofReal (detW (blk b' u d : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s))) := by
    apply Measurable.lintegral_prod_right'
      (f := fun p : (Fin n → ℂ) × ℝ => ENNReal.ofReal (detW (blk b' p.1 p.2 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s)))
    have hc : Continuous (fun p : (Fin n → ℂ) × ℝ => detW (blk b' p.1 p.2 : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)) :=
      (continuous_detW _).comp (continuous_blkM.comp
        (by fun_prop : Continuous fun p : (Fin n → ℂ) × ℝ => ((b' : Matrix (Fin n) (Fin n) ℂ), p.1, p.2)))
    exact (hc.measurable.pow_const _).ennreal_ofReal
  rw [GlobalTheory.T.lintegral_linear_change_variables_complex n _ hdet _ hgm, ← hwA]
  have hv : ∀ v : Fin n → ℂ, ∫⁻ d : ℝ, ENNReal.ofReal (detW (blk b' ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s))
      = ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) *
        (C * ENNReal.ofReal ((1 + ∑ i, Complex.normSq (v i)) ^ (-(2 * s - 1)))) := by
    intro v
    have hr : 0 ≤ ∑ i, Complex.normSq (v i) := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
    have hterm : ∀ d : ℝ, ENNReal.ofReal (detW (blk b' ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s))
        = ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) *
          ENNReal.ofReal (((1 + ∑ i, Complex.normSq (v i)) ^ 2 +
            (d - (star v ⬝ᵥ ((b' : Matrix (Fin n) (Fin n) ℂ) *ᵥ v)).re) ^ 2) ^ (-s)) := by
      intro d
      have hh := mem_hermC.1 (blk b' ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d).2
      rw [GlobalTheory.T.detW_eq_normSq_det_one_add_I _ _ hh]
      have e : ((blk b' ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d : hermC (n+1)) : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
          = blkM (b' : Matrix (Fin n) (Fin n) ℂ) ((1 + Complex.I • (b' : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) d := rfl
      rw [e, GlobalTheory.T.detW_block_matrix_formula n _ hB hdet v d, ← hwA, Real.mul_rpow (by linarith) (by positivity),
        ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith) _)]
    simp only [hterm]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hD (1 + ∑ i, Complex.normSq (v i)) (by linarith)]
    congr 3
    ring_nf
  simp only [hv]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ hC]
  have e2 : ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-(s - 1)))
      = ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ)) *
        ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) := by
    rw [← ENNReal.ofReal_mul (by linarith)]
    congr 1
    rw [show -(s - 1) = 1 + -s by ring, Real.rpow_add (by linarith), Real.rpow_one]
  rw [e2]
  ring

theorem hua_integrable : ∀ (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s → ∀ ν : Measure (hermC n), ν.IsAddHaarMeasure →
    Integrable (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  intro n
  induction n with
  | zero =>
    intro s _ ν hν
    have : IsFiniteMeasure ν := by
      haveI : Finite (hermC 0) := by
        haveI : Subsingleton (Matrix (Fin 0) (Fin 0) ℂ) := inferInstance
        exact Finite.of_subsingleton
      haveI : CompactSpace (hermC 0) := Finite.compactSpace
      exact ⟨isCompact_univ.measure_lt_top⟩
    have h1 : ∀ b : hermC 0, detW (b : Matrix (Fin 0) (Fin 0) ℂ) ^ (-s) = 1 := by
      intro b
      simp [detW]
    simp only [h1]
    exact integrable_const _
  | succ n ih =>
    intro s hs ν hν
    have hs' : (n : ℝ) + 1 / 2 < s := by push_cast at hs; linarith
    have hpos : ∀ b : hermC (n + 1), 0 ≤ detW (b : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s) := fun b =>
      Real.rpow_nonneg (by linarith [GlobalTheory.T.one_le_detW_of_isHermitian _ _ (mem_hermC.1 b.2)]) _
    have hmeas := measurable_term (n + 1) s
    have hm2 : Measurable (fun b : hermC (n + 1) => detW (b : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s)) :=
      (((continuous_detW (n + 1)).comp continuous_subtype_val).measurable.pow_const _)
    refine ⟨hm2.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hpos)]
    obtain ⟨c, hc, hF⟩ := GlobalTheory.T.hermitian_haar_block_decomposition n ν (Measure.addHaar) hν inferInstance
    obtain ⟨K, hK, hI⟩ := inner_eq n s hs'
    rw [hF _ hmeas]
    simp only [hI]
    rw [lintegral_const_mul _ (measurable_term n (s - 1))]
    have h3 := ih (s - 1) (by linarith) Measure.addHaar inferInstance
    have hp3 : ∀ b : hermC n, 0 ≤ detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-(s - 1)) := fun b =>
      Real.rpow_nonneg (by linarith [GlobalTheory.T.one_le_detW_of_isHermitian _ _ (mem_hermC.1 b.2)]) _
    have h4 := (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hp3)).1 h3.2
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hc)
      (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hK) h4)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end
end

open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hua_determinant_integrable_of_lt : ∀ (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s → ∀ ν : Measure (hermC n), ν.IsAddHaarMeasure →
  Integrable (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.hua_integrable
end

section
section
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

theorem integrable_prod_detW_rpow : ∀ (W : Type) [Fintype W] (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s →
    ∀ ν : Measure (W → hermC n), ν.IsAddHaarMeasure →
    Integrable (fun b : W → hermC n => ∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  intro W _ n s hs ν hν
  let μ₀ : Measure (hermC n) := Measure.addHaar
  have hf : ∀ _w : W, Integrable (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) μ₀ :=
    fun _ => GlobalTheory.T.hua_determinant_integrable_of_lt n s hs μ₀ inferInstance
  have hpi := Integrable.fintype_prod (μ := fun _ : W => μ₀)
    (f := fun _ : W => fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) hf
  rw [Measure.isAddLeftInvariant_eq_smul ν (Measure.pi fun _ : W => μ₀)]
  exact hpi.smul_measure_nnreal

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
end

open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_hua_determinant_integrable : ∀ (W : Type) [Fintype W] (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s →
  ∀ ν : Measure (W → hermC n), ν.IsAddHaarMeasure →
  Integrable (fun b : W → hermC n => ∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_prod_detW_rpow
end

section
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.PhaseCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem half_trace_eq (σ : E →ₐ[F] E) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (τ : InfinitePlace F → (E →+* ℂ)) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (h : IsCoord σ e τ Θ)
    (he : ∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) (z : Ainf F ⊗[F] E) (w : InfinitePlace F) :
    e (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E) z) w = (Θ z w).re := by
  have h4 := h.2.2.2 z w
  have h5 : e (Algebra.trace (Ainf F) (Ainf F ⊗[F] E) z) w = 2 * (Θ z w).re := by
    have := congrArg Complex.re h4
    simp only [Complex.ofReal_re, Complex.add_re, Complex.conj_re] at this
    rw [this]; ring
  rw [map_mul, Pi.mul_apply, he, h5, map_div₀, map_one, map_ofNat]
  ring

def evC (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (w : InfinitePlace F) : Ainf F ⊗[F] E →+* ℂ :=
  (Pi.evalRingHom (fun _ : InfinitePlace F => ℂ) w).comp (Θ : Ainf F ⊗[F] E →+* (InfinitePlace F → ℂ))

theorem evC_apply (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (w : InfinitePlace F) (z : Ainf F ⊗[F] E) :
    evC Θ w z = Θ z w := rfl

theorem coord_gramR (σ : E →ₐ[F] E) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (τ : InfinitePlace F → (E →+* ℂ)) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (h : IsCoord σ e τ Θ)
    {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → Ainf F ⊗[F] E) (w : InfinitePlace F) :
    matC Θ (gramR (Ainf F) σ J X) w = gramC (J.map (τ w)) (tupC Θ X w) := by
  ext a c
  change evC Θ w (Formalism.UG.hform (sigR (Ainf F) σ) (JR (Ainf F) J) (X a) (X c)) = _
  simp only [Formalism.UG.hform, map_sum, map_mul, gramC, tupC, evC_apply, h.2.1, JR, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show inclR (Ainf F) (J i j) = (1 : Ainf F) ⊗ₜ[F] (J i j) from rfl, h.2.2.1]

theorem coord_trace_mul (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) {n : ℕ}
    (B G : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (w : InfinitePlace F) :
    Θ (Matrix.trace (B * G)) w = Matrix.trace (matC Θ B w * matC Θ G w) := by
  change evC Θ w _ = _
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul]
  rfl

theorem gramC_smul {n M : ℕ} (c : ℂ) (J : Matrix (Fin M) (Fin M) ℂ) (X : Fin n → Fin M → ℂ) :
    gramC (c • J) X = c • gramC J X := by
  ext a b
  simp only [gramC, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem psiInf_phase : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) →
  ∀ (a : F) (ψ : AddChar (AF F) ℂ),
  (∀ x : Ainf F, ψ (pairA F x 0) = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, ρ w a * e x w : ℝ) : ℂ))) →
  ∀ (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))
    (X : Fin n → Fin M → Ainf F ⊗[F] E),
  psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E)
      (Matrix.trace (B * gramR (Ainf F) σ J X))) =
    Complex.exp (2 * Real.pi * Complex.I * ((phaseM (fun w => ((ρ w a : ℝ) : ℂ) • J.map (τ w))
      (fun w => matC Θ B w) (tupC Θ X) : ℝ) : ℂ)) := by
  intro F E _ _ _ _ _ σ ρ e τ Θ h he a ψ hψ M n J B X
  change ψ (pairA F _ 0) = _
  rw [hψ]
  congr 3
  rw [phaseM]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [half_trace_eq σ ρ e τ Θ h he, coord_trace_mul, coord_gramR σ e τ Θ h, gramC_smul,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.PhaseCoord
end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_character_in_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) →
  ∀ (a : F) (ψ : AddChar (AF F) ℂ),
  (∀ x : Ainf F, ψ (pairA F x 0) = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, ρ w a * e x w : ℝ) : ℂ))) →
  ∀ (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))
    (X : Fin n → Fin M → Ainf F ⊗[F] E),
  psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E)
      (Matrix.trace (B * gramR (Ainf F) σ J X))) =
    Complex.exp (2 * Real.pi * Complex.I * ((phaseM (fun w => ((ρ w a : ℝ) : ℂ) • J.map (τ w))
      (fun w => matC Θ B w) (tupC Θ X) : ℝ) : ℂ)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.PhaseCoord.psiInf_phase
end

section
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HermCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def hermEquiv (σ : E →ₐ[F] E) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ))
    (hconj : ∀ z w, Θ (sigR (Ainf F) σ z) w = conj (Θ z w)) (n : ℕ) :
    HermR (Ainf F) σ n ≃+ (InfinitePlace F → hermC n) where
  toFun b w := ⟨matC Θ (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) w, by
    refine mem_hermC.2 ?_
    ext a c
    simp only [Matrix.conjTranspose_apply, matC, RCLike.star_def]
    rw [← hconj, b.2 a c]⟩
  invFun G := ⟨fun a c => Θ.symm fun w => (G w : Matrix (Fin n) (Fin n) ℂ) a c, by
    intro a c
    apply Θ.injective
    funext w
    have h : (G w : Matrix (Fin n) (Fin n) ℂ).IsHermitian := mem_hermC.1 (G w).2
    rw [hconj]
    simp only [RingEquiv.apply_symm_apply]
    have := congrFun (congrFun h a) c
    simpa [Matrix.conjTranspose_apply] using this⟩
  left_inv b := by
    apply Subtype.ext
    ext a c
    simp [matC]
  right_inv G := by
    funext w
    apply Subtype.ext
    ext a c
    simp [matC]
  map_add' b b' := by
    funext w
    apply Subtype.ext
    ext a c
    simp [matC]

theorem continuous_hermEquiv (σ : E →ₐ[F] E) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ))
    (hconj : ∀ z w, Θ (sigR (Ainf F) σ z) w = conj (Θ z w)) (hΘ : Continuous Θ) (n : ℕ) :
    Continuous (hermEquiv σ Θ hconj n) := by
  refine continuous_pi fun w => Continuous.subtype_mk ?_ _
  refine continuous_matrix fun a c => ?_
  have h1 : Continuous fun b : HermR (Ainf F) σ n =>
      (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) a c :=
    (continuous_id.matrix_elem a c).comp continuous_subtype_val
  exact (continuous_apply w).comp (hΘ.comp h1)

theorem continuous_hermEquiv_symm (σ : E →ₐ[F] E) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ))
    (hconj : ∀ z w, Θ (sigR (Ainf F) σ z) w = conj (Θ z w)) (hΘ : Continuous Θ.symm) (n : ℕ) :
    Continuous (hermEquiv σ Θ hconj n).symm := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_matrix fun a c => ?_
  refine hΘ.comp (continuous_pi fun w => ?_)
  have h1 : Continuous fun b : hermC n => (b : Matrix (Fin n) (Fin n) ℂ) a c :=
    (continuous_id.matrix_elem a c).comp continuous_subtype_val
  exact h1.comp (continuous_apply w)

theorem continuous_symm (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (hΘ : IsHomeomorph Θ) :
    Continuous Θ.symm := by
  have e : (Θ.symm : (InfinitePlace F → ℂ) → Ainf F ⊗[F] E) = (hΘ.homeomorph Θ).symm := by
    funext y
    apply (hΘ.homeomorph Θ).injective
    rw [Homeomorph.apply_symm_apply]
    exact Θ.apply_symm_apply y
  rw [e]
  exact (hΘ.homeomorph Θ).symm.continuous

theorem topAddGroup_tens (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (hΘ : IsHomeomorph Θ) :
    IsTopologicalAddGroup (Ainf F ⊗[F] E) := by
  have c1 : Continuous Θ := hΘ.continuous
  have c2 : Continuous Θ.symm := continuous_symm Θ hΘ
  refine { continuous_add := ?_, continuous_neg := ?_ }
  · have : (fun p : (Ainf F ⊗[F] E) × (Ainf F ⊗[F] E) => p.1 + p.2) =
        fun p => Θ.symm (Θ p.1 + Θ p.2) := by
      funext p; simp
    rw [this]
    exact c2.comp ((c1.comp continuous_fst).add (c1.comp continuous_snd))
  · have : (fun x : Ainf F ⊗[F] E => -x) = fun x => Θ.symm (-Θ x) := by
      funext x; simp
    rw [this]
    exact c2.comp c1.neg

theorem exists_hermEquiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  ∀ n : ℕ, ∃ Ψ : HermR (Ainf F) σ n ≃+ (InfinitePlace F → hermC n),
    (∀ b w, ((Ψ b w : hermC n) : Matrix (Fin n) (Fin n) ℂ) = matC Θ (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) w) ∧
    ∀ ν : Measure (HermR (Ainf F) σ n), ν.IsAddHaarMeasure →
      (ν.map Ψ).IsAddHaarMeasure ∧ ∀ G : (InfinitePlace F → hermC n) → ℂ, Integrable G (ν.map Ψ) → Integrable (fun b => G (Ψ b)) ν := by
  intro F E _ _ _ _ _ σ _ e τ Θ hc n
  obtain ⟨hΘ, hconj, -, -⟩ := hc
  have c1 : Continuous Θ := hΘ.continuous
  have c2 : Continuous Θ.symm := continuous_symm Θ hΘ
  haveI := topAddGroup_tens Θ hΘ
  haveI : BorelSpace (HermR (Ainf F) σ n) := ⟨rfl⟩
  have h1 := continuous_hermEquiv σ Θ hconj c1 n
  have h2 := continuous_hermEquiv_symm σ Θ hconj c2 n
  refine ⟨hermEquiv σ Θ hconj n, fun b w => rfl, fun ν hν => ⟨?_, fun G hG => ?_⟩⟩
  · exact AddEquiv.isAddHaarMeasure_map ν (hermEquiv σ Θ hconj n) h1 h2
  · exact hG.comp_measurable h1.measurable

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HermCoord
end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_archimedean_complex_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  ∀ n : ℕ, ∃ Ψ : HermR (Ainf F) σ n ≃+ (InfinitePlace F → hermC n),
    (∀ b w, ((Ψ b w : hermC n) : Matrix (Fin n) (Fin n) ℂ) = matC Θ (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) w) ∧
    ∀ ν : Measure (HermR (Ainf F) σ n), ν.IsAddHaarMeasure →
      (ν.map Ψ).IsAddHaarMeasure ∧ ∀ G : (InfinitePlace F → hermC n) → ℂ, Integrable G (ν.map Ψ) → Integrable (fun b => G (Ψ b)) ν := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HermCoord.exists_hermEquiv
end

section
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.TupHaar

theorem tup_coord_haar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  ∀ n M : ℕ, ∃ Φ : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (InfinitePlace F → Fin n → Fin M → ℂ),
    (∀ X, Φ X = tupC Θ X) ∧ Continuous Φ ∧ Continuous Φ.symm ∧
    ∀ μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E), μ.IsAddHaarMeasure →
      (μ.map Φ).IsAddHaarMeasure ∧ ∀ g : (InfinitePlace F → Fin n → Fin M → ℂ) → ℂ, ∫ X, g (Φ X) ∂μ = ∫ Y, g Y ∂(μ.map Φ) := by
  intro F E _ _ _ _ _ σ _ e τ Θ hco n M
  have hΘ : IsHomeomorph Θ := hco.1
  have hΘc : Continuous Θ := hΘ.continuous
  have hs : Continuous (Θ.symm : (InfinitePlace F → ℂ) → Ainf F ⊗[F] E) := by
    have h := (IsHomeomorph.homeomorph (⇑Θ) hΘ).symm.continuous
    convert h using 1
    funext y
    apply Θ.injective
    rw [RingEquiv.apply_symm_apply]
    exact ((IsHomeomorph.homeomorph (⇑Θ) hΘ).apply_symm_apply y).symm
  let Φ : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (InfinitePlace F → Fin n → Fin M → ℂ) :=
    { toFun := fun X w a i => Θ (X a i) w
      invFun := fun Y a i => Θ.symm (fun w => Y w a i)
      left_inv := fun X => by funext a i; simp
      right_inv := fun Y => by funext w a i; simp
      map_add' := fun X X' => by funext w a i; simp }
  have hc' : Continuous (fun (X : Fin n → Fin M → Ainf F ⊗[F] E) (w : InfinitePlace F) (a : Fin n)
      (i : Fin M) => Θ (X a i) w) := by fun_prop
  have hcs' : Continuous (fun (Y : InfinitePlace F → Fin n → Fin M → ℂ) (a : Fin n) (i : Fin M) =>
      Θ.symm (fun w => Y w a i)) := by fun_prop
  have hc : Continuous Φ := hc'
  have hcs : Continuous Φ.symm := hcs'
  refine ⟨Φ, fun X => rfl, hc, hcs, fun μ hμ => ?_⟩
  haveI := hμ
  refine ⟨AddEquiv.isAddHaarMeasure_map μ Φ hc hcs, fun g => ?_⟩
  let h : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ (InfinitePlace F → Fin n → Fin M → ℂ) :=
    ⟨Φ.toEquiv, hc, hcs⟩
  exact (h.measurableEmbedding.integral_map g).symm

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.TupHaar
end
end

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tuple_archimedean_complex_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  ∀ n M : ℕ, ∃ Φ : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (InfinitePlace F → Fin n → Fin M → ℂ),
    (∀ X, Φ X = tupC Θ X) ∧ Continuous Φ ∧ Continuous Φ.symm ∧
    ∀ μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E), μ.IsAddHaarMeasure →
      (μ.map Φ).IsAddHaarMeasure ∧ ∀ g : (InfinitePlace F → Fin n → Fin M → ℂ) → ℂ, ∫ X, g (Φ X) ∂μ = ∫ Y, g Y ∂(μ.map Φ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.TupHaar.tup_coord_haar
end

section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

theorem core_integrable {W : Type} [Fintype W] {n M : ℕ} (hnM : 2 * n < M) (J : W → Matrix (Fin M) (Fin M) ℂ)
    (hJ : ∀ w, (J w).IsHermitian) (hJd : ∀ w, (J w).det ≠ 0) {N : ℕ}
    (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)) (he : Continuous e) (hes : Continuous e.symm)
    (f : SchwartzMap (Fin N → ℝ) ℂ) (μ : Measure (W → Fin n → Fin M → ℂ)) (hμ : μ.IsAddHaarMeasure)
    (ν : Measure (W → hermC n)) (hν : ν.IsAddHaarMeasure) :
    Integrable (coreC J μ (fun X => f (e X))) ν := by
  obtain ⟨C, hC⟩ := GlobalTheory.T.archimedean_orbital_integral_hua_bound W n M J hJ hJd N e he hes f μ hμ
  have hcont := GlobalTheory.T.archimedean_orbital_integral_continuous W n M J N e he hes f μ hμ
  have hs : (n : ℝ) - 1 / 2 < (M : ℝ) / 2 := by
    have : (2 * n + 1 : ℝ) ≤ M := by exact_mod_cast hnM
    linarith
  have hint := (GlobalTheory.T.product_hua_determinant_integrable W n ((M : ℝ) / 2) hs ν hν).const_mul C
  refine hint.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun b => ?_)
  have := hC b
  simpa [neg_div] using this

theorem integrable_starLoc_inf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E), μ.IsAddHaarMeasure →
  ∀ ν : Measure (HermR (Ainf F) σ n), ν.IsAddHaarMeasure →
  ∀ P : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzArch P →
    Integrable (starLoc (Ainf F) σ J (psiInf F ψ) μ P) ν := by
  intro F E _ _ _ _ _ σ hcm M J hJ n hn ψ hψ μ hμ ν hν P hP
  obtain ⟨ρ, e, hρ, he, heρ, -, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hcm.1
  obtain ⟨a, ha, hinf, -, -, -⟩ := GlobalTheory.T.adelic_character_archimedean_form F hcm.1 ρ e hρ he heρ ψ hψ
  obtain ⟨τ, Θ, hΘ⟩ := GlobalTheory.T.complex_coordinates_exist_at_infinity F E σ hcm ρ e hρ he heρ
  obtain ⟨Ψ, hΨ, hΨν⟩ := GlobalTheory.T.hermitian_archimedean_complex_coordinates F E σ hcm e τ Θ hΘ n
  obtain ⟨Φ, hΦ, hΦc, hΦs, hΦμ⟩ := GlobalTheory.T.tuple_archimedean_complex_coordinates F E σ hcm e τ Θ hΘ n M
  obtain ⟨N, e₀, he₀, he₀s, f, hP⟩ := hP
  obtain ⟨hνH, hνI⟩ := hΨν ν hν
  obtain ⟨hμH, hμI⟩ := hΦμ μ hμ
  let Jc : InfinitePlace F → Matrix (Fin M) (Fin M) ℂ := fun w => ((ρ w a : ℝ) : ℂ) • J.map (τ w)
  have hρa : ∀ w, ((ρ w a : ℝ) : ℂ) ≠ 0 := fun w => by
    simpa using (map_ne_zero (ρ w)).2 ha
  have hJc : ∀ w, (Jc w).IsHermitian := fun w => by
    ext i j
    have h1 := hJ.1 i j
    have h2 := hcm.2.2.2 (τ w) (J j i)
    simp only [Jc, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul',
      Complex.star_def, Complex.conj_ofReal]
    rw [h1] at h2
    rw [h2]
    rfl
  have hJd : ∀ w, (Jc w).det ≠ 0 := fun w => by
    simp only [Jc, Matrix.det_smul]
    refine mul_ne_zero (pow_ne_zero _ (hρa w)) ?_
    have : (J.map (τ w)).det = τ w J.det := by
      simpa using (RingHom.map_det (τ w) J).symm
    rw [this]
    exact (map_ne_zero (τ w)).2 hJ.2
  let e₂ : (InfinitePlace F → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ) := Φ.symm.trans e₀
  have he₂ : Continuous e₂ := he₀.comp hΦs
  have he₂s : Continuous e₂.symm := hΦc.comp he₀s
  have hcore := core_integrable hn Jc hJc hJd e₂ he₂ he₂s f (μ.map Φ) hμH (ν.map Ψ) hνH
  have := hνI _ hcore
  refine this.congr (Filter.Eventually.of_forall fun b => ?_)
  show coreC Jc (μ.map Φ) (fun X => f (e₂ X)) (Ψ b) = starLoc (Ainf F) σ J (psiInf F ψ) μ P b
  rw [coreC, ← hμI]
  unfold starLoc
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  show f (e₂ (Φ X)) * _ = P X * _
  have hph := GlobalTheory.T.archimedean_character_in_coordinates F E σ ρ e τ Θ hΘ heρ a ψ hinf M n J (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) X
  rw [hph, hP X]
  have h1 : e₂ (Φ X) = e₀ X := by simp [e₂]
  have h2 : (fun w => ((Ψ b w : hermC n) : Matrix (Fin n) (Fin n) ℂ)) = fun w => matC Θ (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) w := funext (hΨ b)
  rw [h1, h2, hΦ X]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
end
