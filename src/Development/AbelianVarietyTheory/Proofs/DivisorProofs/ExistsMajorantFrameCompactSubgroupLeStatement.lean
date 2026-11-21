import Mathlib
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb

section
section
open Matrix

noncomputable section
namespace GlobalTheory.CompactAvg
open MeasureTheory

theorem exists_invariant_posDef_hermitian {n : ℕ} (H : Subgroup (GL (Fin n) ℂ))
    (hH : IsCompact (H : Set (GL (Fin n) ℂ))) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, P.IsHermitian ∧ (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧
      ∀ g ∈ H, (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * P * g = P := by
  classical
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hH
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  let μ : Measure H := Measure.haarMeasure ⊤
  haveI : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  let m : H → Matrix (Fin n) (Fin n) ℂ := fun g => (((g⁻¹ : H) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
  have hm : Continuous m := Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv)

  let f : H → (Fin n → Fin n → ℂ) := fun g => ((m g)ᴴ * m g : Matrix (Fin n) (Fin n) ℂ)
  have hf : Continuous f := hm.matrix_conjTranspose.matrix_mul hm
  have hfi : Integrable f μ := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let P₀ : Matrix (Fin n) (Fin n) ℂ := Matrix.of (∫ g, f g ∂μ)

  have hinv : ∀ h ∈ H, (h : Matrix (Fin n) (Fin n) ℂ)ᴴ * P₀ * h = P₀ := by
    intro h hh
    let M : Matrix (Fin n) (Fin n) ℂ := h
    let Lₗ : (Fin n → Fin n → ℂ) →ₗ[ℂ] (Fin n → Fin n → ℂ) :=
      { toFun := fun A => (Mᴴ * Matrix.of A * M : Matrix (Fin n) (Fin n) ℂ)
        map_add' := fun A B => by
          show Mᴴ * Matrix.of (A + B) * M = Mᴴ * Matrix.of A * M + Mᴴ * Matrix.of B * M
          rw [show Matrix.of (A + B) = Matrix.of A + Matrix.of B from rfl, Matrix.mul_add, Matrix.add_mul]
        map_smul' := fun c A => by
          show Mᴴ * Matrix.of (c • A) * M = c • (Mᴴ * Matrix.of A * M)
          rw [show Matrix.of (c • A) = c • Matrix.of A from rfl, Matrix.mul_smul, Matrix.smul_mul] }
    let L := LinearMap.toContinuousLinearMap Lₗ
    have e1 : L (∫ g, f g ∂μ) = ∫ g, L (f g) ∂μ := (ContinuousLinearMap.integral_comp_comm L hfi).symm
    have e2 : ∀ g : H, L (f g) = f ((⟨h, hh⟩ : H)⁻¹ * g) := by
      intro g
      have hq : m ((⟨h, hh⟩ : H)⁻¹ * g) = m g * M := by
        show (((((⟨h, hh⟩ : H)⁻¹ * g)⁻¹ : H) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = m g * M
        rw [_root_.mul_inv_rev, inv_inv]
        rfl
      show Mᴴ * ((m g)ᴴ * m g) * M = (m _)ᴴ * m _
      rw [hq, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    have e3 : ∫ g, f ((⟨h, hh⟩ : H)⁻¹ * g) ∂μ = ∫ g, f g ∂μ := integral_mul_left_eq_self f _
    show L (∫ g, f g ∂μ) = ∫ g, f g ∂μ
    rw [e1]; simp_rw [e2]; exact e3

  have hpos : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P₀ *ᵥ x).re := by
    intro x hx
    let ℓₗ : (Fin n → Fin n → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun A => star x ⬝ᵥ Matrix.of A *ᵥ x
        map_add' := fun A B => by
          show star x ⬝ᵥ Matrix.of (A + B) *ᵥ x = star x ⬝ᵥ Matrix.of A *ᵥ x + star x ⬝ᵥ Matrix.of B *ᵥ x
          rw [show Matrix.of (A + B) = Matrix.of A + Matrix.of B from rfl, Matrix.add_mulVec, dotProduct_add]
        map_smul' := fun c A => by
          show star x ⬝ᵥ Matrix.of (c • A) *ᵥ x = c • (star x ⬝ᵥ Matrix.of A *ᵥ x)
          rw [show Matrix.of (c • A) = c • Matrix.of A from rfl, Matrix.smul_mulVec, dotProduct_smul] }
    let ℓ := LinearMap.toContinuousLinearMap ℓₗ
    have e1 : ℓ (∫ g, f g ∂μ) = ∫ g, ℓ (f g) ∂μ := (ContinuousLinearMap.integral_comp_comm ℓ hfi).symm
    have hℓi : Integrable (fun g => ℓ (f g)) μ := ℓ.integrable_comp hfi
    have e2 : (star x ⬝ᵥ P₀ *ᵥ x).re = ∫ g, RCLike.re (ℓ (f g)) ∂μ := by
      rw [integral_re hℓi, ← e1]; rfl
    have e3 : ∀ g : H, RCLike.re (ℓ (f g)) = ∑ i, ‖(m g *ᵥ x) i‖ ^ 2 := by
      intro g
      show (star x ⬝ᵥ ((m g)ᴴ * m g) *ᵥ x).re = _
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
      simp only [dotProduct, Pi.star_apply, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [Complex.star_def, Complex.mul_re]
    have hnz : ∀ g : H, m g *ᵥ x ≠ 0 := by
      intro g h0
      have : (((g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) * m g) *ᵥ x = x := by
        simp [m]
      rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero] at this
      exact hx this.symm
    have e4 : ∀ g : H, 0 < ∑ i, ‖(m g *ᵥ x) i‖ ^ 2 := by
      intro g
      obtain ⟨i, hi⟩ := Function.ne_iff.1 (hnz g)
      have hi' : 0 < ‖(m g *ᵥ x) i‖ ^ 2 := by
        have : 0 < ‖(m g *ᵥ x) i‖ := norm_pos_iff.2 hi
        positivity
      exact lt_of_lt_of_le hi' (Finset.single_le_sum (f := fun i => ‖(m g *ᵥ x) i‖ ^ 2)
        (fun j _ => by positivity) (Finset.mem_univ i))
    rw [e2]
    simp_rw [e3]
    have hgi : Integrable (fun g : H => ∑ i, ‖(m g *ᵥ x) i‖ ^ 2) μ :=
      (continuous_finset_sum _ fun i _ =>
        ((continuous_apply i).comp (hm.matrix_mulVec continuous_const)).norm.pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [integral_pos_iff_support_of_nonneg (fun g => (e4 g).le) hgi]
    have hs : Function.support (fun g : H => ∑ i, ‖(m g *ᵥ x) i‖ ^ 2) = Set.univ :=
      Set.eq_univ_of_forall fun g => (e4 g).ne'
    rw [hs]
    exact isOpen_univ.measure_pos μ Set.univ_nonempty
  refine ⟨P₀ + P₀ᴴ, ?_, ?_, ?_⟩
  · simp [Matrix.IsHermitian, add_comm]
  · intro x hx
    have hc : star x ⬝ᵥ P₀ᴴ *ᵥ x = star (star x ⬝ᵥ P₀ *ᵥ x) := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, star_dotProduct]
    rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re, hc]
    have := hpos x hx
    simp only [Complex.star_def, Complex.conj_re]
    linarith
  · intro g hg
    have h1 := hinv g hg
    have h2 : (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * P₀ᴴ * g = P₀ᴴ := by
      conv_rhs => rw [← h1]
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [Matrix.mul_add, Matrix.add_mul, h1, h2]

end GlobalTheory.CompactAvg
end
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_posDef_hermitian_invariant_of_isCompact : ∀ {n : ℕ} (H : Subgroup (GL (Fin n) ℂ)), IsCompact (H : Set (GL (Fin n) ℂ)) →
    ∃ P : Matrix (Fin n) (Fin n) ℂ, P.IsHermitian ∧ (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧
      ∀ g ∈ H, (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * P * g = P := by
  atlas_forward_decl GlobalTheory.CompactAvg.exists_invariant_posDef_hermitian
end

section
noncomputable section

namespace GlobalTheory.ThK.SqIntMaxCpt

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped Matrix TensorProduct

theorem exists_congr_one {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.IsHermitian)
    (hpos : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) : ∃ Q : GL (Fin n) ℂ, Q.1ᴴ * P * Q.1 = 1 := by
  have hd : P.det ≠ 0 := fun h => by
    obtain ⟨x, hx, e⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    simpa [e] using hpos x hx
  obtain ⟨ε, Q, hQ⟩ := Frames.exists_congr_diagonal_sign hP hd
  refine ⟨Q, hQ.trans ?_⟩
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  have hx : Q.1 *ᵥ (Pi.single i 1 : Fin n → ℂ) ≠ 0 := fun h => by
    have := congrArg ((Q⁻¹).1 *ᵥ ·) h
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    simpa using congrFun this i
  have := hpos _ hx
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQ] at this
  cases h : ε i
  · simp [h, Matrix.mulVec_single_one, dotProduct, Pi.single_apply, Matrix.diagonal_apply] at this
    linarith
  · simp

theorem exists_unitary_sign {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (h2 : H * H = 1) :
    ∃ (ε : Fin n → Bool) (U : GL (Fin n) ℂ), U.1ᴴ * U.1 = 1 ∧
      U.1ᴴ * H * U.1 = Matrix.diagonal fun i => if ε i then 1 else -1 := by
  set U : Matrix (Fin n) (Fin n) ℂ := hH.eigenvectorUnitary.1 with hU
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hH.eigenvectorUnitary.2
  have h1' : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hH.eigenvectorUnitary.2
  have h3 : Uᴴ * H * U = Matrix.diagonal fun i => (hH.eigenvalues i : ℂ) := by
    have := hH.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def] using this
  have h4 : (Uᴴ * H * U) * (Uᴴ * H * U) = 1 := by
    calc _ = Uᴴ * (H * (U * Uᴴ) * H) * U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1', Matrix.mul_one, h2, Matrix.mul_one, h1]
  rw [h3, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one] at h4
  refine ⟨fun i => decide ((hH.eigenvalues i : ℂ) = 1), ⟨U, Uᴴ, h1', h1⟩, h1, h3.trans ?_⟩
  congr 1
  funext i
  have := congrFun (Matrix.diagonal_injective h4) i
  rcases mul_self_eq_one_iff.1 this with h | h
  · simp [h]
  · simp [h]

theorem exists_frame {n : ℕ} {M θ G : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) (hθ : IsCartan M θ) {s : ℝ} (hs : s ≠ 0)
    (hG : G = (s : ℂ) • M.map star) : ∃ (ε : Fin n → Bool) (Q : GL (Fin n) ℂ),
      Q.1ᴴ * G * Q.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) ∧
      ∀ k : Matrix (Fin n) (Fin n) ℂ, kᴴ * G * k = G → ((Q⁻¹).1 * k * Q.1)ᴴ * ((Q⁻¹).1 * k * Q.1) = 1 → Commute k θ := by
  obtain ⟨h1, h2, h3⟩ := hθ
  set N := M.map star with hN
  have hNh : Nᴴ = N := by
    ext i j
    simpa [hN] using congrArg star (congrFun (congrFun hM i) j)
  have h2' : θᴴ * N * θ = N := by
    have := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A.map (starRingEnd ℂ)) h2
    simp only [Matrix.map_mul] at this
    have e1 : θᵀ.map (starRingEnd ℂ) = θᴴ := by ext i j; simp
    have e2 : (θ.map star).map (starRingEnd ℂ) = θ := by ext i j; simp
    rw [e1, e2] at this
    exact this
  have h4 : θᴴ * N = N * θ := by
    conv_rhs => rw [← h2', Matrix.mul_assoc, h1, Matrix.mul_one]
  obtain ⟨e, he, hes⟩ : ∃ e : ℝ, e * e = 1 ∧ 0 < s * e := by
    rcases lt_or_gt_of_ne hs with h | h
    · exact ⟨-1, by norm_num, by linarith⟩
    · exact ⟨1, by norm_num, by linarith⟩
  have he' : (e : ℂ) * e = 1 := by exact_mod_cast he
  set T := (e : ℂ) • θ with hT
  have hTT : T * T = 1 := by rw [hT, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he', one_smul, h1]
  have hGT : G * T = ((s * e : ℝ) : ℂ) • (θᴴ * N) := by
    rw [hG, hT, h4, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.ofReal_mul]
  have hGh : Gᴴ = G := by rw [hG, Matrix.conjTranspose_smul, hNh]; simp
  have hP : (G * T).IsHermitian := by
    rw [Matrix.IsHermitian, hGT, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hNh,
      Matrix.conjTranspose_conjTranspose, ← h4]
    simp
  obtain ⟨Q₀, hQ₀⟩ := exists_congr_one hP fun x hx => by
    have e1 : star x ⬝ᵥ (θᴴ * N) *ᵥ x = star ((θ *ᵥ x) ⬝ᵥ M *ᵥ star x) := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
      simp [dotProduct, Matrix.mulVec, hN, mul_comm]
    rw [hGT, Matrix.smul_mulVec, dotProduct_smul, e1, smul_eq_mul, Complex.re_ofReal_mul]
    exact mul_pos hes (by simpa using h3 x hx)
  have h5 : Q₀.1ᴴ * G = (Q₀⁻¹).1 * T := by
    have := congrArg (· * (Q₀⁻¹).1 * T) hQ₀
    simpa only [Matrix.mul_assoc, Units.mul_inv_cancel_left, hTT, Matrix.mul_one, Matrix.one_mul] using this
  obtain ⟨ε, U, hU, hUH⟩ := exists_unitary_sign (H := Q₀.1ᴴ * G * Q₀.1)
    (Matrix.isHermitian_conjTranspose_mul_mul _ hGh) (by
      rw [h5]
      simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
      rw [← Matrix.mul_assoc T, hTT, Matrix.one_mul, Units.inv_mul])
  refine ⟨ε, Q₀ * U, by simpa [Matrix.mul_assoc] using hUH, fun k hk hu => ?_⟩
  set Q := Q₀ * U with hQ
  have hQP : Q.1ᴴ * (G * T) * Q.1 = 1 := by
    calc _ = U.1ᴴ * (Q₀.1ᴴ * (G * T) * Q₀.1) * U.1 := by simp [hQ, Matrix.mul_assoc]
      _ = 1 := by rw [hQ₀, Matrix.mul_one, hU]
  have hi : (Q⁻¹).1ᴴ * Q.1ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
  have hPe : G * T = (Q⁻¹).1ᴴ * (Q⁻¹).1 := by
    have := congrArg (fun A => (Q⁻¹).1ᴴ * A * (Q⁻¹).1) hQP
    simpa only [← Matrix.mul_assoc, hi, Matrix.one_mul, Matrix.mul_one, Units.mul_inv_cancel_right] using this
  have hkP : kᴴ * (G * T) * k = G * T := by
    have := congrArg (fun A => (Q⁻¹).1ᴴ * A * (Q⁻¹).1) hu
    rw [hPe]
    simpa only [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, hi, Matrix.one_mul, Matrix.mul_one,
      Units.mul_inv_cancel_right] using this
  have hL : (Q.1 * Q.1ᴴ) * G * T = 1 := by
    rw [Matrix.mul_assoc, hPe, Matrix.mul_assoc, ← Matrix.mul_assoc Q.1ᴴ, ← Matrix.conjTranspose_mul, Units.inv_mul,
      Matrix.conjTranspose_one, Matrix.one_mul, Units.mul_inv]
  have hGu : IsUnit G := by
    have : IsUnit (Q.1 * Q.1ᴴ * G) := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hL)
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at this
    exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right this)
  have hkG : IsUnit (kᴴ * G) := by
    rw [← hk, Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at hGu
    exact (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left hGu)
  have hc : k * T = T * k := hkG.mul_left_cancel (by
    rw [← Matrix.mul_assoc, hk, ← hkP]; simp only [Matrix.mul_assoc])
  have := congrArg ((e : ℂ) • ·) hc
  simpa only [hT, Matrix.mul_smul, Matrix.smul_mul, smul_smul, he', one_smul, Commute, SemiconjBy] using this

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_evI_of_compFin {z : AE F E} (h : ∀ v, compFin F E v z = 0) : At (evI F) z := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  refine GlobalTheory.Doubling.adele_ext (fun w => ?_) fun v => ?_
  · rw [Algebra.smul_def, map_mul, map_zero]
    refine mul_eq_zero_of_left ?_ _
    change evInf F w u ⊗ₜ[F] (1 : E) = 0
    rw [show evInf F w u = 0 from congrFun h1 w, TensorProduct.zero_tmul]
  · rw [Algebra.smul_def, map_mul, h, mul_zero, map_zero]

theorem exists_isMaxCpt_le_kInf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (d r s : ℕ) (W : Spc F E d), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∃ K, IsMaxCpt σ (c • W.J.map σ) K ∧ ∀ k ∈ K, (toGAd hσ W.J hc).symm k ∈ KInf σ W B.emb := by
  intro F E _ _ _ _ _ σ hσ B d r s W hB hW c hc hσc
  have h := hB.cm
  have hcj : ∀ (τ : E →+* ℂ) x, star (τ x) = τ (σ x) := fun τ x => (h.2.2.2 τ x).symm
  have key : ∀ w : InfinitePlace F, ∃ (ε : Fin d → Bool) (Q : GL (Fin d) ℂ),
      Q.1ᴴ * (c • W.J.map σ).map (B.emb w).1 * Q.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) ∧
      ∀ k : Matrix (Fin d) (Fin d) ℂ, kᴴ * (c • W.J.map σ).map (B.emb w).1 * k = (c • W.J.map σ).map (B.emb w).1 →
        ((Q⁻¹).1 * k * Q.1)ᴴ * ((Q⁻¹).1 * k * Q.1) = 1 → Commute k (W.θ w) := fun w => by
    have hre : ((B.emb w).1 c).re = 0 := by
      have := congrArg Complex.re (hcj (B.emb w).1 c)
      rw [hσc, map_neg] at this
      simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at this
      linarith
    have him : ((B.emb w).1 c).im ≠ 0 := fun e =>
      (map_ne_zero (B.emb w).1).2 hc (Complex.ext hre e)
    refine exists_frame (s := -((B.emb w).1 c).im) ?_ (hW.cartan w) (neg_ne_zero.2 him) ?_
    · ext i j
      simp [hcj, hW.skew]
    · ext i j
      have e : (B.emb w).1 c = ((B.emb w).1 c).im * Complex.I := by
        conv_lhs => rw [← Complex.re_add_im ((B.emb w).1 c), hre]
        simp
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, star_mul', hcj]
      conv_lhs => rw [e]
      simp [mul_assoc]
  choose ε Q hQ hk using key
  let e := fun w : InfinitePlace F => RingEquiv.ofBijective _ (infEmb_bijective h (B.emb w))
  let b := fun w : InfinitePlace F => Formalism.UG.bc (e w).symm.toRingHom (Q w)
  have h1 : ∀ w, (b w).1.map (infEmb (B.emb w)) = (Q w).1 := fun w => Matrix.ext fun i j => (e w).apply_symm_apply _
  have h1' : ∀ w, ((b w)⁻¹).1.map (infEmb (B.emb w)) = ((Q w)⁻¹).1 := fun w =>
    Matrix.ext fun i j => (e w).apply_symm_apply _
  have h2 : ∀ w, (JR w.Completion (c • W.J.map σ)).map (infEmb (B.emb w)) = (c • W.J.map σ).map (B.emb w).1 := fun w => by
    ext r s; simp [JR, inclR]
  refine ⟨majCpt σ _ b, isMaxCpt_majCpt h fun w => ⟨ε w, Matrix.map_injective (e w).injective ?_⟩, fun k hkK => ?_⟩
  · change Matrix.map _ (infEmb (B.emb w)) = Matrix.map _ (infEmb (B.emb w))
    rw [Matrix.map_mul, Matrix.map_mul, Frames.map_cT_sigR h, h1, h2, hQ, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    split_ifs <;> simp
  obtain ⟨hk1, hk2⟩ := mem_majCpt.1 hkK
  have hm : mat ((toGAd hσ W.J hc).symm k) = (matHom _ σ _ k).1 := rfl
  refine ⟨fun u hu => Matrix.ext fun i j => at_evI_of_compFin (fun v => ?_) u hu, fun w => ?_⟩
  · have := congrArg (fun g => (matHom _ σ _ g).1 i j) (mem_infPts_iff_forall.1 hk1 v)
    rw [hm, Matrix.sub_apply, map_sub, sub_eq_zero]
    refine this.trans ?_
    simp [Matrix.one_apply, apply_ite (compFin F E v)]
  · have e1 : (mat ((toGAd hσ W.J hc).symm k)).map (piInf (B.emb w)) =
        (matHom _ σ _ (projArch σ _ w k)).1.map (infEmb (B.emb w)) := rfl
    rw [e1]
    refine hk w _ ?_ ?_
    · have : Formalism.UG.cT (sigR _ σ) (matHom _ σ _ (projArch σ _ w k)).1 * JR w.Completion (c • W.J.map σ) *
        (matHom _ σ _ (projArch σ _ w k)).1 = JR w.Completion (c • W.J.map σ) := (projArch σ _ w k).2
      have := congrArg (fun A => A.map (infEmb (B.emb w))) this
      simpa only [Matrix.map_mul, Frames.map_cT_sigR h, h2] using this
    · have : Formalism.UG.cT (sigR _ σ) ((b w)⁻¹ * matHom _ σ _ (projArch σ _ w k) * b w).1 * 1 *
        ((b w)⁻¹ * matHom _ σ _ (projArch σ _ w k) * b w).1 = 1 := mem_stabArch.1 (hk2 w)
      have := congrArg (fun A => A.map (infEmb (B.emb w))) this
      simpa only [Matrix.mul_one, Matrix.map_mul, Frames.map_cT_sigR h, Units.val_mul, h1, h1',
        Matrix.map_one _ (map_zero _) (map_one _)] using this

end GlobalTheory.ThK.SqIntMaxCpt
end
end

section
section
open Matrix

namespace GlobalTheory.SimNormal

theorem diagonal_comm_of_comm {n : ℕ} {d f : Fin n → ℂ} {g : Matrix (Fin n) (Fin n) ℂ}
    (h : diagonal d * g = g * diagonal d) (hf : ∀ i j, d i = d j → f i = f j) :
    diagonal f * g = g * diagonal f := by
  ext i j
  have e := congrFun (congrFun h i) j
  simp only [diagonal_mul, mul_diagonal] at e ⊢
  by_cases hg : g i j = 0
  · simp [hg]
  · have : d i = d j := mul_right_cancel₀ hg (e.trans (mul_comm _ _))
    rw [hf i j this, mul_comm]

theorem simultaneous_normal_form : ∀ {n : ℕ} {J P : Matrix (Fin n) (Fin n) ℂ}, J.IsHermitian → J.det ≠ 0 → P.IsHermitian →
    (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) →
    ∃ (ε : Fin n → Bool) (Q : GL (Fin n) ℂ), Q.1ᴴ * J * Q.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) ∧
      ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * P * g = P → gᴴ * J * g = J →
        ((Q⁻¹).1 * g * Q.1)ᴴ * ((Q⁻¹).1 * g * Q.1) = 1 := by
  intro n J P hJ hJd hP hpos
  obtain ⟨Q₀, hQ₀⟩ := GlobalTheory.ThK.SqIntMaxCpt.exists_congr_one hP hpos
  set M := Q₀.1ᴴ * J * Q₀.1 with hMdef
  have hM : M.IsHermitian := isHermitian_conjTranspose_mul_mul _ hJ
  set U : Matrix (Fin n) (Fin n) ℂ := hM.eigenvectorUnitary.1 with hU
  have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hM.eigenvectorUnitary.2
  have h1' : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hM.eigenvectorUnitary.2
  set d : Fin n → ℝ := hM.eigenvalues with hd
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal fun i => (d i : ℂ) with hD
  have h3 : Uᴴ * M * U = D := by
    have := hM.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def] using this
  have hdne : ∀ i, d i ≠ 0 := by
    have hUd : Uᴴ.det * U.det = 1 := by rw [← det_mul, h1, det_one]
    have hQd : Q₀.1.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 Q₀.isUnit).ne_zero
    have hDd : D.det ≠ 0 := by
      rw [← h3, hMdef, det_mul, det_mul, det_mul, det_mul]
      have hU1 : Uᴴ.det ≠ 0 := left_ne_zero_of_mul_eq_one hUd
      have hU2 : U.det ≠ 0 := right_ne_zero_of_mul_eq_one hUd
      have hQ2 : Q₀.1ᴴ.det ≠ 0 := by rw [det_conjTranspose]; simpa using hQd
      simp only [ne_eq, mul_eq_zero, not_or]; tauto
    intro i hi
    apply hDd
    rw [hD, det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have hMU : U * D * Uᴴ = M := by
    rw [← h3]; simp only [← Matrix.mul_assoc, h1', Matrix.one_mul]; rw [Matrix.mul_assoc, h1', Matrix.mul_one]
  set s : Fin n → ℝ := fun i => (Real.sqrt |d i|)⁻¹ with hs
  have hsq : ∀ i, 0 < Real.sqrt |d i| := fun i => Real.sqrt_pos.2 (abs_pos.2 (hdne i))
  let S : GL (Fin n) ℂ := ⟨diagonal fun i => (s i : ℂ), diagonal fun i => (Real.sqrt |d i| : ℂ), by
      rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i
      simp only [hs, Complex.ofReal_inv]; exact inv_mul_cancel₀ (by exact_mod_cast (hsq i).ne'), by
      rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i
      simp only [hs, Complex.ofReal_inv]; exact mul_inv_cancel₀ (by exact_mod_cast (hsq i).ne')⟩
  let Ug : GL (Fin n) ℂ := ⟨U, Uᴴ, h1', h1⟩
  refine ⟨fun i => decide (0 < d i), Q₀ * Ug * S, ?_, fun g hgP hgJ => ?_⟩
  · have hSh : (S.1)ᴴ = S.1 := by
      show (diagonal fun i => (s i : ℂ))ᴴ = _
      rw [diagonal_conjTranspose]; congr 1; funext i; simp
    have : (Q₀ * Ug * S).1ᴴ * J * (Q₀ * Ug * S).1 = S.1 * (Uᴴ * M * U) * S.1 := by
      simp only [Units.val_mul, conjTranspose_mul, hSh, Matrix.mul_assoc, hMdef]; rfl
    rw [this, h3]
    show diagonal _ * diagonal _ * diagonal _ = _
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; funext i
    have hsi : s i * s i = |d i|⁻¹ := by
      simp only [hs]; rw [← mul_inv, Real.mul_self_sqrt (abs_nonneg _)]
    have : (s i : ℂ) * d i * s i = ((d i * (s i * s i) : ℝ) : ℂ) := by push_cast; ring
    rw [this, hsi]
    rcases lt_or_gt_of_ne (hdne i) with h | h
    · simp [h, not_lt.2 h.le, abs_of_neg h, (hdne i)]
    · simp [h, abs_of_pos h, (hdne i)]
  · have hi : (Q₀⁻¹).1ᴴ * Q₀.1ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
    have hPi : (Q₀⁻¹).1ᴴ * (Q₀⁻¹).1 = P := by
      have := congrArg (fun A => (Q₀⁻¹).1ᴴ * A * (Q₀⁻¹).1) hQ₀
      simpa only [← Matrix.mul_assoc, hi, Matrix.one_mul, Matrix.mul_one, Units.mul_inv_cancel_right] using this.symm
    have hJi : (Q₀⁻¹).1ᴴ * M * (Q₀⁻¹).1 = J := by
      rw [hMdef]
      simp only [← Matrix.mul_assoc, hi, Matrix.one_mul, Units.mul_inv_cancel_right]
    set g' := Uᴴ * (Q₀⁻¹).1 * g * Q₀.1 * U with hg'
    have hg'1 : g'ᴴ * g' = 1 := by
      calc g'ᴴ * g' = Uᴴ * Q₀.1ᴴ * (gᴴ * ((Q₀⁻¹).1ᴴ * (U * Uᴴ) * (Q₀⁻¹).1) * g) * Q₀.1 * U := by
            simp only [hg', conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
        _ = Uᴴ * (Q₀.1ᴴ * P * Q₀.1) * U := by
            rw [h1', Matrix.mul_one, hPi, hgP]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hQ₀, Matrix.mul_one, h1]
    have hg'D : g'ᴴ * D * g' = D := by
      calc g'ᴴ * D * g' = Uᴴ * Q₀.1ᴴ * (gᴴ * ((Q₀⁻¹).1ᴴ * (U * D * Uᴴ) * (Q₀⁻¹).1) * g) * Q₀.1 * U := by
            simp only [hg', conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
        _ = Uᴴ * (Q₀.1ᴴ * J * Q₀.1) * U := by
            rw [hMU, hJi, hgJ]; simp only [Matrix.mul_assoc]
        _ = D := by rw [← hMdef, h3]
    have hg'2 : g' * g'ᴴ = 1 := mul_eq_one_comm.1 hg'1
    have hcomm : D * g' = g' * D := by
      calc D * g' = g' * g'ᴴ * D * g' := by rw [hg'2, Matrix.one_mul]
        _ = g' * (g'ᴴ * D * g') := by simp only [Matrix.mul_assoc]
        _ = g' * D := by rw [hg'D]
    have hQinv : ((Q₀ * Ug * S)⁻¹).1 * g * (Q₀ * Ug * S).1 = (S⁻¹).1 * g' * S.1 := by
      simp only [_root_.mul_inv_rev, Units.val_mul, hg', Matrix.mul_assoc]; rfl
    have hSc : (S⁻¹).1 * g' = g' * (S⁻¹).1 :=
      diagonal_comm_of_comm (f := fun i => (Real.sqrt |d i| : ℂ)) hcomm fun i j h => by
        have : d i = d j := by exact_mod_cast h
        simp [this]
    have hfin : (S⁻¹).1 * g' * S.1 = g' := by
      rw [hSc, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    rw [hQinv, hfin]
    exact hg'1

end GlobalTheory.SimNormal
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_posDef_simultaneous_normal_form : ∀ {n : ℕ} {J P : Matrix (Fin n) (Fin n) ℂ}, J.IsHermitian → J.det ≠ 0 → P.IsHermitian →
    (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) →
    ∃ (ε : Fin n → Bool) (Q : GL (Fin n) ℂ), Q.1ᴴ * J * Q.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) ∧
      ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * P * g = P → gᴴ * J * g = J →
        ((Q⁻¹).1 * g * Q.1)ᴴ * ((Q⁻¹).1 * g * Q.1) = 1 := by
  atlas_forward_decl GlobalTheory.SimNormal.simultaneous_normal_form
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Matrix
noncomputable section

namespace GlobalTheory.CptMajorant

theorem exists_frame_le_majCpt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ K : Subgroup (GAd σ J), K ≤ infPts σ J → IsCompact (K : Set (GAd σ J)) →
    ∃ c : (∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E)),
      (∀ w, ∃ ε : Fin n → Bool, Formalism.UG.cT (sigR _ σ) (c w).1 * JR w.Completion J * (c w).1 =
        Matrix.diagonal fun i => if ε i then 1 else -1) ∧ K ≤ majCpt σ J c := by
  intro F E _ _ _ _ _ σ h n J hJ K hKinf hK
  have key : ∀ w : InfinitePlace F, ∃ c : GL (Fin n) (w.Completion ⊗[F] E),
      (∃ ε : Fin n → Bool, Formalism.UG.cT (sigR _ σ) c.1 * JR w.Completion J * c.1 =
        Matrix.diagonal fun i => if ε i then 1 else -1) ∧ ∀ k ∈ K, projArch σ J w k ∈ stabArch σ J w c := by
    intro w
    obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
    let e := RingEquiv.ofBijective _ (infEmb_bijective h τ)
    have : IsTopologicalRing (w.Completion ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens
    let φ : GAd σ J →* GL (Fin n) ℂ :=
      (Units.map (infEmb τ).mapMatrix.toMonoidHom).comp ((matHom _ σ J).comp (projArch σ J w))
    have hφv : ∀ x, (φ x).1 = (matHom _ σ J (projArch σ J w x)).1.map (infEmb τ) := fun x => rfl
    have hcv : Continuous fun x : GAd σ J => (φ x).1 := by
      simp only [hφv]
      exact (Units.continuous_val.comp ((isEmbedding_matHom _ σ J).continuous.comp
        (continuous_projArch σ J w))).matrix_map (GlobalTheory.Orb.continuous_infEmb τ)
    have hφ : Continuous φ := Units.continuous_iff.2 ⟨hcv, by
      simp only [← map_inv]; exact hcv.comp continuous_inv⟩
    obtain ⟨P, hPh, hPpos, hPinv⟩ := GlobalTheory.T.exists_posDef_hermitian_invariant_of_isCompact (K.map φ) (by rw [Subgroup.coe_map]; exact hK.image hφ)
    have hG : (J.map τ.1).IsHermitian := by
      ext i j
      exact (h.2.2.2 τ.1 _).symm.trans (congrArg _ (hJ.1 i j))
    have hd : (J.map τ.1).det ≠ 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (map_ne_zero _).2 hJ.2
    obtain ⟨ε, Q, hQ, hQu⟩ := GlobalTheory.T.hermitian_posDef_simultaneous_normal_form hG hd hPh hPpos
    have h1 : (Formalism.UG.bc e.symm.toRingHom Q).1.map (infEmb τ) = Q.1 := Matrix.ext fun i j => e.apply_symm_apply _
    have h1' : ((Formalism.UG.bc e.symm.toRingHom Q)⁻¹).1.map (infEmb τ) = (Q⁻¹).1 :=
      Matrix.ext fun i j => e.apply_symm_apply _
    have h2 : (JR w.Completion J).map (infEmb τ) = J.map τ.1 := by ext r s; simp [JR, inclR]
    refine ⟨Formalism.UG.bc e.symm.toRingHom Q, ⟨ε, Matrix.map_injective e.injective ?_⟩, fun k hk => ?_⟩
    · change Matrix.map _ (infEmb τ) = Matrix.map _ (infEmb τ)
      rw [Matrix.map_mul, Matrix.map_mul, Frames.map_cT_sigR h, h1, h2, hQ, Matrix.diagonal_map (map_zero _)]
      congr 1
      funext i
      split_ifs <;> simp
    · rw [mem_stabArch]
      change Formalism.UG.cT _ _ * 1 * _ = 1
      refine Matrix.map_injective e.injective ?_
      change Matrix.map _ (infEmb τ) = Matrix.map _ (infEmb τ)
      have hu := hQu (φ k).1 (hPinv _ ⟨k, hk, rfl⟩) (by
        have : Formalism.UG.cT (sigR _ σ) (matHom _ σ J (projArch σ J w k)).1 * JR w.Completion J *
          (matHom _ σ J (projArch σ J w k)).1 = JR w.Completion J := (projArch σ J w k).2
        have := congrArg (fun A => A.map (infEmb τ)) this
        simpa only [Matrix.map_mul, Frames.map_cT_sigR h, h2, hφv] using this)
      simpa only [Matrix.mul_one, Matrix.map_mul, Frames.map_cT_sigR h, Units.val_mul, h1, h1', hφv,
        Matrix.map_one _ (map_zero _) (map_one _)] using hu
  choose c hc hKc using key
  exact ⟨c, hc, fun k hk => mem_majCpt.2 ⟨hKinf hk, fun w => hKc w k hk⟩⟩

end GlobalTheory.CptMajorant
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_majorantFrame_compact_subgroup_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ K : Subgroup (GAd σ J), K ≤ infPts σ J → IsCompact (K : Set (GAd σ J)) →
    ∃ c : (∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E)),
      (∀ w, ∃ ε : Fin n → Bool, Formalism.UG.cT (sigR _ σ) (c w).1 * JR w.Completion J * (c w).1 =
        Matrix.diagonal fun i => if ε i then 1 else -1) ∧ K ≤ majCpt σ J c := by
  first | exact @GlobalTheory.CptMajorant.exists_frame_le_majCpt | exact GlobalTheory.CptMajorant.exists_frame_le_majCpt | (intros; apply GlobalTheory.CptMajorant.exists_frame_le_majCpt <;> assumption)
end
