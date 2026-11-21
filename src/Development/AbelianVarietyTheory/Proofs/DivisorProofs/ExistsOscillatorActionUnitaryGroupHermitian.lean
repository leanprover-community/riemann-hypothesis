import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionOfGaussianPairings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianPairingUnitaryGroupTwoThree

section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_oscillatorAction_of_gaussianPairings : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ h : IsHeis (omJ J) ρ, ∀ (G : Type) [Group G] (k : G →* (V →L[ℝ] V)) (c : G → ℂ), (∀ g x y, omJ J (k g x) (k g y) = omJ J x y) → c 1 = 1 → (∀ g, star (c g) * c g * lam (k g) = 1) → (∀ g g', c g * c g' * mu J (k (g * g')) (k g) = c (g * g') * lam (k (g * g'))) → ∃ Ω : G → B → B, IsOsc ρ (fun g v => k g v) Ω ∧ (∀ (Y : Type) [TopologicalSpace Y] (γ : Y → G), Continuous (fun y => k (γ y)) → Continuous (fun y => c (γ y)) → ∀ f, Sm ρ f → Continuous fun y => Ω (γ y) f) ∧ ∀ a g, (∀ x, ‖k g x‖ = ‖x‖) → ∀ f, Sm ρ f → ∫ u, gau u • ρ (k a u) f = f → Ω (a * g * a⁻¹) f = c g • f := by
  first | exact @GlobalTheory.RealWeil.Osc.exists_isOsc | exact GlobalTheory.RealWeil.Osc.exists_isOsc | (intros; apply GlobalTheory.RealWeil.Osc.exists_isOsc <;> assumption)
end

section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory

open scoped MatrixOrder in

theorem cartanInvolution_conj_of_posDef (ι : Type) [Fintype ι] [DecidableEq ι]
    (s s' : Matrix ι ι ℂ) (hs : sᴴ = s) (hss : s * s = 1) (hs's' : s' * s' = 1)
    (hM : (s * s').PosDef) :
    ∃ a : Matrix ι ι ℂ, aᴴ * s * a = s ∧ a * s = s' * a := by
  set M := s * s' with hMdef
  have hMpsd : M.PosSemidef := hM.posSemidef
  have hM0 : 0 ≤ M := Matrix.nonneg_iff_posSemidef.mpr hMpsd
  set R := CFC.sqrt M with hRdef
  have hR0 : 0 ≤ R := CFC.sqrt_nonneg M
  have hRpsd : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hR0
  have hRR : R * R = M := CFC.sqrt_mul_sqrt_self M hM0
  have hRh : Rᴴ = R := hRpsd.isHermitian
  have hsM : s * M = s' := by rw [hMdef, ← Matrix.mul_assoc, hss, Matrix.one_mul]
  have hMinv : M⁻¹ = s * M * s := by
    apply Matrix.inv_eq_left_inv
    calc s * M * s * M = (s * M) * (s * M) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hsM, hs's']
  have hsRs : CFC.sqrt M⁻¹ = s * R * s := by
    refine CFC.sqrt_unique ?_ ?_
    · calc s * R * s * (s * R * s) = s * (R * R) * s := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc s s, hss, Matrix.one_mul]
        _ = M⁻¹ := by rw [hRR, hMinv]
    · have h := hRpsd.conjTranspose_mul_mul_same s
      rw [hs] at h
      exact Matrix.nonneg_iff_posSemidef.mpr h
  have hRinv : R⁻¹ = s * R * s := by
    rw [← hsRs]
    exact hMpsd.inv_sqrt
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.mpr hM.det_pos.ne'
  have hRu : IsUnit R.det := by
    rw [← hRR, Matrix.det_mul] at hMu
    exact isUnit_of_mul_isUnit_left hMu
  have hsRinv : s * R⁻¹ = R * s := by
    rw [hRinv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hss, Matrix.one_mul]
  refine ⟨R⁻¹, ?_, ?_⟩
  · rw [Matrix.conjTranspose_nonsing_inv, hRh, Matrix.mul_assoc, hsRinv, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hRu, Matrix.one_mul]
  · calc R⁻¹ * s = s * R := by rw [hRinv, Matrix.mul_assoc, hss, Matrix.mul_one]
      _ = s * M * R⁻¹ := by
        rw [← hRR, Matrix.mul_assoc s, Matrix.mul_assoc R, Matrix.mul_nonsing_inv _ hRu,
          Matrix.mul_one]
      _ = s' * R⁻¹ := by rw [hsM]

end GlobalTheory
end

section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussianPairing_unitaryGroup_two_three : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (ι : Type) [Fintype ι] [DecidableEq ι] (e : V ≃L[ℝ] (ι → ℂ)), (∀ v, ‖v‖ ^ 2 = ∑ i, ‖e v i‖ ^ 2) → ∀ (s : Matrix ι ι ℂ), sᴴ = s → s * s = 1 → ∀ J : V ≃ₗᵢ[ℝ] V, (∀ v, e (J v) = I • s *ᵥ e v) → (∀ (g : Matrix ι ι ℂ) (k : V → V), gᴴ * s * g = s → (∀ v, e (k v) = g *ᵥ e v) → dP s g ≠ 0 ∧ dP s g⁻¹ = star (dP s g) ∧ lam k = (dP s g * dP s g⁻¹)⁻¹) ∧ ∀ (g₁ g₂ : Matrix ι ι ℂ) (k₁ k₂ : V → V), g₁ᴴ * s * g₁ = s → g₂ᴴ * s * g₂ = s → (∀ v, e (k₁ v) = g₁ *ᵥ e v) → (∀ v, e (k₂ v) = g₂ *ᵥ e v) → mu J k₁ k₂ = (dP s g₁⁻¹ * dP s g₂ * dP s (g₂⁻¹ * g₁))⁻¹ := by
  first | exact @GlobalTheory.RealWeil.GaussPairing.lam_mu_eq | exact GlobalTheory.RealWeil.GaussPairing.lam_mu_eq | (intros; apply GlobalTheory.RealWeil.GaussPairing.lam_mu_eq <;> assumption)
end

section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory

open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in

theorem _root_.GlobalTheory.hermitian_congr_involution (ι : Type) [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : Hᴴ = H) (hd : H.det ≠ 0) :
    ∃ R s : Matrix ι ι ℂ, R.det ≠ 0 ∧ sᴴ = s ∧ s * s = 1 ∧ Rᴴ * s * R = H := by
  have hA : H.IsHermitian := hH
  set U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  set d := hA.eigenvalues with hdd
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i hi
    apply hd
    rw [hA.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← hdd, hi]; simp)
  set s : Matrix ι ι ℂ := diagonal fun i => if 0 < d i then 1 else -1 with hs
  set D : Matrix ι ι ℂ := diagonal fun i => ((Real.sqrt |d i| : ℝ) : ℂ) with hD
  have key : D * s * D = diagonal (RCLike.ofReal ∘ d) := by
    rw [hD, hs, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    have hsq : ((Real.sqrt |d i| : ℝ) : ℂ) * ((Real.sqrt |d i| : ℝ) : ℂ) = ((|d i| : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (abs_nonneg _)]
    simp only [Function.comp_apply]
    split_ifs with h
    · rw [mul_one, hsq, abs_of_pos h]; rfl
    · rw [mul_neg_one, neg_mul, hsq, abs_of_neg (lt_of_le_of_ne (not_lt.1 h) (hd0 i))]
      push_cast; ring_nf; rfl
  have hDH : Dᴴ = D := by
    rw [hD, diagonal_conjTranspose]; congr 1; funext i; simp
  have hsH : sᴴ = s := by
    rw [hs, diagonal_conjTranspose]; congr 1; funext i; by_cases h : 0 < d i <;> simp [h]
  have hss : s * s = 1 := by
    rw [hs, diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; split_ifs <;> simp
  have hR : (D * star U)ᴴ * s * (D * star U) = H := by
    rw [conjTranspose_mul, hDH, star_eq_conjTranspose, conjTranspose_conjTranspose]
    conv_rhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, ← key]
    simp only [Matrix.mul_assoc, star_eq_conjTranspose]
    rfl
  refine ⟨D * star U, s, ?_, hsH, hss, hR⟩
  intro h0
  apply hd
  rw [← hR, det_mul, det_mul, h0, mul_zero]

end GlobalTheory
end

section
noncomputable section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.RealWeil.Vacuum

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] {J : V ≃ₗᵢ[ℝ] V} {ρ : V → B →L[ℂ] B}

theorem differentiable_norm (f : B) (hf : Sm ρ f) : Differentiable ℝ fun u => (gau u)⁻¹ • ρ u f :=
  ((contDiff_gau_inv (V := V)).smul hf).differentiable (by simp)

theorem fderiv_norm (h : IsHeis (omJ J) ρ) (f : B) (hf : Sm ρ f) (u z : V) :
    fderiv ℝ (fun u => (gau u)⁻¹ • ρ u f) u z =
      (gau u)⁻¹ • ρ u (fderiv ℝ (fun v => ρ v f) 0 z) +
        ((gau u)⁻¹ * (π * (⟪u, z⟫ : ℝ) - π * I * (⟪u, J z⟫ : ℝ))) • ρ u f := by
  have hl : HasDerivAt (fun s : ℝ => u + s • z) z 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const z).const_add u
  have hl0 : HasDerivAt (fun s : ℝ => s • z) z 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const z)
  have h1 : HasDerivAt (fun s : ℝ => (gau (u + s • z))⁻¹ • ρ (u + s • z) f)
      (fderiv ℝ (fun u => (gau u)⁻¹ • ρ u f) u z) 0 :=
    (differentiable_norm f hf u).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have h2 : HasDerivAt (fun s : ℝ => ρ (s • z) f) (fderiv ℝ (fun v => ρ v f) 0 z) 0 :=
    ((ContDiff.differentiable hf (by simp)) 0).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl0 (by simp)
  have h3 : HasDerivAt (fun s : ℝ => ρ u (ρ (s • z) f)) (ρ u (fderiv ℝ (fun v => ρ v f) 0 z)) 0 :=
    ((ρ u).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  set c : ℂ := π * (⟪u, z⟫ : ℝ) - π * I * (⟪u, J z⟫ : ℝ) with hc
  have h4 : HasDerivAt (fun s : ℂ => (gau u)⁻¹ * cexp (c * s + (π / 2 * ‖z‖ ^ 2) * s ^ 2)) ((gau u)⁻¹ * c) 0 := by
    have := ((((hasDerivAt_id (0 : ℂ)).const_mul c).add
      (((hasDerivAt_id (0 : ℂ)).pow 2).const_mul (π / 2 * ‖z‖ ^ 2 : ℂ))).cexp).const_mul (gau u)⁻¹
    simpa using this
  have h5 : HasDerivAt (fun s : ℝ => (gau u)⁻¹ * cexp (c * s + (π / 2 * ‖z‖ ^ 2) * s ^ 2)) ((gau u)⁻¹ * c) 0 :=
    HasDerivAt.comp_ofReal (z := 0) (by rw [ofReal_zero]; exact h4)
  have h6 := h5.smul h3
  have e : (fun s : ℝ => (gau (u + s • z))⁻¹ • ρ (u + s • z) f) =
      (fun s : ℝ => (gau u)⁻¹ * cexp (c * s + (π / 2 * ‖z‖ ^ 2) * s ^ 2)) • fun s : ℝ => ρ u (ρ (s • z) f) := by
    funext s
    simp only [Pi.smul_apply', h.2.1, smul_smul]
    congr 1
    have n : ((‖u + s • z‖ : ℝ) : ℂ) ^ 2 = (‖u‖ : ℂ) ^ 2 + 2 * s * (⟪u, z⟫ : ℝ) + s ^ 2 * ‖z‖ ^ 2 := by
      have : ‖u + s • z‖ ^ 2 = ‖u‖ ^ 2 + 2 * s * ⟪u, z⟫ + s ^ 2 * ‖z‖ ^ 2 := by
        rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
      exact_mod_cast this
    have o : omJ J u (s • z) = s * ⟪u, J z⟫ := by simp [omJ, inner_smul_right]
    rw [gau, gau, n, o, ← Complex.exp_neg, ← Complex.exp_neg, ← Complex.exp_add, ← Complex.exp_add, hc]
    congr 1
    push_cast
    ring
  rw [← e] at h6
  rw [h1.unique h6]
  simp [h.1]

theorem fderiv_norm_J (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (f : B) (hf : Sm ρ f)
    (ha : ∀ z, fderiv ℝ (fun v => ρ v f) 0 z + I • fderiv ℝ (fun v => ρ v f) 0 (J z) = 0) (u z : V) :
    fderiv ℝ (fun u => (gau u)⁻¹ • ρ u f) u (J z) = I • fderiv ℝ (fun u => (gau u)⁻¹ • ρ u f) u z := by
  have e : fderiv ℝ (fun v => ρ v f) 0 (J z) = I • fderiv ℝ (fun v => ρ v f) 0 z := by
    rw [eq_neg_of_add_eq_zero_left (ha z), smul_neg, smul_smul, I_mul_I]
    simp
  rw [fderiv_norm h f hf, fderiv_norm h f hf, e, map_smul, smul_add, smul_comm I, smul_smul I, hJ, inner_neg_right]
  congr 2
  push_cast
  linear_combination (gau u)⁻¹ * π * (⟪u, J z⟫ : ℝ) * I_mul_I

def line (J : V ≃ₗᵢ[ℝ] V) (u : V) : ℂ →L[ℝ] V := reCLM.smulRight u + imCLM.smulRight (J u)

open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] {J : V ≃ₗᵢ[ℝ] V} {ρ : V → B →L[ℂ] B} in
theorem _root_.GlobalTheory.RealWeil.Vacuum.line_apply (u : V) (ζ : ℂ) :
    _root_.GlobalTheory.RealWeil.Vacuum.line J u ζ = ζ.re • u + ζ.im • J u := by
  simp [_root_.GlobalTheory.RealWeil.Vacuum.line]

theorem mean_value [CompleteSpace B] (hJ : ∀ x, J (J x) = -x) (h : IsHeis (omJ J) ρ) (f : B) (hf : Sm ρ f)
    (ha : ∀ z, fderiv ℝ (fun v => ρ v f) 0 z + I • fderiv ℝ (fun v => ρ v f) 0 (J z) = 0) (u : V) :
    ∫ θ in (0 : ℝ)..2 * π, (gau (line J u (circleMap 0 1 θ)))⁻¹ • ρ (line J u (circleMap 0 1 θ)) f =
      (2 * π) • f := by
  have hd : Differentiable ℂ fun ζ => (gau (line J u ζ))⁻¹ • ρ (line J u ζ) f := by
    intro ζ
    have h1 : HasFDerivAt (fun ζ => (gau (line J u ζ))⁻¹ • ρ (line J u ζ) f)
        ((fderiv ℝ (fun u => (gau u)⁻¹ • ρ u f) (line J u ζ)).comp (line J u)) ζ :=
      (differentiable_norm f hf _).hasFDerivAt.comp ζ (line J u).hasFDerivAt
    refine differentiableAt_complex_iff_differentiableAt_real.2 ⟨h1.differentiableAt, ?_⟩
    rw [h1.fderiv]
    simpa [line_apply] using fderiv_norm_J hJ h f hf ha (line J u ζ) u
  have := DiffContOnCl.circleAverage (c := 0) (R := 1) hd.diffContOnCl
  rw [Real.circleAverage_def] at this
  simp only [map_zero, gau_zero, h.1, inv_one, one_smul] at this
  conv_rhs => rw [← this]
  rw [smul_inv_smul₀ Real.two_pi_pos.ne']

open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] {J : V ≃ₗᵢ[ℝ] V} {ρ : V → B →L[ℂ] B} in
private theorem inner_self_complexStructure_eq_zero (hJ : ∀ x, J (J x) = -x) (u : V) :
    ⟪u, J u⟫ = 0 := by
  have e := J.inner_map_map u (J u)
  rw [hJ, inner_neg_right, real_inner_comm u (J u)] at e
  linarith

open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] {J : V ≃ₗᵢ[ℝ] V} {ρ : V → B →L[ℂ] B} in
theorem _root_.GlobalTheory.RealWeil.Vacuum.norm_line (hJ : ∀ x, J (J x) = -x) (u : V) (θ : ℝ) :
    ‖_root_.GlobalTheory.RealWeil.Vacuum.line J u (circleMap 0 1 θ)‖ = ‖u‖ := by
  have h0 := inner_self_complexStructure_eq_zero hJ u
  rw [_root_.GlobalTheory.RealWeil.Vacuum.line_apply, circleMap_zero, ofReal_one, one_mul,
    exp_ofReal_mul_I_re, exp_ofReal_mul_I_im,
    ← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm u (J u), h0, LinearIsometryEquiv.inner_map_map, mul_zero, add_zero, zero_add]
  linear_combination ⟪u, u⟫ * Real.cos_sq_add_sin_sq θ

def rot [FiniteDimensional ℝ V] (hJ : ∀ x, J (J x) = -x) (θ : ℝ) : V ≃ₗᵢ[ℝ] V :=
  LinearIsometry.toLinearIsometryEquiv
    { toFun := fun u => line J u (circleMap 0 1 θ)
      map_add' := fun x y => by simp only [line_apply, map_add, smul_add]; abel
      map_smul' := fun a x => by simp only [line_apply, map_smul, smul_add, RingHom.id_apply, smul_comm a]
      norm_map' := fun u => norm_line hJ u θ } rfl

end GlobalTheory.RealWeil.Vacuum

namespace GlobalTheory.RealWeil

open Vacuum

open MeasureTheory Complex in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] in
private theorem gaussian_exponent_add_eq (a s : ℝ) (ζ η : ℂ)
    (hs : s = a * (ζ.im * η.re - ζ.re * η.im)) :
    ((Real.pi / 2 * a * ‖ζ + η‖ ^ 2 : ℝ) : ℂ) + -(Real.pi * I * s) =
      ((Real.pi / 2 * a * ‖ζ‖ ^ 2 : ℝ) : ℂ) + Real.pi * a * ((starRingEnd ℂ) ζ * η) +
        ((Real.pi / 2 * a * ‖η‖ ^ 2 : ℝ) : ℂ) := by
  subst hs
  apply Complex.ext <;>
    simp [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring

open MeasureTheory Complex in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] in
private theorem omJ_line_line_eq {J : V ≃ₗᵢ[ℝ] V} (hJ : ∀ x, J (J x) = -x)
    (u : V) (ζ η : ℂ) :
    _root_.GlobalTheory.RealWeil.omJ J (_root_.GlobalTheory.RealWeil.Vacuum.line J u ζ)
      (_root_.GlobalTheory.RealWeil.Vacuum.line J u η) = ‖u‖ ^ 2 * (ζ.im * η.re - ζ.re * η.im) := by
  have h0 := inner_self_complexStructure_eq_zero hJ u
  unfold _root_.GlobalTheory.RealWeil.omJ
  simp only [_root_.GlobalTheory.RealWeil.Vacuum.line_apply, map_add, map_smul, hJ, inner_add_left,
    inner_add_right, real_inner_smul_left, real_inner_smul_right, inner_neg_right,
    real_inner_comm u (J u), h0, LinearIsometryEquiv.inner_map_map, real_inner_self_eq_norm_sq]
  ring

open MeasureTheory Complex in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] in
private theorem differentiable_gaussian_mul_orbit_line {J : V ≃ₗᵢ[ℝ] V} {ρ : V → B →L[ℂ] B}
    (hJ : ∀ x, J (J x) = -x)
    (h : _root_.GlobalTheory.RealWeil.IsHeis (_root_.GlobalTheory.RealWeil.omJ J) ρ)
    (f : B) (hf : _root_.GlobalTheory.RealWeil.Sm ρ f)
    (ha : ∀ z, fderiv ℝ (fun v => ρ v f) 0 z + I • fderiv ℝ (fun v => ρ v f) 0 (J z) = 0)
    (u : V) :
    Differentiable ℂ fun ζ : ℂ =>
      cexp ((Real.pi / 2 * ‖u‖ ^ 2 * ‖ζ‖ ^ 2 : ℝ) : ℂ) • ρ (_root_.GlobalTheory.RealWeil.Vacuum.line J u ζ) f := by
  obtain ⟨-, hmul, -, -⟩ := h
  set ψ : ℂ → B := fun ζ =>
    cexp ((Real.pi / 2 * ‖u‖ ^ 2 * ‖ζ‖ ^ 2 : ℝ) : ℂ) • ρ (_root_.GlobalTheory.RealWeil.Vacuum.line J u ζ) f
    with hψ
  set D := fderiv ℝ (fun v => ρ v f) 0
  have hD : HasFDerivAt (fun v => ρ v f) D 0 :=
    ((hf.differentiable (by simp)) 0).hasFDerivAt
  have hDJ : ∀ z, D (J z) = I • D z := by
    intro z
    have e : I • D (J z) = -D z := eq_neg_of_add_eq_zero_right (ha z)
    calc D (J z) = (-I * I) • D (J z) := by simp [I_mul_I]
      _ = -I • (I • D (J z)) := by rw [smul_smul]
      _ = I • D z := by rw [e, smul_neg, neg_smul, neg_neg]
  have key : ∀ η : ℂ, D (_root_.GlobalTheory.RealWeil.Vacuum.line J u η) = η • D u := by
    intro η
    rw [_root_.GlobalTheory.RealWeil.Vacuum.line_apply, map_add, map_smul, map_smul, hDJ,
      ← Complex.coe_smul η.re, ← Complex.coe_smul η.im, smul_smul (η.im : ℂ) I, ← add_smul,
      Complex.re_add_im]
  have hψ0 : HasDerivAt ψ (D u) 0 := by
    have hn : HasFDerivAt (fun ζ : ℂ => ((Real.pi / 2 * ‖u‖ ^ 2 * ‖ζ‖ ^ 2 : ℝ) : ℂ))
        (0 : ℂ →L[ℝ] ℂ) 0 := by
      have h1 := ((hasStrictFDerivAt_norm_sq (0 : ℂ)).hasFDerivAt.const_mul
        (Real.pi / 2 * ‖u‖ ^ 2))
      have h2 := ofRealCLM.hasFDerivAt.comp (0 : ℂ) h1
      simpa [Function.comp_def] using h2
    have hg : HasFDerivAt (fun ζ => ρ (_root_.GlobalTheory.RealWeil.Vacuum.line J u ζ) f)
        (D.comp (_root_.GlobalTheory.RealWeil.Vacuum.line J u)) 0 := by
      have hD0 : HasFDerivAt (fun v => ρ v f) D (_root_.GlobalTheory.RealWeil.Vacuum.line J u 0) := by
        simpa using hD
      have h3 := hD0.comp (0 : ℂ) (_root_.GlobalTheory.RealWeil.Vacuum.line J u).hasFDerivAt
      simpa [Function.comp_def] using h3
    have hP := hn.cexp.smul hg
    refine (hasFDerivAt_of_restrictScalars ℝ hP
      (f' := (1 : ℂ →L[ℂ] ℂ).smulRight (D u)) ?_).hasDerivAt.congr_deriv (by simp)
    ext η
    simp [key]
  have hshift : ∀ ζ η : ℂ, ψ (ζ + η) =
      cexp ((Real.pi / 2 * ‖u‖ ^ 2 * ‖ζ‖ ^ 2 : ℝ) : ℂ) •
        (cexp (Real.pi * ‖u‖ ^ 2 * ((starRingEnd ℂ) ζ * η)) •
          ρ (_root_.GlobalTheory.RealWeil.Vacuum.line J u ζ) (ψ η)) := by
    intro ζ η
    simp only [hψ, map_add, map_smul]
    rw [hmul, smul_smul, smul_smul, smul_smul, ← exp_add, ← exp_add, ← exp_add]
    congr 2
    have e := gaussian_exponent_add_eq (‖u‖ ^ 2) _ ζ η (omJ_line_line_eq hJ u ζ η)
    push_cast at e ⊢
    linear_combination e
  intro ζ
  have hd : DifferentiableAt ℂ (fun η => ψ (ζ + η)) (ζ - ζ) := by
    rw [sub_self]
    simp_rw [hshift ζ]
    have hψd : DifferentiableAt ℂ ψ 0 := hψ0.differentiableAt
    fun_prop
  have h4 := hd.comp (f := fun y => y - ζ) ζ (differentiableAt_id.sub_const ζ)
  simpa [Function.comp_def] using h4

open MeasureTheory Complex in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] in
private theorem circleAverage_orbit_line_eq_gaussian_smul {J : V ≃ₗᵢ[ℝ] V} {ρ : V → B →L[ℂ] B}
    [CompleteSpace B] (hJ : ∀ x, J (J x) = -x)
    (h : _root_.GlobalTheory.RealWeil.IsHeis (_root_.GlobalTheory.RealWeil.omJ J) ρ)
    (f : B) (hf : _root_.GlobalTheory.RealWeil.Sm ρ f)
    (ha : ∀ z, fderiv ℝ (fun v => ρ v f) 0 z + I • fderiv ℝ (fun v => ρ v f) 0 (J z) = 0)
    (u : V) :
    Real.circleAverage (fun ζ => ρ (_root_.GlobalTheory.RealWeil.Vacuum.line J u ζ) f) 0 1 =
      cexp (-(Real.pi / 2) * ‖u‖ ^ 2) • f := by
  have hψ := differentiable_gaussian_mul_orbit_line hJ h f hf ha u
  have hmean := (hψ.diffContOnCl (s := Metric.ball (0 : ℂ) |1|)).circleAverage
  have hρ0 : ρ 0 f = f := h.1 f
  have hs : Set.EqOn
      (fun ζ : ℂ => cexp ((Real.pi / 2 * ‖u‖ ^ 2 * ‖ζ‖ ^ 2 : ℝ) : ℂ) •
        ρ (_root_.GlobalTheory.RealWeil.Vacuum.line J u ζ) f)
      (fun ζ : ℂ => cexp ((Real.pi / 2 * ‖u‖ ^ 2 : ℝ) : ℂ) • ρ (_root_.GlobalTheory.RealWeil.Vacuum.line J u ζ) f)
      (Metric.sphere 0 |1|) := by
    intro ζ hζ
    simp only [abs_one, mem_sphere_zero_iff_norm] at hζ
    simp [hζ]
  rw [Real.circleAverage_congr_sphere hs, Real.circleAverage_fun_smul] at hmean
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    ofReal_zero, exp_zero, map_zero, hρ0, one_smul] at hmean
  calc Real.circleAverage (fun ζ => ρ (_root_.GlobalTheory.RealWeil.Vacuum.line J u ζ) f) 0 1
      = (cexp (-(Real.pi / 2) * ‖u‖ ^ 2) * cexp ((Real.pi / 2 * ‖u‖ ^ 2 : ℝ) : ℂ)) •
          Real.circleAverage (fun ζ => ρ (_root_.GlobalTheory.RealWeil.Vacuum.line J u ζ) f) 0 1 := by
        rw [← exp_add]; push_cast; ring_nf; simp
    _ = cexp (-(Real.pi / 2) * ‖u‖ ^ 2) • f := by rw [mul_smul, hmean]

open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in

theorem _root_.GlobalTheory.RealWeil.proj_eq_self_of_annihilated (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B]
    [CompleteSpace B]
    (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B) (hJ : ∀ x, J (J x) = -x)
    (h : _root_.GlobalTheory.RealWeil.IsHeis (_root_.GlobalTheory.RealWeil.omJ J) ρ) (f : B)
    (hf : _root_.GlobalTheory.RealWeil.Sm ρ f)
    (ha : ∀ z, fderiv ℝ (fun v => ρ v f) 0 z + I • fderiv ℝ (fun v => ρ v f) 0 (J z) = 0) :
    _root_.GlobalTheory.RealWeil.proj h f = f := by
  have hg : ∀ u : V, _root_.GlobalTheory.RealWeil.gau u = cexp (-(Real.pi / 2) * ‖u‖ ^ 2) := fun u => rfl
  have hiso : ∀ (x : V) (y : B), ‖ρ x y‖ = ‖y‖ := h.2.2.1
  rw [_root_.GlobalTheory.RealWeil.proj_apply]
  set G : ℝ → V → B := fun θ u =>
    _root_.GlobalTheory.RealWeil.gau u • ρ (_root_.GlobalTheory.RealWeil.Vacuum.line J u (circleMap 0 1 θ)) f with hG
  have hrot : ∀ θ, ∫ u, _root_.GlobalTheory.RealWeil.gau u • ρ u f = ∫ u, G θ u := by
    intro θ
    set R := _root_.GlobalTheory.RealWeil.Vacuum.rot hJ θ
    have e := (LinearIsometryEquiv.measurePreserving R).integral_comp
      R.toHomeomorph.measurableEmbedding (fun u => _root_.GlobalTheory.RealWeil.gau u • ρ u f)
    rw [← e]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hG, hg, LinearIsometryEquiv.norm_map]
    rfl
  have hcont : Continuous (Function.uncurry G) := by
    have ha' : Continuous fun p : ℝ × V => _root_.GlobalTheory.RealWeil.Vacuum.line J p.2 (circleMap 0 1 p.1) := by
      simp only [_root_.GlobalTheory.RealWeil.Vacuum.line_apply]
      have := continuous_circleMap (0 : ℂ) 1
      fun_prop
    exact (_root_.GlobalTheory.RealWeil.continuous_gau.comp continuous_snd).smul
      (h.continuous ha' continuous_const)
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))) := by
    rw [isFiniteMeasure_restrict]
    exact ((measure_mono Set.uIoc_subset_uIcc).trans_lt isCompact_uIcc.measure_lt_top).ne
  have hint : Integrable (Function.uncurry G)
      ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod volume) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod
      (_root_.GlobalTheory.RealWeil.integrable_gau.norm.mul_const ‖f‖)) hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    simp [Function.uncurry, hG, norm_smul, hiso]
  have hpos : (2 * Real.pi) ≠ 0 := by positivity
  calc ∫ u, _root_.GlobalTheory.RealWeil.gau u • ρ u f
      = (2 * Real.pi)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, ∫ u, G θ u := by
        rw [intervalIntegral.integral_congr (g := fun _ => ∫ u, _root_.GlobalTheory.RealWeil.gau u • ρ u f)
          (fun θ _ => (hrot θ).symm), intervalIntegral.integral_const, smul_smul, sub_zero,
          inv_mul_cancel₀ hpos, one_smul]
    _ = ∫ u, _root_.GlobalTheory.RealWeil.gau u •
          Real.circleAverage (fun ζ => ρ (_root_.GlobalTheory.RealWeil.Vacuum.line J u ζ) f) 0 1 := by
        rw [intervalIntegral_integral_swap hint, ← integral_smul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        simp only [hG, Real.circleAverage_def, intervalIntegral.integral_smul]
        rw [smul_comm]
    _ = ∫ u, cexp (-(Real.pi : ℂ) * ‖u‖ ^ 2) • f := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        simp only
        rw [circleAverage_orbit_line_eq_gaussian_smul hJ h f hf ha u, smul_smul, hg, ← exp_add]
        ring_nf
    _ = f := by
        rw [integral_smul_const, GaussianFourier.integral_cexp_neg_mul_sq_norm (by simp [Real.pi_pos])]
        simp [div_self (ofReal_ne_zero.2 Real.pi_ne_zero)]

end GlobalTheory.RealWeil

end
end

section
noncomputable section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.RealWeil.UnitaryOsc

section Transport

variable {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]

theorem sm_comp_iff (E : V ≃L[ℝ] V') (ρ : V' → B →L[ℂ] B) (f : B) : Sm (fun v => ρ (E v)) f ↔ Sm ρ f :=
  E.contDiff_comp_iff (f := fun v => ρ v f)

theorem isHeis_comp {om : V' → V' → ℝ} {om' : V → V → ℝ} {ρ : V' → B →L[ℂ] B} (h : IsHeis om ρ) (E : V →L[ℝ] V')
    (hE : ∀ x y, om (E x) (E y) = om' x y) : IsHeis om' fun v => ρ (E v) :=
  ⟨fun f => by simp only [map_zero, h.1], fun u v f => by simp only [h.2.1, hE, map_add], fun u f => h.2.2.1 _ f,
    fun f => (h.2.2.2 f).comp E.continuous⟩

theorem fderiv_comp_clm {ρ : V' → B →L[ℂ] B} {f : B} (hf : Sm ρ f) (E : V →L[ℝ] V') (z : V) :
    fderiv ℝ (fun v => ρ (E v) f) 0 z = fderiv ℝ (fun v => ρ v f) 0 (E z) := by
  have h1 : DifferentiableAt ℝ (fun v => ρ v f) (E 0) := (ContDiff.differentiable hf (by simp)).differentiableAt
  have h2 := fderiv_comp (0 : V) h1 E.differentiableAt
  rw [E.fderiv, map_zero] at h2
  exact congrArg (fun T : V →L[ℝ] B => T z) h2

theorem isOsc_comp (E : V ≃L[ℝ] V') {ρ : V' → B →L[ℂ] B} {G G' : Type} [Group G] [Group G'] (φ : G →* G')
    {k : G → V' → V'} {k' : G' → V → V} (hk : ∀ g v, E (k' (φ g) v) = k g (E v)) {Ω : G' → B → B}
    (h : IsOsc (fun v => ρ (E v)) k' Ω) : IsOsc ρ k fun g => Ω (φ g) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  simp only [sm_comp_iff] at h1 h2 h3 h4 h5 h6 h7 h8
  refine ⟨fun g => h1 _, fun g => h2 _, fun g => h3 _, fun f hf => ?_, fun g g' f hf => ?_, fun g v f hf => ?_,
    fun g A hA => h7 _ A fun v => hA _, fun H _ _ _ Φ hΦ g => h8 H Φ (fun v => hΦ _) _⟩
  · simp only [map_one, h4 f hf]
  · simp only [map_mul, h5 _ _ f hf]
  · have := h6 (φ g) (E.symm v) f hf
    simpa only [hk, E.apply_symm_apply] using this

end Transport

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem detPlus_conj₂ {a s s' g g' : Matrix ι ι ℂ} (ha : a.det ≠ 0) (hs : a * s = s' * a) (hg : a * g = g' * a) :
    dP s g = dP s' g' := by
  have e : a * ((1 / 2 : ℂ) • ((1 + s) * g) + (1 / 2 : ℂ) • (1 - s)) =
      ((1 / 2 : ℂ) • ((1 + s') * g') + (1 / 2 : ℂ) • (1 - s')) * a := by
    have e1 : a * (s * g) = s' * g' * a := by rw [← mul_assoc, hs, mul_assoc, hg, mul_assoc]
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, one_mul, mul_one, hs, hg, e1]
  have := congrArg Matrix.det e
  rw [det_mul, det_mul, mul_comm] at this
  exact mul_right_cancel₀ ha this

theorem detPlus_one₂ (s : Matrix ι ι ℂ) : dP s 1 = 1 := by
  have : (1 / 2 : ℂ) • ((1 + s) * 1) + (1 / 2 : ℂ) • (1 - s) = (1 : Matrix ι ι ℂ) := by
    rw [mul_one]; module
  rw [dP, this, det_one]

theorem continuous_dP (s : Matrix ι ι ℂ) : Continuous (dP s) := by
  unfold dP
  exact Continuous.matrix_det (by fun_prop)

def mvL (g : Matrix ι ι ℂ) : (ι → ℂ) →L[ℝ] (ι → ℂ) :=
  LinearMap.toContinuousLinearMap ((Matrix.mulVecLin g).restrictScalars ℝ)

omit [DecidableEq ι] in
@[simp] theorem mvL_apply (g : Matrix ι ι ℂ) (v : ι → ℂ) : mvL g v = g *ᵥ v := rfl

omit [DecidableEq ι] in
theorem form_mulVec (H a : Matrix ι ι ℂ) (x y : ι → ℂ) :
    star (a *ᵥ y) ⬝ᵥ H *ᵥ a *ᵥ x = star y ⬝ᵥ (aᴴ * H * a) *ᵥ x := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

def crd (ι : Type) [Fintype ι] : EuclideanSpace ℂ ι ≃L[ℝ] (ι → ℂ) := PiLp.continuousLinearEquiv 2 ℝ fun _ : ι => ℂ

omit [DecidableEq ι] in
theorem inner_crd (x y : EuclideanSpace ℂ ι) : ⟪x, y⟫ = (star (crd ι x) ⬝ᵥ crd ι y).re := by
  rw [PiLp.inner_apply, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [crd, mul_comm]

omit [DecidableEq ι] in
theorem norm_sq_crd (x : EuclideanSpace ℂ ι) : ‖x‖ ^ 2 = ∑ i, ‖crd ι x i‖ ^ 2 :=
  EuclideanSpace.norm_sq_eq x

def kL (g : Matrix ι ι ℂ) : EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι :=
  ((crd ι).symm : (ι → ℂ) →L[ℝ] EuclideanSpace ℂ ι) ∘L mvL g ∘L (crd ι : EuclideanSpace ℂ ι →L[ℝ] (ι → ℂ))

omit [DecidableEq ι] in
theorem crd_kL (g : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) : crd ι (kL g v) = g *ᵥ crd ι v := by
  simp [kL]

theorem kL_one : kL (1 : Matrix ι ι ℂ) = 1 :=
  ContinuousLinearMap.ext fun v => (crd ι).injective (by rw [crd_kL, one_mulVec]; rfl)

omit [DecidableEq ι] in
theorem kL_mul (g g' : Matrix ι ι ℂ) : kL (g * g') = kL g * kL g' :=
  ContinuousLinearMap.ext fun v => (crd ι).injective (by
    rw [ContinuousLinearMap.mul_apply, crd_kL, crd_kL, crd_kL, mulVec_mulVec])

omit [DecidableEq ι] in
theorem continuous_kL : Continuous (kL : Matrix ι ι ℂ → _) := by
  refine continuous_clm_apply.2 fun v => ?_
  exact (crd ι).symm.continuous.comp (continuous_id.matrix_mulVec continuous_const)

theorem norm_kL {g : Matrix ι ι ℂ} (hg : gᴴ * g = 1) (v : EuclideanSpace ℂ ι) : ‖kL g v‖ = ‖v‖ := by
  have := form_mulVec 1 g (crd ι v) (crd ι v)
  rw [mul_one, hg, one_mulVec, one_mulVec] at this
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_crd, inner_crd, crd_kL, this]

def cplx (s : Matrix ι ι ℂ) (h1 : sᴴ = s) (h2 : s * s = 1) : EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι :=
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := (kL (I • s) : EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
      norm_map' := norm_kL (by
        rw [conjTranspose_smul, h1, smul_mul_smul_comm, h2]
        simp) } rfl

theorem crd_cplx (s : Matrix ι ι ℂ) (h1 : sᴴ = s) (h2 : s * s = 1) (v : EuclideanSpace ℂ ι) :
    crd ι (cplx s h1 h2 v) = I • s *ᵥ crd ι v := by
  rw [← smul_mulVec]
  exact crd_kL (I • s) v

theorem cplx_cplx (s : Matrix ι ι ℂ) (h1 : sᴴ = s) (h2 : s * s = 1) (v : EuclideanSpace ℂ ι) :
    cplx s h1 h2 (cplx s h1 h2 v) = -v := by
  apply (crd ι).injective
  rw [crd_cplx, crd_cplx, mulVec_smul, mulVec_mulVec, h2, one_mulVec, smul_smul, I_mul_I, map_neg, neg_one_smul]

theorem omJ_cplx (s : Matrix ι ι ℂ) (h1 : sᴴ = s) (h2 : s * s = 1) (x y : EuclideanSpace ℂ ι) :
    omJ (cplx s h1 h2) x y = (star (crd ι y) ⬝ᵥ s *ᵥ crd ι x).im := by
  rw [omJ_skew (cplx_cplx s h1 h2), omJ, inner_crd, crd_cplx, dotProduct_smul]
  simp

def uGrp (H : Matrix ι ι ℂ) : Subgroup (Matrix ι ι ℂ)ˣ where
  carrier := {g | (g : Matrix ι ι ℂ)ᴴ * H * g = H}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, conjTranspose_mul] at ha hb ⊢
    calc _ = (b : Matrix ι ι ℂ)ᴴ * ((a : Matrix ι ι ℂ)ᴴ * H * a) * b := by simp only [mul_assoc]
      _ = H := by rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    calc _ = ((a⁻¹ : (Matrix ι ι ℂ)ˣ) : Matrix ι ι ℂ)ᴴ * ((a : Matrix ι ι ℂ)ᴴ * H * a) * (a⁻¹ : (Matrix ι ι ℂ)ˣ) := by
          rw [ha]
      _ = ((a : Matrix ι ι ℂ) * (a⁻¹ : (Matrix ι ι ℂ)ˣ).1)ᴴ * H * ((a : Matrix ι ι ℂ) * (a⁻¹ : (Matrix ι ι ℂ)ˣ).1) := by
          simp only [mul_assoc, conjTranspose_mul]
      _ = H := by simp

def kU (H : Matrix ι ι ℂ) : uGrp H →* (EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι) where
  toFun g := kL (g.1 : Matrix ι ι ℂ)
  map_one' := kL_one
  map_mul' _ _ := kL_mul _ _

theorem exists_osc_involution (H : Matrix ι ι ℂ) (h1 : Hᴴ = H) (h2 : H * H = 1) (B : Type) [NormedAddCommGroup B]
    [NormedSpace ℂ B] [CompleteSpace B] (ρ : (ι → ℂ) → B →L[ℂ] B) (hρ : IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ)
    (G : Type) [Group G] (m : G →* Matrix ι ι ℂ) (hm : ∀ g, (m g)ᴴ * H * m g = H) :
    ∃ Ω : G → B → B, IsOsc ρ (fun g v => m g *ᵥ v) Ω ∧ (∀ g, m g = 1 → ∀ f, Sm ρ f → Ω g f = f) ∧
      (∀ [TopologicalSpace G], Continuous m → ∀ f, Sm ρ f → Continuous fun g => Ω g f) ∧
      ∀ (s : Matrix ι ι ℂ) (g : G), s * s = 1 → (H * s).PosDef → s * m g = m g * s → ∀ f, Sm ρ f →
        (∀ z, fderiv ℝ (fun v => ρ v f) 0 z + I • fderiv ℝ (fun v => ρ v f) 0 (I • s *ᵥ z) = 0) →
        Ω g f = dP s (m g) • f := by
  have hJ := cplx_cplx H h1 h2
  have hρ' : IsHeis (omJ (cplx H h1 h2)) fun v => ρ (crd ι v) :=
    isHeis_comp hρ (crd ι : EuclideanSpace ℂ ι →L[ℝ] (ι → ℂ)) fun x y => (omJ_cplx H h1 h2 x y).symm
  obtain ⟨hl, hmu⟩ := GlobalTheory.T.gaussianPairing_unitaryGroup_two_three (EuclideanSpace ℂ ι) ι (crd ι) norm_sq_crd H h1 h2 (cplx H h1 h2) (crd_cplx H h1 h2)
  have hom : ∀ (g : uGrp H) x y, omJ (cplx H h1 h2) (kU H g x) (kU H g y) = omJ (cplx H h1 h2) x y := by
    intro g x y
    have hg : (g.1 : Matrix ι ι ℂ)ᴴ * H * g.1 = H := g.2
    rw [omJ_cplx, omJ_cplx]
    change (star (crd ι (kL _ y)) ⬝ᵥ H *ᵥ crd ι (kL _ x)).im = _
    rw [crd_kL, crd_kL, form_mulVec, hg]
  obtain ⟨Ω, hΩ, hc, hv⟩ := GlobalTheory.T.exists_oscillatorAction_of_gaussianPairings (EuclideanSpace ℂ ι) B (cplx H h1 h2) _ hJ hρ' (uGrp H) (kU H)
    (fun g => dP H (g.1 : Matrix ι ι ℂ)) hom (detPlus_one₂ H)
    (fun g => by
      obtain ⟨e1, e2, e3⟩ := hl (g.1 : Matrix ι ι ℂ) (kU H g) g.2 (crd_kL _)
      have : star (dP H (g.1 : Matrix ι ι ℂ)) ≠ 0 := star_ne_zero.2 e1
      rw [e3, e2]
      field_simp)
    (fun g g' => by
      obtain ⟨e1, e2, e3⟩ := hl ((g * g').1 : Matrix ι ι ℂ) (kU H (g * g')) (g * g').2 (crd_kL _)
      have e4 := (hl (g.1 : Matrix ι ι ℂ) (kU H g) g.2 (crd_kL _)).1
      have e5 := (hl (g'.1 : Matrix ι ι ℂ) (kU H g') g'.2 (crd_kL _)).1
      have : star (dP H ((g * g').1 : Matrix ι ι ℂ)) ≠ 0 := star_ne_zero.2 e1
      have e6 : (g.1 : Matrix ι ι ℂ)⁻¹ * ((g * g').1 : Matrix ι ι ℂ) = g'.1 := by
        rw [← Matrix.coe_units_inv, Subgroup.coe_mul, Units.val_mul, Units.inv_mul_cancel_left]
      rw [hmu ((g * g').1 : Matrix ι ι ℂ) (g.1 : Matrix ι ι ℂ) (kU H (g * g')) (kU H g) (g * g').2 g.2 (crd_kL _)
        (crd_kL _), e3, e2, e6]
      field_simp)
  let φ : G →* uGrp H := m.toHomUnits.codRestrict (uGrp H) hm
  have hφ : ∀ g, ((φ g).1 : Matrix ι ι ℂ) = m g := fun _ => rfl
  refine ⟨fun g => Ω (φ g), isOsc_comp (crd ι) φ (fun g v => crd_kL _ v) hΩ, fun g hg f hf => ?_,
    fun hmc f hf => ?_, fun s g hs hpos hsg f hf hD => ?_⟩
  · have : φ g = 1 := Subtype.ext (Units.ext hg)
    simp only [this]
    exact hΩ.2.2.2.1 f ((sm_comp_iff _ _ _).2 hf)
  · exact hc G φ (continuous_kL.comp hmc) ((continuous_dP H).comp hmc) f ((sm_comp_iff _ _ _).2 hf)
  · obtain ⟨a, ha, has⟩ := GlobalTheory.cartanInvolution_conj_of_posDef ι H s h1 h2 hs hpos
    have hdet : a.det ≠ 0 := by
      intro h0
      have e := congrArg Matrix.det ha
      have e' := congrArg Matrix.det h2
      rw [det_mul, h0, mul_zero] at e
      rw [det_mul, ← e, det_one] at e'
      simp at e'
    obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det a).2 hdet.isUnit
    let a' : uGrp H := ⟨u, ha⟩
    let g₀ : uGrp H := a'⁻¹ * φ g * a'
    have hg₀ : (u : Matrix ι ι ℂ) * g₀.1 = m g * u := by
      have : a' * g₀ = φ g * a' := by simp only [g₀]; group
      exact congrArg (fun x : uGrp H => (x.1 : Matrix ι ι ℂ)) this
    have hcomm : H * (g₀.1 : Matrix ι ι ℂ) = g₀.1 * H := by
      refine (Units.mul_right_inj u).1 ?_
      rw [← mul_assoc, ← mul_assoc, has, hg₀, mul_assoc, hg₀, mul_assoc, has, ← mul_assoc, ← mul_assoc, hsg]
    have hiso : (g₀.1 : Matrix ι ι ℂ)ᴴ * g₀.1 = 1 := by
      have e : (g₀.1 : Matrix ι ι ℂ)ᴴ * H * g₀.1 = H := g₀.2
      rw [mul_assoc, hcomm, ← mul_assoc] at e
      have e' := congrArg (· * H) e
      simpa only [mul_assoc, h2, mul_one] using e'
    let E : EuclideanSpace ℂ ι →L[ℝ] (ι → ℂ) := (crd ι : EuclideanSpace ℂ ι →L[ℝ] (ι → ℂ)) ∘L kU H a'
    have hE : ∀ z, E z = (u : Matrix ι ι ℂ) *ᵥ crd ι z := fun z => crd_kL _ z
    have hvac := GlobalTheory.RealWeil.proj_eq_self_of_annihilated (EuclideanSpace ℂ ι) B (cplx H h1 h2) _ hJ (hρ'.twist (kU H a') (hom a')) f
      (ContDiff.comp (g := fun v => ρ v f) hf E.contDiff) fun z => by
        have e1 := fderiv_comp_clm hf E z
        have e2 := fderiv_comp_clm hf E (cplx H h1 h2 z)
        have e3 : E (cplx H h1 h2 z) = I • s *ᵥ E z := by
          rw [hE, hE, crd_cplx, mulVec_smul, mulVec_mulVec, mulVec_mulVec, has]
        rw [e3] at e2
        have e4 := hD (E z)
        rw [← e1, ← e2] at e4
        exact e4
    have key := hv a' g₀ (norm_kL hiso) f ((sm_comp_iff _ _ _).2 hf) hvac
    have e : a' * g₀ * a'⁻¹ = φ g := by simp only [g₀]; group
    rw [e, detPlus_conj₂ hdet has hg₀] at key
    exact key

theorem exists_osc : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ), Hᴴ = H → H.det ≠ 0 → ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (ρ : (ι → ℂ) → B →L[ℂ] B), IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ → ∀ (G : Type) [Group G] (m : G →* Matrix ι ι ℂ), (∀ g, (m g)ᴴ * H * m g = H) → ∃ Ω : G → B → B, IsOsc ρ (fun g v => m g *ᵥ v) Ω ∧ (∀ g, m g = 1 → ∀ f, Sm ρ f → Ω g f = f) ∧ (∀ [TopologicalSpace G], Continuous m → ∀ f, Sm ρ f → Continuous fun g => Ω g f) ∧ ∀ (s : Matrix ι ι ℂ) (g : G), s * s = 1 → (H * s).PosDef → s * m g = m g * s → ∀ f, Sm ρ f → (∀ z, fderiv ℝ (fun v => ρ v f) 0 z + I • fderiv ℝ (fun v => ρ v f) 0 (I • s *ᵥ z) = 0) → Ω g f = dP s (m g) • f := by
  intro ι _ _ H h1 h2 B _ _ _ ρ hρ G _ m hm
  obtain ⟨R, s₀, hR, hs1, hs2, rfl⟩ := GlobalTheory.hermitian_congr_involution ι H h1 h2
  obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det R).2 hR.isUnit
  have hback : ∀ X : Matrix ι ι ℂ, (u⁻¹).1ᴴ * (u.1ᴴ * X * u.1) * (u⁻¹).1 = X := fun X =>
    calc _ = (u.1 * (u⁻¹).1)ᴴ * X * (u.1 * (u⁻¹).1) := by simp only [mul_assoc, conjTranspose_mul]
      _ = X := by simp
  let E : (ι → ℂ) ≃L[ℝ] (ι → ℂ) := ContinuousLinearEquiv.equivOfInverse (mvL (u⁻¹).1) (mvL u.1)
    (fun v => by simp) fun v => by simp
  have hE : ∀ v, E v = (u⁻¹).1 *ᵥ v := fun _ => rfl
  have hρ' : IsHeis (fun x y => (star y ⬝ᵥ s₀ *ᵥ x).im) fun v => ρ (E v) :=
    isHeis_comp hρ (E : (ι → ℂ) →L[ℝ] (ι → ℂ)) fun x y => by
      change (star ((u⁻¹).1 *ᵥ y) ⬝ᵥ _ *ᵥ (u⁻¹).1 *ᵥ x).im = _
      rw [form_mulVec, hback]
  let m' : G →* Matrix ι ι ℂ :=
    { toFun := fun g => u.1 * m g * (u⁻¹).1
      map_one' := by simp
      map_mul' := fun g g' => by simp only [map_mul, mul_assoc, Units.inv_mul_cancel_left] }
  have hm' : ∀ g, m' g = u.1 * m g * (u⁻¹).1 := fun _ => rfl
  obtain ⟨Ω, hΩ, ho, hc, hv⟩ := exists_osc_involution s₀ hs1 hs2 B _ hρ' G m' fun g => by
    calc _ = (u⁻¹).1ᴴ * ((m g)ᴴ * (u.1ᴴ * s₀ * u.1) * m g) * (u⁻¹).1 := by
          simp only [hm', mul_assoc, conjTranspose_mul]
      _ = s₀ := by rw [hm, hback]
  refine ⟨Ω, isOsc_comp E (MonoidHom.id G) (fun g v => ?_) hΩ, fun g hg f hf => ?_, fun hmc f hf => ?_,
    fun s g hs hpos hsg f hf hD => ?_⟩
  · simp only [hE, hm', MonoidHom.id_apply, mulVec_mulVec, mul_assoc, Units.inv_mul_cancel_left]
  · exact ho g (by simp [hm', hg]) f ((sm_comp_iff _ _ _).2 hf)
  · exact hc ((continuous_const.mul hmc).mul continuous_const) f ((sm_comp_iff _ _ _).2 hf)
  · have hpos' : (s₀ * (u.1 * s * (u⁻¹).1)).PosDef := by
      have := hpos.conjTranspose_mul_mul_same (B := (u⁻¹).1) (Matrix.mulVec_injective_of_isUnit (u⁻¹).isUnit)
      have e : s₀ * (u.1 * s * (u⁻¹).1) = (u⁻¹).1ᴴ * (u.1ᴴ * s₀ * u.1 * s) * (u⁻¹).1 := by
        calc _ = (u.1 * (u⁻¹).1)ᴴ * (s₀ * (u.1 * s * (u⁻¹).1)) := by simp
          _ = _ := by simp only [mul_assoc, conjTranspose_mul]
      rw [e]
      exact this
    have key := hv (u.1 * s * (u⁻¹).1) g
      (by simp only [mul_assoc, Units.inv_mul_cancel_left]; rw [← mul_assoc s, hs, one_mul, Units.mul_inv]) hpos'
      (by simp only [hm', mul_assoc, Units.inv_mul_cancel_left]; rw [← mul_assoc s, hsg, mul_assoc]) f
      ((sm_comp_iff _ _ _).2 hf) fun z => by
        have e1 := fderiv_comp_clm hf (E : (ι → ℂ) →L[ℝ] (ι → ℂ)) z
        have e2 := fderiv_comp_clm hf (E : (ι → ℂ) →L[ℝ] (ι → ℂ)) (I • (u.1 * s * (u⁻¹).1) *ᵥ z)
        have e3 : E (I • (u.1 * s * (u⁻¹).1) *ᵥ z) = I • s *ᵥ E z := by
          simp only [hE, mulVec_smul, mulVec_mulVec, mul_assoc, Units.inv_mul_cancel_left]
        simp only [ContinuousLinearEquiv.coe_coe] at e1 e2
        rw [e1, e2, e3]
        exact hD _
    rw [key, ← detPlus_conj₂ (s := s) (g := m g) hR (by simp) (by simp [hm'])]

end GlobalTheory.RealWeil.UnitaryOsc

end
end
