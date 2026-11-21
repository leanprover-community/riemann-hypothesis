import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegSqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffLinearSubstEqAbsDetSqMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationComponentEqOfSameModulusPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicLocalInverseOfInjOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameDomainCoordinatesHolomorphic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAndFderivMoebI
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtEqOfPtOfFrameEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DomainPointStabilizerTrivial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameActionUpperTriangularBlockExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundaryArcLiftNotConvergesSymmetricDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicChartOfExpChartGenericFibre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHoloCoordFrameAt

section
section
open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PointFormSign

theorem curvPoly_eq_smul_sum {n m : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) :
    curvPoly G v = ∑ a, ∑ b, (X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) •
      (curv G v (coordVec a) (coordVec b)).map C := by
  ext i j
  simp [curvPoly, Matrix.sum_apply, mul_comm]

theorem sqPoly_eq_smul_sum {n m r : ℕ} (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) :
    sqPoly T = ∑ a, ∑ b, (X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) •
      (T (coordVec a) * (T (coordVec b))ᴴ).map C := by
  refine Matrix.ext fun i j => ?_
  simp only [sqPoly, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mul_comm]

theorem curvPoly_of_negSq {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) (S : Matrix (Fin m) (Fin m) ℂ)
    (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ)
    (h : ∀ ξ η, curv G v ξ η = S⁻¹ * (-(T ξ * (T η)ᴴ)) * S) :
    curvPoly G v = S⁻¹.map C * (-(sqPoly T)) * S.map C := by
  have key : ∀ M : Matrix (Fin m) (Fin m) ℂ,
      (S⁻¹ * (-M) * S).map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) = -(S⁻¹.map C * M.map C * S.map C) := by
    intro M
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_neg _ (fun a => map_neg C a), Matrix.mul_neg, Matrix.neg_mul]
  rw [curvPoly_eq_smul_sum, sqPoly_eq_smul_sum]
  simp only [h, key]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Finset.sum_neg_distrib, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_neg]

theorem charpolyRev_neg_coeff_dim {R : Type*} [CommRing R] [Nontrivial R] {m : ℕ} (P : Matrix (Fin m) (Fin m) R) :
    (Matrix.charpolyRev (-P)).coeff m = P.det := by
  rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
    Polynomial.revAt_le le_rfl, Nat.sub_self]
  have h := Matrix.det_eq_sign_charpoly_coeff (-P)
  rw [Matrix.det_neg, Fintype.card_fin] at h
  have h2 : ((-1 : R) ^ m) * ((-1) ^ m) = 1 := by rw [← mul_pow]; simp
  calc (-P).charpoly.coeff 0 = ((-1) ^ m * (-1) ^ m) * (-P).charpoly.coeff 0 := by rw [h2, one_mul]
    _ = P.det := by rw [mul_assoc, ← h, ← mul_assoc, h2, one_mul]

theorem chernPoly_top_of_negSq {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) (S : Matrix (Fin m) (Fin m) ℂ)
    (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) (hS : IsUnit S.det)
    (h : ∀ ξ η, curv G v ξ η = S⁻¹ * (-(T ξ * (T η)ᴴ)) * S) :
    chernPoly G v m = (-1) ^ m * (sqPoly T).det := by
  rw [chernPoly, charpolyRev_neg_coeff_dim, curvPoly_of_negSq G v S T h, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_neg, Fintype.card_fin]
  have h1 : (S⁻¹.map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ)).det * (S.map C).det = 1 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det, ← map_mul,
      ← Matrix.det_mul, Matrix.nonsing_inv_mul _ hS, Matrix.det_one, map_one]
  calc (S⁻¹.map C).det * ((-1) ^ m * (sqPoly T).det) * (S.map C).det
      = ((S⁻¹.map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ)).det * (S.map C).det) * ((-1) ^ m * (sqPoly T).det) := by ring
    _ = (-1) ^ m * (sqPoly T).det := by rw [h1, one_mul]

end GlobalTheory.PointFormSign
end
end

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernFormPolyCoeff_top_of_neg_hermitianSquare : ∀ {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) (S : Matrix (Fin m) (Fin m) ℂ)
    (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ), IsUnit S.det →
    (∀ ξ η, curv G v ξ η = S⁻¹ * (-(T ξ * (T η)ᴴ)) * S) → chernPoly G v m = (-1) ^ m * (sqPoly T).det := by
  atlas_forward_decl GlobalTheory.PointFormSign.chernPoly_top_of_negSq
end

section
section
set_option autoImplicit false

noncomputable section

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

namespace GlobalTheory.PointFormSign.TopPos

open GlobalTheory.GoodMetric.LinSubst

variable {n : ℕ}

def pairForm (u v : Fin n → ℂ) : MvPolynomial (Fin n × Fin n) ℂ :=
  ∑ p : Fin n × Fin n, C (u p.1 * starRingEnd ℂ (v p.2)) * X p

theorem topCoeff_prod_pairForm_fin (k : ℕ) :
    ∃ D : (Fin k → Fin n → ℂ) → ℂ, ∀ u v : Fin k → Fin n → ℂ,
      topCoeff (∏ j, pairForm (u j) (v j)) = D u * starRingEnd ℂ (D v) := by
  by_cases hk : k = n
  · subst hk
    refine ⟨fun u => (Matrix.of u).det, fun u v => ?_⟩
    simp only [pairForm]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
    simp_rw [Finset.prod_mul_distrib, ← map_prod, topCoeff_C_mul]
    rw [← (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Fin k) (fun _ => Fin k)).symm.sum_comp,
      Fintype.sum_prod_type]
    simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk]
    simp_rw [topCoeff_prod_X_pair]
    have key : ∀ (c d : Fin k → Fin k),
        (∏ i, u i (c i) * starRingEnd ℂ (v i (d i))) * ((rowSel c).det * (rowSel d).det) =
        ((∏ i, (Matrix.of u) i (c i)) * (rowSel c).det) *
        ((∏ i, ((Matrix.of v).map (starRingEnd ℂ)) i (d i)) * (rowSel d).det) := by
      intro c d
      simp only [Matrix.of_apply, Matrix.map_apply, Finset.prod_mul_distrib]
      ring
    rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => key c d, ← Finset.sum_mul_sum,
      sum_prod_mul_det_rowSel, sum_prod_mul_det_rowSel, RingHom.map_det]
    rfl
  · refine ⟨fun _ => 0, fun u v => ?_⟩
    simp only [pairForm]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
    simp_rw [Finset.prod_mul_distrib, ← map_prod, topCoeff_C_mul]
    simp [topCoeff_prod_X_of_ne hk]

theorem topCoeff_prod_pairForm (J : Type) [Fintype J] :
    ∃ D : (J → Fin n → ℂ) → ℂ, ∀ u v : J → Fin n → ℂ,
      topCoeff (∏ j, pairForm (u j) (v j)) = D u * starRingEnd ℂ (D v) := by
  obtain ⟨D, hD⟩ := topCoeff_prod_pairForm_fin (n := n) (Fintype.card J)
  let e := (Fintype.equivFin J).symm
  refine ⟨fun u => D (u ∘ e), fun u v => ?_⟩
  rw [← hD, ← e.prod_comp]
  rfl

theorem factorial_mul_det {R : Type} [CommRing R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R) :
    (m.factorial : R) * M.det = ∑ σ : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m),
      ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R) * ∏ i, M (σ i) (τ i) := by
  rw [Finset.sum_comm]
  have h (τ : Equiv.Perm (Fin m)) : ∑ σ : Equiv.Perm (Fin m),
      ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R) * ∏ i, M (σ i) (τ i) = M.det := by
    have h1 := Matrix.det_permute' τ M
    rw [Matrix.det_apply'] at h1
    have h2 : ((Equiv.Perm.sign τ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
      simp
    calc _ = ((Equiv.Perm.sign τ : ℤ) : R) * ∑ σ : Equiv.Perm (Fin m),
          ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, (M.submatrix id τ) (σ i) i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun σ _ => ?_
          simp only [Matrix.submatrix_apply, id]
          ring
      _ = M.det := by rw [h1, ← mul_assoc, h2, one_mul]
  simp_rw [h]
  simp [Fintype.card_perm]

theorem sqPoly_apply {m r : ℕ} (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) (i j : Fin m) :
    sqPoly T i j = ∑ k, pairForm (fun a => T (coordVec a) i k) (fun a => T (coordVec a) j k) := by
  simp only [sqPoly, pairForm, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum,
    Finset.sum_mul, Fintype.sum_prod_type]
  rw [Finset.sum_comm (γ := Fin r)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm (γ := Fin r)]
  rfl

theorem factorial_mul_det_sqPoly {m r : ℕ} (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) :
    C (m.factorial : ℂ) * (sqPoly T).det = ∑ k : Fin m → Fin r, ∑ σ : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m),
      C (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) *
        ∏ i, pairForm (fun a => T (coordVec a) (σ i) (k i)) (fun a => T (coordVec a) (τ i) (k i)) := by
  rw [map_natCast, factorial_mul_det]
  simp_rw [sqPoly_apply, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  rw [Finset.sum_comm (γ := Fin m → Fin r)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm (γ := Fin m → Fin r)]
  simp only [map_mul, map_intCast]

theorem topCoeff_prod_det_nonneg {B : Type} [Fintype B] (m r : B → ℕ)
    (T : ∀ b, V n →ₗ[ℂ] Matrix (Fin (m b)) (Fin (r b)) ℂ) :
    0 ≤ topCoeff (∏ b, (sqPoly (T b)).det) := by
  classical
  obtain ⟨D, hD⟩ := topCoeff_prod_pairForm (n := n) (Σ b, Fin (m b))
  have h : (∏ b, ((m b).factorial : ℂ)) * topCoeff (∏ b, (sqPoly (T b)).det) =
      ∑ k : ∀ b, Fin (m b) → Fin (r b),
        (∑ σ : ∀ b, Equiv.Perm (Fin (m b)), (∏ b, ((Equiv.Perm.sign (σ b) : ℤ) : ℂ)) *
          D fun j a => T j.1 (coordVec a) (σ j.1 j.2) (k j.1 j.2)) *
        starRingEnd ℂ (∑ σ : ∀ b, Equiv.Perm (Fin (m b)), (∏ b, ((Equiv.Perm.sign (σ b) : ℤ) : ℂ)) *
          D fun j a => T j.1 (coordVec a) (σ j.1 j.2) (k j.1 j.2)) := by
    rw [← topCoeff_C_mul, map_prod, ← Finset.prod_mul_distrib]
    simp_rw [factorial_mul_det_sqPoly]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.prod_mul_distrib, ← map_prod, topCoeff_C_mul, ← Fintype.prod_sigma', hD, Finset.prod_mul_distrib]
    simp only [map_mul, map_prod, map_intCast]
    ring
  have h0 : 0 ≤ (∏ b, ((m b).factorial : ℂ)) * topCoeff (∏ b, (sqPoly (T b)).det) := by
    rw [h]
    exact Finset.sum_nonneg fun k _ => mul_star_self_nonneg _
  have hN : (0 : ℝ) < ∏ b, ((m b).factorial : ℝ) :=
    Finset.prod_pos fun b _ => by exact_mod_cast Nat.factorial_pos _
  have e : (∏ b, ((m b).factorial : ℂ)) = ((∏ b, ((m b).factorial : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [e] at h0
  have h1 : (0 : ℂ) ≤ (((∏ b, ((m b).factorial : ℝ))⁻¹ : ℝ) : ℂ) := Complex.zero_le_real.2 (inv_nonneg.2 hN.le)
  have h2 := mul_nonneg h1 h0
  rwa [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hN.ne', Complex.ofReal_one, one_mul] at h2

end GlobalTheory.PointFormSign.TopPos

theorem GlobalTheory.PointFormSign.topCoeff_prod_det_sqPoly_pow_nonneg {n : ℕ} {κ : Type} [Fintype κ] (m r e : κ → ℕ)
    (T : ∀ t, V n →ₗ[ℂ] Matrix (Fin (m t)) (Fin (r t)) ℂ) :
    0 ≤ topCoeff (∏ t, (sqPoly (T t)).det ^ e t) := by
  have h := TopPos.topCoeff_prod_det_nonneg (B := Σ t, Fin (e t)) (fun b => m b.1) (fun b => r b.1) fun b => T b.1
  rw [Fintype.prod_sigma] at h
  refine h.trans_eq (congrArg topCoeff (Finset.prod_congr rfl fun t _ => ?_))
  exact (Finset.prod_const (s := Finset.univ) (sqPoly (T t)).det).trans (by rw [Finset.card_univ, Fintype.card_fin])
end
end

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDegreeFormCoeff_prod_det_hermitianSquare_pow_nonneg : ∀ {n : ℕ} {κ : Type} [Fintype κ] (m r e : κ → ℕ) (T : ∀ t, V n →ₗ[ℂ] Matrix (Fin (m t)) (Fin (r t)) ℂ),
    0 ≤ topCoeff (∏ t, (sqPoly (T t)).det ^ e t) := by
  atlas_forward_decl GlobalTheory.PointFormSign.topCoeff_prod_det_sqPoly_pow_nonneg
end

section
section
open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PointFormSign.DomCurv

section Sqrt

open scoped MatrixOrder

theorem exists_eq_conjTranspose_mul_self {k : ℕ} {T : Matrix (Fin k) (Fin k) ℂ}
    (hT : T.PosSemidef) : ∃ B : Matrix (Fin k) (Fin k) ℂ, T = Bᴴ * B := by
  have h0 : 0 ≤ T := Matrix.nonneg_iff_posSemidef.mpr hT
  have hs : (CFC.sqrt T).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg T)
  exact ⟨CFC.sqrt T, by rw [hs.1.eq, CFC.sqrt_mul_sqrt_self T h0]⟩

end Sqrt

variable {m r : ℕ}

def domForm (m r : ℕ) (x : Fin m → Fin r → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  1 - Matrix.of x * (Matrix.of x)ᴴ

theorem domGram_eq (x : Fin m → Fin r → ℂ) : domGram m r x = ((domForm m r x)⁻¹)ᵀ := rfl

theorem mContDiffAt_of (k : WithTop ℕ∞) (y : Fin m → Fin r → ℂ) :
    MContDiffAt k (fun y : Fin m → Fin r → ℂ => Matrix.of y) y := fun a b => by
  show ContDiffAt ℝ k (fun x : Fin m → Fin r → ℂ => x a b) y
  exact ((contDiff_apply ℝ ℂ b).comp (contDiff_apply ℝ (Fin r → ℂ) a)).contDiffAt

theorem mdel_of (y ξ : Fin m → Fin r → ℂ) :
    mdel (fun y : Fin m → Fin r → ℂ => Matrix.of y) y ξ = Matrix.of ξ := by
  ext a b
  show del (fun x : Fin m → Fin r → ℂ => x a b) y ξ = ξ a b
  have e : (fun x : Fin m → Fin r → ℂ => x a b) =
      ⇑((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) b).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => Fin r → ℂ) a)) := rfl
  rw [e, del_eq_fderiv (ContinuousLinearMap.differentiableAt _), ContinuousLinearMap.fderiv]
  rfl

theorem mdbar_of (y η : Fin m → Fin r → ℂ) :
    mdbar (fun y : Fin m → Fin r → ℂ => Matrix.of y) y η = 0 := by
  ext a b
  show dbar (fun x : Fin m → Fin r → ℂ => x a b) y η = 0
  have e : (fun x : Fin m → Fin r → ℂ => x a b) =
      ⇑((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) b).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => Fin r → ℂ) a)) := rfl
  rw [e, dbar_eq_zero (ContinuousLinearMap.differentiableAt _)]
  rfl

theorem mContDiffAt_domForm (k : WithTop ℕ∞) (y : Fin m → Fin r → ℂ) :
    MContDiffAt k (domForm m r) y :=
  (mContDiffAt_const 1).sub ((mContDiffAt_of k y).mul (mContDiffAt_of k y).conjTranspose)

theorem domForm_eq_fun : domForm m r = fun y => 1 + -(Matrix.of y * (Matrix.of y)ᴴ) := by
  funext y; simp [domForm, sub_eq_add_neg]

theorem mdel_domForm (y ξ : Fin m → Fin r → ℂ) :
    mdel (domForm m r) y ξ = -(Matrix.of ξ * (Matrix.of y)ᴴ) := by
  have h1 := mContDiffAt_of (m := m) (r := r) 1 y
  rw [domForm_eq_fun, mdel_add (mContDiffAt_const _) (h1.mul h1.conjTranspose).neg, mdel_const,
    mdel_neg, mdel_mul h1 h1.conjTranspose, mdel_conjTranspose, mdbar_of, mdel_of]
  simp

theorem mdbar_domForm (y η : Fin m → Fin r → ℂ) :
    mdbar (domForm m r) y η = -(Matrix.of y * (Matrix.of η)ᴴ) := by
  have h1 := mContDiffAt_of (m := m) (r := r) 1 y
  rw [domForm_eq_fun, mdbar_add (mContDiffAt_const _) (h1.mul h1.conjTranspose).neg, mdbar_const,
    mdbar_neg, mdbar_mul h1 h1.conjTranspose, mdbar_conjTranspose, mdbar_of, mdel_of]
  simp

theorem conn_domGram {y : Fin m → Fin r → ℂ} (hu : IsUnit (domForm m r y).det)
    (ξ : Fin m → Fin r → ℂ) :
    conn (domGram m r) y ξ = Matrix.of ξ * ((Matrix.of y)ᴴ * (domForm m r y)⁻¹) := by
  have e : (fun x => (domGram m r x)ᵀ) = fun x => (domForm m r x)⁻¹ := by
    funext x; rw [domGram_eq, transpose_transpose]
  have e2 : (domGram m r y)ᵀ = (domForm m r y)⁻¹ := congrFun e y
  rw [conn, e2, ← mdel_transpose, e, mdel_inv (mContDiffAt_domForm 1 y) hu, mdel_domForm,
    nonsing_inv_nonsing_inv _ hu]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc,
    mul_nonsing_inv_cancel_left _ _ hu]

theorem curv_domGram_eq {x : Fin m → Fin r → ℂ} (hx : IsUnit (domForm m r x).det)
    (ξ η : Fin m → Fin r → ℂ) :
    curv (domGram m r) x ξ η = -(Matrix.of ξ * ((1 + (Matrix.of x)ᴴ * (domForm m r x)⁻¹ *
      Matrix.of x) * ((Matrix.of η)ᴴ * (domForm m r x)⁻¹))) := by
  have hev := (mContDiffAt_domForm (m := m) (r := r) 1 x).eventually_isUnit hx
  have he : (fun y => conn (domGram m r) y ξ) =ᶠ[𝓝 x]
      fun y => Matrix.of ξ * ((Matrix.of y)ᴴ * (domForm m r y)⁻¹) :=
    hev.mono fun y hy => conn_domGram hy ξ
  have hZ := mContDiffAt_of (m := m) (r := r) 1 x
  have hM := (mContDiffAt_domForm (m := m) (r := r) 1 x).inv hx
  rw [curv, mdbar_congr he, mdbar_mul (mContDiffAt_const (Matrix.of ξ)) (hZ.conjTranspose.mul hM),
    mdbar_const, mdbar_mul hZ.conjTranspose hM, mdbar_inv (mContDiffAt_domForm 1 x) hx,
    mdbar_domForm, mdbar_conjTranspose, mdel_of]
  simp only [Matrix.zero_mul, add_zero, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.add_mul,
    Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_add]
  rw [add_comm]

end GlobalTheory.PointFormSign.DomCurv

namespace GlobalTheory.PointFormSign

open DomCurv in

theorem curv_domGram_isNegSq (m r : ℕ) (x : Fin m → Fin r → ℂ)
    (hx : (1 - Matrix.of x * (Matrix.of x)ᴴ).PosDef) : IsNegSq (curv (domGram m r) x) r := by
  have hxA : (domForm m r x).PosDef := hx
  have hu : IsUnit (domForm m r x).det := (isUnit_iff_isUnit_det _).1 hxA.isUnit
  have hM := hxA.inv
  obtain ⟨B, hB⟩ := exists_eq_conjTranspose_mul_self hM.posSemidef
  have hQ : (1 + (Matrix.of x)ᴴ * (domForm m r x)⁻¹ * Matrix.of x).PosSemidef :=
    (PosDef.one.add_posSemidef (hM.posSemidef.conjTranspose_mul_mul_same (Matrix.of x))).posSemidef
  obtain ⟨C, hC⟩ := exists_eq_conjTranspose_mul_self hQ
  have hBu : IsUnit B.det := by
    have h1 : IsUnit (Bᴴ * B).det := by rw [← hB]; exact (isUnit_iff_isUnit_det _).1 hM.isUnit
    rw [det_mul] at h1
    exact isUnit_of_mul_isUnit_right h1
  let T : (Fin m → Fin r → ℂ) →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ :=
    { toFun := fun ξ => B * Matrix.of ξ * Cᴴ
      map_add' := fun ξ ξ' => by
        show B * Matrix.of (ξ + ξ') * Cᴴ = B * Matrix.of ξ * Cᴴ + B * Matrix.of ξ' * Cᴴ
        rw [← Matrix.of_add_of, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c ξ => by
        show B * (c • Matrix.of ξ) * Cᴴ = c • (B * Matrix.of ξ * Cᴴ)
        rw [Matrix.mul_smul, Matrix.smul_mul] }
  refine ⟨B, T, hBu, fun ξ η => ?_⟩
  rw [curv_domGram_eq hu, hC, hB]
  show -(Matrix.of ξ * ((Cᴴ * C) * ((Matrix.of η)ᴴ * (Bᴴ * B)))) =
    B⁻¹ * (-((B * Matrix.of ξ * Cᴴ) * (B * Matrix.of η * Cᴴ)ᴴ)) * B
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hBu]

end GlobalTheory.PointFormSign
end
end

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNegHermitianSquare_curvature_boundedDomainHodgeGram : ∀ (m r : ℕ) (x : Fin m → Fin r → ℂ), (1 - Matrix.of x * (Matrix.of x)ᴴ).PosDef →
    IsNegSq (curv (domGram m r) x) r := by
  atlas_forward_decl GlobalTheory.PointFormSign.curv_domGram_isNegSq
end

section
section
set_option autoImplicit false

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

namespace GlobalTheory.PointFormSign

theorem mContDiffAt_domGram {m r : ℕ} {k : WithTop ℕ∞} (x : Fin m → Fin r → ℂ)
    (hx : IsUnit (1 - Matrix.of x * (Matrix.of x)ᴴ).det) : MContDiffAt k (domGram m r) x := by
  have h : MContDiffAt k (fun y : Fin m → Fin r → ℂ => Matrix.of y) x := fun a b => by
    simp only [Matrix.of_apply]
    fun_prop
  exact (((mContDiffAt_const 1).sub (h.mul h.conjTranspose)).inv hx).transpose

theorem isUnit_det_domGram {m r : ℕ} (x : Fin m → Fin r → ℂ)
    (hx : IsUnit (1 - Matrix.of x * (Matrix.of x)ᴴ).det) : IsUnit (domGram m r x).det := by
  rw [domGram, det_transpose]
  exact isUnit_nonsing_inv_det _ hx

theorem isNegSq_curv_of_changeFrame_comp {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n)
    (W : V n → Matrix (Fin m) (Fin m) ℂ) (Z : V n → (Fin m → Fin r → ℂ)) (κ : ℝ) (hκ : 0 < κ)
    (hG : ∀ᶠ u in 𝓝 v, G u = (κ : ℂ) • ((W u)ᵀ * domGram m r (Z u) * (W u)ᴴᵀ))
    (hZ : ∀ᶠ u in 𝓝 v, DifferentiableAt ℂ Z u)
    (hW : ∀ i j, ∀ᶠ u in 𝓝 v, DifferentiableAt ℂ (fun u => W u i j) u)
    (hWu : IsUnit (W v).det) (hpos : (1 - Matrix.of (Z v) * (Matrix.of (Z v))ᴴ).PosDef)
    (hneg : IsNegSq (curv (domGram m r) (Z v)) r) : IsNegSq (curv G v) r := by
  obtain ⟨S, T, hS, hF⟩ := hneg
  have hu : IsUnit (1 - Matrix.of (Z v) * (Matrix.of (Z v))ᴴ).det :=
    (isUnit_iff_isUnit_det _).1 hpos.isUnit
  have hD2 : MContDiffAt 2 (domGram m r) (Z v) := mContDiffAt_domGram _ hu
  have hDu : IsUnit (domGram m r (Z v)).det := isUnit_det_domGram _ hu
  have hZ2 : ContDiffAt ℂ 2 Z v := (GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 hZ).contDiffAt
  have hW2 : MContDiffAt 2 W v := fun i j =>
    ((GlobalTheory.SCV.analyticAt_iff_eventually_differentiableAt.2 (hW i j)).contDiffAt (n := 2)).restrict_scalars ℝ
  have hW0 : ∀ᶠ x in 𝓝 v, ∀ η, mdbar W x η = 0 := by
    filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => hW i j]
      with x hx η
    ext a b
    rw [mdbar_apply, GlobalTheory.dbar_eq_zero (hx a b)]
    rfl
  have hH2 : MContDiffAt 2 (fun x => domGram m r (Z x)) v :=
    fun a b => (hD2 a b).comp v (hZ2.restrict_scalars ℝ)
  have hK2 : MContDiffAt 2 (fun u => (W u)ᵀ * domGram m r (Z u) * (W u)ᴴᵀ) v :=
    (hW2.transpose.mul hH2).mul hW2.conjTranspose.transpose
  have hKu : IsUnit ((W v)ᵀ * domGram m r (Z v) * (W v)ᴴᵀ).det := by
    simp only [det_mul, det_transpose, det_conjTranspose]
    exact (hWu.mul hDu).mul hWu.star
  refine ⟨S * W v, T ∘ₗ (fderiv ℂ Z v).toLinearMap, by rw [det_mul]; exact hS.mul hWu, fun ξ η => ?_⟩
  rw [curv_congr hG, curv_smul (f := fun _ => κ) contDiffAt_const hκ.ne' hK2 hKu, leviForm_const,
    curv_changeFrame (H := fun x => domGram m r (Z x)) hH2 hDu hW2 hWu hW0,
    curv_comp_holo hD2 hDu hZ2, hF, Matrix.mul_inv_rev]
  simp [Matrix.mul_assoc]

end GlobalTheory.PointFormSign
end

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNegHermitianSquare_curvature_of_holomorphic_frameChange : ∀ {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) (W : V n → Matrix (Fin m) (Fin m) ℂ)
    (Z : V n → (Fin m → Fin r → ℂ)) (κ : ℝ), 0 < κ →
    (∀ᶠ u in 𝓝 v, G u = (κ : ℂ) • ((W u)ᵀ * domGram m r (Z u) * (W u)ᴴᵀ)) →
    (∀ᶠ u in 𝓝 v, DifferentiableAt ℂ Z u) → (∀ i j, ∀ᶠ u in 𝓝 v, DifferentiableAt ℂ (fun u => W u i j) u) →
    IsUnit (W v).det → (1 - Matrix.of (Z v) * (Matrix.of (Z v))ᴴ).PosDef →
    IsNegSq (curv (domGram m r) (Z v)) r → IsNegSq (curv G v) r := by
  atlas_forward_decl GlobalTheory.PointFormSign.isNegSq_curv_of_changeFrame_comp
end

section
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_local_inverse_of_injOn : ∀ (n : ℕ) (W : Set (V n)) (g : V n → V n) (a : V n), IsOpen W → a ∈ W → DifferentiableOn ℂ g W → Set.InjOn g W → ∃ h : V n → V n, ∀ᶠ u in 𝓝 (g a), h u ∈ W ∧ g (h u) = u ∧ DifferentiableAt ℂ h u := by
  first | exact @GlobalTheory.InjHol.exists_local_inverse_of_injOn | exact GlobalTheory.InjHol.exists_local_inverse_of_injOn | (intros; apply GlobalTheory.InjHol.exists_local_inverse_of_injOn <;> assumption)
end

section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_setOf_lact_eq_rmul_blockTriangular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (K : Set (ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)), IsCompact K → K ⊆ X.dom → {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ x ∈ K, ∃ y ∈ K, ∃ b : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r, (∀ τ, (ReciprocityTheory.ChartRestriction.G.FD.mat b τ).det ≠ 0) ∧ (∀ τ (a c : Fin r), (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → b τ a c = 0) ∧ ReciprocityTheory.ChartRestriction.G.FD.lact γ x = ReciprocityTheory.ChartRestriction.G.FD.rmul y b}.Finite := by
  first | exact @GlobalTheory.BlockTransporter.finite_blockTransporter | exact GlobalTheory.BlockTransporter.finite_blockTransporter | (intros; apply GlobalTheory.BlockTransporter.finite_blockTransporter <;> assumption)
end

section
section
open NumberField

open Matrix Formalism.DegreeFormula Formalism.MJ Formalism.UG ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.TrueCx Topology Filter

noncomputable section

namespace GlobalTheory.LocInj

variable {ι : Type} [Fintype ι] {p q : ℕ}

theorem isOpen_domI : IsOpen (DomI ι p q) := by
  have hc : Continuous (flat : (ι → Matrix (Fin p) (Fin q) ℂ) → ι × Fin p × Fin q → ℂ) :=
    continuous_pi fun x => (continuous_apply x.1).matrix_elem x.2.1 x.2.2
  exact GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat.preimage hc

theorem continuousAt_moeb (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ)
    (hu : IsUnit (M.toBlocks₂₁ * z + M.toBlocks₂₂).det) :
    ContinuousAt (fun w : Matrix (Fin p) (Fin q) ℂ => moeb M w) z := by
  unfold moeb
  set A := M.toBlocks₁₁
  set B := M.toBlocks₁₂
  set C := M.toBlocks₂₁
  set D := M.toBlocks₂₂
  have h1 : Continuous (fun w : Matrix (Fin p) (Fin q) ℂ => A * w + B) :=
    (continuous_const.matrix_mul continuous_id).add continuous_const
  have h2 : Continuous (fun w : Matrix (Fin p) (Fin q) ℂ => C * w + D) :=
    (continuous_const.matrix_mul continuous_id).add continuous_const
  have hi : ContinuousAt (Inv.inv : Matrix (Fin q) (Fin q) ℂ → Matrix (Fin q) (Fin q) ℂ) (C * z + D) := by
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hu.ne_zero
  have h3 : ContinuousAt (fun w : Matrix (Fin p) (Fin q) ℂ => (C * w + D)⁻¹) z :=
    ContinuousAt.comp (g := Inv.inv) hi h2.continuousAt
  have hm : Continuous (fun x : Matrix (Fin p) (Fin q) ℂ × Matrix (Fin q) (Fin q) ℂ => x.1 * x.2) :=
    continuous_fst.matrix_mul continuous_snd
  exact ContinuousAt.comp (g := fun x : Matrix (Fin p) (Fin q) ℂ × Matrix (Fin q) (Fin q) ℂ => x.1 * x.2)
    (f := fun w => (A * w + B, (C * w + D)⁻¹)) hm.continuousAt (h1.continuousAt.prodMk h3)

theorem continuousAt_moebI {g : ι → GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ UpqI ι p q) {z : ι → Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ DomI ι p q) : ContinuousAt (moebI g) z := by
  refine continuousAt_pi.2 fun t => ?_
  have hu := GlobalTheory.HodgeDomain.kapQ_isUnit (hg t trivial) (hz t)
  exact ContinuousAt.comp (g := fun w => moeb ((g t : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) w)
    (continuousAt_moeb _ _ hu) (continuous_apply t).continuousAt

theorem moebI_one (z : ι → Matrix (Fin p) (Fin q) ℂ) : moebI (1 : ι → GL (Fin p ⊕ Fin q) ℂ) z = z := by
  funext t
  simp [moebI, GlobalTheory.TrueCx.PointWell.moeb_one]

end GlobalTheory.LocInj

namespace GlobalTheory.LocInj

open GlobalTheory.ShFam.SecFrame

theorem continuous_frameAt {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ}
    (hj : j ≤ r) {Tau : Type} (κ : Tau ≃ X.Ψ) : Continuous (frameAt X hj κ) := by
  refine continuous_pi fun τ => ?_
  show Continuous fun z : Tau → Matrix (Fin j) (Fin (r - j)) ℂ =>
    mat (x0F X) τ * (reindex (idx hj) (idx hj)).symm (fromBlocks 1 (z (κ.symm τ)) 0 1)
  refine continuous_const.matrix_mul ?_
  simp only [reindex_symm, reindex_apply, Equiv.symm_symm]
  exact (continuous_const.matrix_fromBlocks (continuous_apply _) continuous_const continuous_const).matrix_submatrix _ _

theorem locInj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ z₀ ∈ Formalism.DegreeFormula.DomI Tau j (r - j), ∃ O : Set (Tau → Matrix (Fin j) (Fin (r - j)) ℂ), IsOpen O ∧ z₀ ∈ O ∧ ∀ z ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ z' ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ γ ∈ X.Γ, z' = Formalism.DegreeFormula.moebI (GlobalTheory.TrueCx.toUpq X hj κ γ) z → z = z' := by
  intro E _ _ _ r j X hj Tau _ κ hp z₀ hz₀
  haveI : LocallyCompactSpace (Tau → Matrix (Fin j) (Fin (r - j)) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Tau → Fin j → Fin (r - j) → ℂ))

  obtain ⟨C, hCn, hCD, hCc⟩ := local_compact_nhds (isOpen_domI.mem_nhds hz₀)
  set K := frameAt X hj κ '' C with hK
  have hKc : IsCompact K := hCc.image (continuous_frameAt X hj κ)
  have hKd : K ⊆ X.dom := by
    rintro _ ⟨z, hz, rfl⟩
    exact frameAt_mem X hj κ hp (hCD hz)
  have hS := GlobalTheory.T.finite_setOf_lact_eq_rmul_blockTriangular E r X K hKc hKd
  set S := {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ x ∈ K, ∃ y ∈ K, ∃ b : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r,
    (∀ τ, (ReciprocityTheory.ChartRestriction.G.FD.mat b τ).det ≠ 0) ∧
    (∀ τ (a c : Fin r), (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → b τ a c = 0) ∧
    ReciprocityTheory.ChartRestriction.G.FD.lact γ x = ReciprocityTheory.ChartRestriction.G.FD.rmul y b} with hSdef

  have hev : ∀ γ ∈ S, ∀ᶠ w in 𝓝 z₀ ×ˢ 𝓝 z₀, γ ≠ 1 → moebI (toUpq X hj κ γ) w.1 ≠ w.2 := by
    intro γ hγS
    by_cases h1 : γ = 1
    · exact Filter.Eventually.of_forall fun _ h => absurd h1 h
    have hne : moebI (toUpq X hj κ γ) z₀ ≠ z₀ := by
      intro h
      have hx := frameAt_mem X hj κ hp hz₀
      refine h1 (GlobalTheory.FreeOnDomain.eq_one_of_domPt_lact_eq E r j X hj Tau κ hp γ hγS.1 _ hx ?_)
      rw [domPt_lact X hj κ hp γ hx, domPt_frameAt, h]
    have hc : ContinuousAt (fun w : (Tau → Matrix (Fin j) (Fin (r - j)) ℂ) × (Tau → Matrix (Fin j) (Fin (r - j)) ℂ) =>
        moebI (toUpq X hj κ γ) w.1) (z₀, z₀) :=
      ContinuousAt.comp (g := moebI (toUpq X hj κ γ))
        (continuousAt_moebI (gammaU_le X hj κ hp ⟨γ, hγS.1, rfl⟩) hz₀) continuous_fst.continuousAt
    have hO : IsOpen {w : (Tau → Matrix (Fin j) (Fin (r - j)) ℂ) × (Tau → Matrix (Fin j) (Fin (r - j)) ℂ) |
        w.1 ≠ w.2} := isOpen_ne_fun continuous_fst continuous_snd
    have := (hc.prodMk continuous_snd.continuousAt).preimage_mem_nhds (hO.mem_nhds hne)
    rw [nhds_prod_eq] at this
    exact Filter.mem_of_superset this fun w hw _ => hw
  have hCC : C ×ˢ C ∈ 𝓝 z₀ ×ˢ 𝓝 z₀ := Filter.prod_mem_prod hCn hCn
  have hall : ∀ᶠ w in 𝓝 z₀ ×ˢ 𝓝 z₀, (fun a b => a ∈ C ∧ b ∈ C ∧ ∀ γ ∈ S, γ ≠ 1 → moebI (toUpq X hj κ γ) a ≠ b) w.1 w.2 :=
    (Filter.Eventually.and hCC ((Filter.eventually_all_finite hS).2 hev)).mono fun w h => ⟨h.1.1, h.1.2, h.2⟩
  obtain ⟨t, ht, htP⟩ := (Filter.eventually_prod_self_iff (la := 𝓝 z₀)
    (r := fun a b => a ∈ C ∧ b ∈ C ∧ ∀ γ ∈ S, γ ≠ 1 → moebI (toUpq X hj κ γ) a ≠ b)).1 hall
  refine ⟨interior t, isOpen_interior, mem_interior_iff_mem_nhds.2 ht, ?_⟩
  rintro z ⟨hzt, hzD⟩ z' ⟨hzt', hzD'⟩ γ hγ e
  obtain ⟨hzC, hzC', hmove⟩ := htP z (interior_subset hzt) z' (interior_subset hzt')
  have hx := frameAt_mem X hj κ hp hzD
  have hy := frameAt_mem X hj κ hp hzD'
  have hgx := KU.lact_dom X hγ hx
  set x := frameAt X hj κ z
  set y := frameAt X hj κ z'
  have hpt : domPt X hj κ (lact γ x) = domPt X hj κ y := by
    rw [domPt_lact X hj κ hp γ hx, domPt_frameAt, domPt_frameAt, e]
  have hblk : ∀ τ (a c : Fin r), X.p0 ≤ a → (c : ℕ) < X.p0 → ((mat y τ)⁻¹ * mat (lact γ x) τ) a c = 0 := by
    intro τ
    refine GlobalTheory.TrueCx.PointWell.block_of_moeb_eq X hj hp hy hgx τ ?_
    obtain ⟨s, rfl⟩ := κ.surjective τ
    exact (congrFun hpt s).symm
  have hγS : γ ∈ S := by
    refine ⟨hγ, x, ⟨z, hzC, rfl⟩, y, ⟨z', hzC', rfl⟩, fun τ => (mat y τ)⁻¹ * mat (lact γ x) τ, fun τ => ?_,
      fun τ a c hc ha => hblk τ a c (not_lt.1 ha) hc, ?_⟩
    · show ((mat y τ)⁻¹ * mat (lact γ x) τ).det ≠ 0
      rw [det_mul, det_nonsing_inv]
      exact mul_ne_zero (by rw [Ring.inverse_eq_inv']; exact inv_ne_zero (hy τ).1) (hgx τ).1
    · funext τ
      show mat (lact γ x) τ = mat y τ * ((mat y τ)⁻¹ * mat (lact γ x) τ)
      rw [mul_nonsing_inv_cancel_left _ _ (hy τ).1.isUnit]
  by_contra hne
  by_cases h1 : γ = 1
  · subst h1
    apply hne
    rw [e, map_one, moebI_one]
  · exact hmove γ hγS h1 e.symm

end GlobalTheory.LocInj
end
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundedDomain_arithmeticGroup_locally_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ z₀ ∈ Formalism.DegreeFormula.DomI Tau j (r - j), ∃ O : Set (Tau → Matrix (Fin j) (Fin (r - j)) ℂ), IsOpen O ∧ z₀ ∈ O ∧ ∀ z ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ z' ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ γ ∈ X.Γ, z' = Formalism.DegreeFormula.moebI (GlobalTheory.TrueCx.toUpq X hj κ γ) z → z = z' := by
  atlas_forward_decl GlobalTheory.LocInj.locInj
end

section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifSlice

open Matrix Formalism.DegreeFormula GlobalTheory.TrueCx ReciprocityTheory.ChartRestriction.G.FD

theorem locInj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ z₀ ∈ Formalism.DegreeFormula.DomI Tau j (r - j), ∃ O : Set (Tau → Matrix (Fin j) (Fin (r - j)) ℂ), IsOpen O ∧ z₀ ∈ O ∧ ∀ z ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ z' ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ γ ∈ X.Γ, z' = Formalism.DegreeFormula.moebI (GlobalTheory.TrueCx.toUpq X hj κ γ) z → z = z' := GlobalTheory.T.boundedDomain_arithmeticGroup_locally_injective

theorem domPt_rel_of_pt_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r)
    (hU : Formalism.L2.PjFree.IsUnf U) (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (k : U.Comp) {j : ℕ} (hj : j ≤ r) (hp : (U.X k).p0 = r - j) {Tau : Type} [Fintype Tau] (κ : Tau ≃ (U.X k).Ψ)
    (x x' : (U.X k).dom) (h : (U.un k x).x = (U.un k x').x) :
    ∃ γ ∈ (U.X k).Γ, domPt (U.X k) hj κ x'.1 = moebI (toUpq (U.X k) hj κ γ) (domPt (U.X k) hj κ x.1) := by
  obtain ⟨b, hb, hb0, hm, t, ht⟩ := GlobalTheory.PointOfFrames.exists_frBor U hU hσ k x (U.un k x') h
  obtain ⟨γ, hγ, b', hb', e⟩ := (hU.2.2.2.1 k k ⟨_, hm⟩ x').1 ⟨t, ht⟩
  have e' : x'.1 = rmul (lact γ (rmul x.1 b)) b' := eq_of_heq (Sigma.mk.inj e).2
  refine ⟨γ, hγ, ?_⟩
  rw [e', domPt_rmul _ hj κ hb', domPt_lact _ hj κ hp γ hm,
    GlobalTheory.PointOfFrames.domPt_rmul_block _ hj κ _ b hb (by rw [← hp]; exact hb0)]

theorem flat_unflat {ι : Type} {p q : ℕ} (v : ι × Fin p × Fin q → ℂ) : flat (unflat v) = v := by
  funext ⟨i, a, b⟩; rfl

theorem unflat_flat {ι : Type} {p q : ℕ} (z : ι → Matrix (Fin p) (Fin q) ℂ) : unflat (flat z) = z := by
  funext i; ext a b; rfl

theorem continuous_unflat {ι : Type} {p q : ℕ} :
    Continuous (unflat : (ι × Fin p × Fin q → ℂ) → ι → Matrix (Fin p) (Fin q) ℂ) :=
  continuous_pi fun _ => continuous_matrix fun _ _ => continuous_apply _

theorem exists_slice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (x₀ : (U.X k).dom) (n : ℕ), n = (U.X k).Ψ.card * (Dw.p * Dw.q) → ∃ (W : Set (V n)) (a : V n) (ψ : V n → Frame (U.X k).Ψ (Dw.p + Dw.q)), IsOpen W ∧ a ∈ W ∧ (∀ w ∈ W, ψ w ∈ (U.X k).dom) ∧ (∀ τ i i', DifferentiableOn ℂ (fun w => mat (ψ w) τ i i') W) ∧ (∀ h : ψ a ∈ (U.X k).dom, (U.un k ⟨ψ a, h⟩).x = (U.un k x₀).x) ∧ ∀ w ∈ W, ∀ w' ∈ W, ∀ (h : ψ w ∈ (U.X k).dom) (h' : ψ w' ∈ (U.X k).dom), (U.un k ⟨ψ w, h⟩).x = (U.un k ⟨ψ w', h'⟩).x → w = w' := by
  intro E _ _ _ H Dw l Xo c σ U hσ hU k x₀ n hn
  classical
  have hj : Dw.p ≤ Dw.p + Dw.q := Nat.le_add_right _ _
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by have := (hU.2.1 k).1; omega
  have hcard : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = n := by
    rw [hn, Fintype.card_prod, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin, Fintype.card_fin,
      Nat.add_sub_cancel_left]
  let f : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let L : V n ≃L[ℂ] ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) :=
    (EuclideanSpace.equiv (Fin n) ℂ).trans (LinearEquiv.funCongrLeft ℂ ℂ f).toContinuousLinearEquiv
  set z₀ := domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) x₀.1 with hz₀
  have hz₀D : z₀ ∈ DomI (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) := domPt_mem (U.X k) hj _ hp x₀.2
  obtain ⟨O, hO, hz₀O, hinj⟩ := locInj E (Dw.p + Dw.q) Dw.p (U.X k) hj (U.X k).Ψ (Equiv.refl _) hp z₀ hz₀D
  let ψ : V n → Frame (U.X k).Ψ (Dw.p + Dw.q) := fun w => SecFrame.frameAt (U.X k) hj (Equiv.refl _) (unflat (L w))
  have hdom : ∀ w, unflat (L w) ∈ DomI (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ψ w ∈ (U.X k).dom := fun w hw =>
    SecFrame.frameAt_mem (U.X k) hj _ hp hw
  have hpt : ∀ w, domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) (ψ w) = unflat (L w) := fun w => SecFrame.domPt_frameAt (U.X k) hj _ _
  refine ⟨{w | unflat (L w) ∈ O} ∩ L ⁻¹' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), L.symm (flat z₀), ψ,
    (hO.preimage (continuous_unflat.comp L.continuous)).inter
      (GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat.preimage L.continuous), ?_, fun w hw => hdom w hw.2,
    fun τ i i' => ((SecFrame.differentiable_frameAt (U.X k) hj (Equiv.refl _) τ i i').comp L.differentiable).differentiableOn,
    fun h => ?_, fun w hw w' hw' h h' e => ?_⟩
  · refine ⟨?_, ?_⟩
    · show unflat (L (L.symm (flat z₀))) ∈ O
      rw [L.apply_symm_apply, unflat_flat]; exact hz₀O
    · show unflat (L (L.symm (flat z₀))) ∈ DomI (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p)
      rw [L.apply_symm_apply, unflat_flat]; exact hz₀D
  · have e0 : domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) (ψ (L.symm (flat z₀))) = domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) x₀.1 := by
      rw [hpt, L.apply_symm_apply, unflat_flat]
    have h5 : ∀ τ, Formalism.MJ.moeb (frameCo (U.X k) hj (ψ (L.symm (flat z₀))) τ) 0 = Formalism.MJ.moeb (frameCo (U.X k) hj x₀.1 τ) 0 :=
      fun τ => congrFun e0 τ
    exact PointWell.pt_eq_of_block hU hσ k ⟨_, h⟩ x₀
      (fun τ => PointWell.block_of_moeb_eq (U.X k) hj hp h x₀.2 τ (h5 τ))
      (fun τ => PointWell.block_of_moeb_eq (U.X k) hj hp x₀.2 h τ (h5 τ).symm)
  · obtain ⟨γ, hγ, hγe⟩ := domPt_rel_of_pt_eq U hU hσ k hj hp (Equiv.refl (U.X k).Ψ) ⟨_, h⟩ ⟨_, h'⟩ e
    have hγe' : unflat (L w') = moebI (toUpq (U.X k) hj (Equiv.refl (U.X k).Ψ) γ) (unflat (L w)) := by
      rw [← hpt w', ← hpt w]; exact hγe
    have h1 := hinj _ ⟨hw.1, hw.2⟩ _ ⟨hw'.1, hw'.2⟩ γ hγ hγe'
    have h2 : L w = L w' := by rw [← flat_unflat (L w), h1, flat_unflat]
    exact L.injective h2

end GlobalTheory.UnifSlice
end
end

section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_frame_slice_componentUniformisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (x₀ : (U.X k).dom) (n : ℕ), n = (U.X k).Ψ.card * (Dw.p * Dw.q) → ∃ (W : Set (V n)) (a : V n) (ψ : V n → Frame (U.X k).Ψ (Dw.p + Dw.q)), IsOpen W ∧ a ∈ W ∧ (∀ w ∈ W, ψ w ∈ (U.X k).dom) ∧ (∀ τ i i', DifferentiableOn ℂ (fun w => mat (ψ w) τ i i') W) ∧ (∀ h : ψ a ∈ (U.X k).dom, (U.un k ⟨ψ a, h⟩).x = (U.un k x₀).x) ∧ ∀ w ∈ W, ∀ w' ∈ W, ∀ (h : ψ w ∈ (U.X k).dom) (h' : ψ w' ∈ (U.X k).dom), (U.un k ⟨ψ w, h⟩).x = (U.un k ⟨ψ w', h'⟩).x → w = w' := by
  first | exact @GlobalTheory.UnifSlice.exists_slice | exact GlobalTheory.UnifSlice.exists_slice | (intros; apply GlobalTheory.UnifSlice.exists_slice <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

namespace GlobalTheory.OpenBaseDim

theorem dim_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), (∃ y, y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j)) → ∀ k : U.Comp, X.dim = (U.X k).Ψ.card * (Dw.p * Dw.q) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _ _ X j hoi _ _ k
  haveI := hoi
  have hcard : (U.X k).Ψ.card = Module.finrank ℚ E / 2 := by
    rw [← Fintype.card_coe]; exact ReciprocityTheory.ChartRestriction.G.FD.QuadraticCoefficientForms.card_Psi (U.X k)
  obtain ⟨Uo, hUo, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.X.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (genericPoint X.X))
  have h1 := GlobalTheory.SmoothDim.ringKrullDim_affineOpen F X.X X.str X.dim inferInstance Uo hUo ⟨_, hx⟩
  have h2 := GlobalTheory.SmoothDim.ringKrullDim_affineOpen c.F (gen T.Z) (genStr T.Z) Dw.dim T.smooth (j ''ᵁ Uo)
    (hUo.image_of_isOpenImmersion j) ⟨j (genericPoint X.X), ⟨_, hx, rfl⟩⟩
  rw [ringKrullDim_eq_of_ringEquiv (j.appIso Uo).commRingCatIsoToRingEquiv, h1] at h2
  have hd : X.dim = Dw.dim := by exact_mod_cast h2
  rw [hd, Datum.dim, hcard, mul_assoc]

end GlobalTheory.OpenBaseDim
end

section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dim_openly_immersed_variety_eq_cmType_card_mul_pq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), (∃ y, y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j)) → ∀ k : U.Comp, X.dim = (U.X k).Ψ.card * (Dw.p * Dw.q) := by
  first | exact @GlobalTheory.OpenBaseDim.dim_eq | exact GlobalTheory.OpenBaseDim.dim_eq | (intros; apply GlobalTheory.OpenBaseDim.dim_eq <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase

theorem isHol_chart_framePt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), ∀ (c' : AlgChart X.str (σ.comp e.toRingHom) X.dim) (k : U.Comp) (n : ℕ) (W : Set (V n)) (ψ : V n → Frame (U.X k).Ψ (Dw.p + Dw.q)), IsOpen W → (∀ w ∈ W, ψ w ∈ (U.X k).dom) → (∀ τ i i', DifferentiableOn ℂ (fun w => mat (ψ w) τ i i') W) → ∃ q : V n → CxPts X.str (σ.comp e.toRingHom), IsOpen {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} ∧ (∀ w ∈ W, ∀ h : ψ w ∈ (U.X k).dom, (∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)) → q w ∈ c'.e.source ∧ cxOf e σ hj (q w) = cxPt T.Z (U.un k ⟨ψ w, h⟩)) ∧ DifferentiableOn ℂ (fun w => c'.e (q w)) {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U _hσ hU X j hji hj c' k n W ψ hW hψW hψd
  classical
  haveI := hji
  have hU' : Formalism.L2.Pj.IsUnf U.toPj := (Formalism.L2.PjFree.isUnf_ofPj U.toPj).1 hU
  by_cases hne : ((U.X k).dom).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    let sf : Frame (U.X k).Ψ (Dw.p + Dw.q) → (U.X k).dom := fun x =>
      if h : x ∈ (U.X k).dom then ⟨x, h⟩ else ⟨x₀, hx₀⟩
    have hsf : ∀ x (h : x ∈ (U.X k).dom), sf x = ⟨x, h⟩ := fun x h => dif_pos h
    have h1 := BdArc.Leave.isHolTo_ptC (U := U.toPj) hU' k sf fun x h => by rw [hsf x h]
    have h2 := LocLift.isHolTo_comp_hom h1 T.Z.jQ
    have hψ : DifferentiableOn ℂ ψ W :=
      differentiableOn_pi.2 fun τ => differentiableOn_pi.2 fun a => differentiableOn_pi.2 fun b => hψd τ a b
    have h3 := LocLift.isHolTo_comp h2 hW hψ hψW
    let P : V n → CxPts (genStr T.Z) σ := fun w => cxPt T.Z (U.un k (sf (ψ w)))
    have h4 : IsHolTo W fun w => (P w).1 := h3
    have hP : ∀ w, ∀ h : ψ w ∈ (U.X k).dom, cxPt T.Z (U.un k ⟨ψ w, h⟩) = P w := fun w h => by
      simp only [P, hsf _ h]
    have hc : ContinuousOn P W := GlobalTheory.TrueCx.TorHolo.continuousOn_of_isHolTo h4
    have hκ : Topology.IsOpenEmbedding (cxOf e σ hj) := isOpenEmbedding_cxOf e σ hj
    have hS : {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source,
        cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} = W ∩ P ⁻¹' (cxOf e σ hj '' c'.e.source) := by
      ext w
      constructor
      · rintro ⟨hw, h, y', hy', he⟩
        exact ⟨hw, y', hy', he.trans (hP w h)⟩
      · rintro ⟨hw, y', hy', he⟩
        exact ⟨hw, hψW w hw, y', hy', he.trans (hP w _).symm⟩
    let q : V n → CxPts X.str (σ.comp e.toRingHom) := fun w =>
      if h : ∃ y' ∈ c'.e.source, cxOf e σ hj y' = P w then h.choose else c'.e.symm 0
    have hq : ∀ w, (∃ y' ∈ c'.e.source, cxOf e σ hj y' = P w) →
        q w ∈ c'.e.source ∧ cxOf e σ hj (q w) = P w := fun w h => by
      simp only [q, dif_pos h]
      exact h.choose_spec
    refine ⟨q, ?_, fun w _ h hex => ?_, ?_⟩
    · rw [hS]
      exact hc.isOpen_inter_preimage hW (hκ.isOpenMap _ c'.e.open_source)
    · rw [hP w h] at hex ⊢
      exact hq w hex
    · rw [hS, differentiableOn_euclidean]
      intro a
      have hd := (h4 (j ''ᵁ c'.U) ((j.appIso c'.U).inv.hom (c'.x a))).2
      refine (hd.mono fun w hw => ⟨hw.1, ?_⟩).congr fun w hw => ?_
      · obtain ⟨hq1, hq2⟩ := hq w (by obtain ⟨y', hy', he⟩ := hw.2; exact ⟨y', hy', he⟩)
        show ⊤ ≤ (P w).1 ⁻¹ᵁ _
        rw [← hq2]
        exact le_preimage_cxOf e σ hj c'.U (c'.source_subset hq1)
      · obtain ⟨hq1, hq2⟩ := hq w (by obtain ⟨y', hy', he⟩ := hw.2; exact ⟨y', hy', he⟩)
        show c'.e (q w) a = valAt' (P w).1 _ _
        rw [c'.apply_eq _ hq1 a, ev_eq_valAt'_cxOf e σ hj _ _ (c'.source_subset hq1), hq2]
  · have hS : {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source,
        cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun w hw => hne ⟨_, hw.2.1⟩
    refine ⟨fun _ => c'.e.symm 0, ?_, fun w _ h _ => absurd ⟨_, h⟩ hne, ?_⟩
    · rw [hS]
      exact isOpen_empty
    · rw [hS]
      exact differentiableOn_empty

end GlobalTheory.LieBase
end
end

section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_frameFamily_chart_coordinates_holomorphic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), ∀ (c' : AlgChart X.str (σ.comp e.toRingHom) X.dim) (k : U.Comp) (n : ℕ) (W : Set (V n)) (ψ : V n → Frame (U.X k).Ψ (Dw.p + Dw.q)), IsOpen W → (∀ w ∈ W, ψ w ∈ (U.X k).dom) → (∀ τ i i', DifferentiableOn ℂ (fun w => mat (ψ w) τ i i') W) → ∃ q : V n → CxPts X.str (σ.comp e.toRingHom), IsOpen {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} ∧ (∀ w ∈ W, ∀ h : ψ w ∈ (U.X k).dom, (∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)) → q w ∈ c'.e.source ∧ cxOf e σ hj (q w) = cxPt T.Z (U.un k ⟨ψ w, h⟩)) ∧ DifferentiableOn ℂ (fun w => c'.e (q w)) {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} := by
  first | exact @GlobalTheory.LieBase.isHol_chart_framePt | exact GlobalTheory.LieBase.isHol_chart_framePt | (intros; apply GlobalTheory.LieBase.isHol_chart_framePt <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

namespace GlobalTheory.LieBase.HoloFrame

theorem exists_un : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.IsUnf U → ∀ (y : CxPts (genStr T.Z) σ), ¬ LiesIn y (genBd T.Z) → ∃ (k : U.Comp) (x : (U.X k).dom), cxPt T.Z (U.un k x) = y := by
  intro E _ _ _ H Dw l Xo c O _ β Y T σ r U hU y hy
  have hr : Set.range y.1 ⊆ Set.range T.Z.jQ := by
    rintro _ ⟨p, rfl⟩
    have hp : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst hp
    exact not_not.1 hy
  haveI := T.Z.jQ_open
  let xF := IsOpenImmersion.lift T.Z.jQ y.1 hr
  have hxF : xF ≫ T.Z.jQ = y.1 := IsOpenImmersion.lift_fac _ _ _
  have hs : xF ≫ Limits.pullback.snd _ _ = spMap (algebraMap c.F (CAt σ)) := by
    have h2 := y.2
    rw [← hxF, Category.assoc, T.Z.jQ_over] at h2
    exact h2
  have hover : (xF ≫ Limits.pullback.fst _ _) ≫ Xo.s = sOf c (CAt σ) := by
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hs]
    exact GlobalTheory.ShFam.OpenReg.spMap_comp _ _
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  obtain ⟨z, hz⟩ : ∃ z : FrPt Xo c (CAt σ), z.x = xF ≫ Limits.pullback.fst _ _ :=
    GlobalTheory.FlagTan.exists_frPt _ hover
  obtain ⟨k, f, t, hb⟩ := hU.2.2.1 z
  refine ⟨k, f, ?_⟩
  rw [cxPt_congr hb.1.symm]
  refine Subtype.ext ?_
  show GlobalTheory.AllWt.ptF (S := CAt σ) z ≫ T.Z.jQ = y.1
  rw [← hxF]
  congr 1
  apply Limits.pullback.hom_ext
  · exact (ptF_fst z).trans hz
  · exact (ptF_snd z).trans hs.symm

theorem exists_holo_frame_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (X : Var F) (j : X.X ⟶ gen T.Z), IsOpenImmersion j → ∀ (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∃ (k : U.Comp) (Fr : V X.dim → Frame (U.X k).Ψ (Dw.p + Dw.q)), ∀ᶠ u in 𝓝 (c'.e y), ∃ h : Fr u ∈ (U.X k).dom, cxPt T.Z (U.un k ⟨Fr u, h⟩) = cxOf e σ hj (c'.e.symm u) ∧ ∀ τ' a b, DifferentiableAt ℂ (fun u => mat (Fr u) τ' a b) u := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU X j hjo hj y hy c' hyc
  have hnb : ¬ LiesIn (cxOf e σ hj y) (genBd T.Z) := by
    intro h
    have h1 : IsLocalRing.closedPoint ℂ ∈ y.1 ⁻¹ᵁ openPart j := hy (Set.mem_univ _)
    exact h1 h
  obtain ⟨k, x₀, hx₀⟩ := exists_un E H Dw l Xo c O β Y T σ _ U hU _ hnb
  have hn := GlobalTheory.T.dim_openly_immersed_variety_eq_cmType_card_mul_pq E H Dw l Xo c O β Y T F e σ U hσ hU X j hjo hj ⟨y, hy⟩ k
  obtain ⟨W, a, ψ, hWo, haW, hψd, hψh, hψa, hinj⟩ := GlobalTheory.T.exists_holomorphic_frame_slice_componentUniformisation E H Dw l Xo c σ U hσ hU k x₀ X.dim hn
  obtain ⟨q, hOo, hq, hqd⟩ := GlobalTheory.T.holomorphic_frameFamily_chart_coordinates_holomorphic E H Dw l Xo c O β Y T F e σ U hσ hU X j hjo hj c' k X.dim W ψ hWo hψd hψh
  haveI := T.Z.jQ_open
  have hxeq : ∀ {z z' : FrPt Xo c (CAt σ)}, cxPt T.Z z = cxPt T.Z z' → z.x = z'.x := by
    intro z z' h
    have h1 : GlobalTheory.AllWt.ptF (S := CAt σ) z = GlobalTheory.AllWt.ptF (S := CAt σ) z' :=
      (cancel_mono T.Z.jQ).1 (congrArg Subtype.val h)
    rw [← ptF_fst z, h1, ptF_fst]
  have hcxinj : Function.Injective (cxOf e σ hj) := by
    intro y1 y2 h
    apply Subtype.ext
    exact (cancel_mono j).1 (congrArg Subtype.val h)
  have hya : cxOf e σ hj y = cxPt T.Z (U.un k ⟨ψ a, hψd a haW⟩) := hx₀.symm.trans (cxPt_congr (hψa _).symm)
  have haO : a ∈ {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} := ⟨haW, hψd a haW, y, hyc, hya⟩
  have hqa : q a = y := hcxinj ((hq a haW _ ⟨y, hyc, hya⟩).2.trans hya.symm)
  have hinjg : Set.InjOn (fun w => c'.e (q w)) {w | w ∈ W ∧ ∃ h : ψ w ∈ (U.X k).dom, ∃ y' ∈ c'.e.source, cxOf e σ hj y' = cxPt T.Z (U.un k ⟨ψ w, h⟩)} := by
    rintro w ⟨hw, hwd, hw'⟩ w' ⟨hw2, hwd', hw2'⟩ hg
    have h1 := hq w hw hwd hw'
    have h2 := hq w' hw2 hwd' hw2'
    have hqq : q w = q w' := c'.e.injOn h1.1 h2.1 hg
    refine hinj w hw w' hw2 hwd hwd' (hxeq ?_)
    rw [← h1.2, ← h2.2, hqq]
  obtain ⟨h, hev⟩ := GlobalTheory.T.exists_holomorphic_local_inverse_of_injOn X.dim _ _ a hOo haO hqd hinjg
  refine ⟨k, fun u => ψ (h u), ?_⟩
  rw [show c'.e y = c'.e (q a) by rw [hqa]]
  filter_upwards [hev] with u ⟨⟨huW, hud, hux⟩, hgu, hdu⟩
  refine ⟨hψd _ huW, ?_, fun τ' i i' => ?_⟩
  · have h1 := hq _ huW (hψd _ huW) hux
    rw [← h1.2]
    congr 1
    exact (c'.e.left_inv h1.1).symm.trans (congrArg c'.e.symm hgu)
  · exact ((hψh τ' i i' _ huW).differentiableAt (hWo.mem_nhds huW)).comp u hdu

end GlobalTheory.LieBase.HoloFrame
end
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open GlobalTheory.PointFormSign Matrix
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase.LocalModel

theorem differentiableAt_det {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {d : ℕ}
    {A : V → Matrix (Fin d) (Fin d) ℂ} {u : V} (hA : ∀ a b, DifferentiableAt ℂ (fun v => A v a b) u) :
    DifferentiableAt ℂ (fun v => (A v).det) u := by
  simp only [Matrix.det_apply']
  refine DifferentiableAt.fun_sum fun σ _ => DifferentiableAt.const_mul ?_ _
  have key : ∀ t : Finset (Fin d), DifferentiableAt ℂ (fun v => ∏ i ∈ t, A v (σ i) i) u := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hA _ _).mul ih
  exact key _

theorem differentiableAt_inv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {d : ℕ}
    {A : V → Matrix (Fin d) (Fin d) ℂ} {u : V} (hA : ∀ a b, DifferentiableAt ℂ (fun v => A v a b) u)
    (hd : (A u).det ≠ 0) (i k : Fin d) : DifferentiableAt ℂ (fun v => (A v)⁻¹ i k) u := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  refine ((differentiableAt_det hA).inv hd).mul (differentiableAt_det fun a b => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact differentiableAt_const _
  · exact hA _ _

theorem differentiableAt_mul {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {a b d : ℕ}
    {A : V → Matrix (Fin a) (Fin b) ℂ} {B : V → Matrix (Fin b) (Fin d) ℂ} {u : V}
    (hA : ∀ i k, DifferentiableAt ℂ (fun v => A v i k) u) (hB : ∀ i k, DifferentiableAt ℂ (fun v => B v i k) u)
    (i k : Fin _) : DifferentiableAt ℂ (fun v => (A v * B v) i k) u := by
  simp only [Matrix.mul_apply]
  exact DifferentiableAt.fun_sum fun c _ => (hA i c).mul (hB c k)

theorem gram_cast {n m q q' : ℕ} (h : n = m) (h' : q' = q) (κ : ℂ) (Gm Mu : Matrix (Fin n) (Fin n) ℂ)
    (C : Matrix (Fin m) (Fin m) ℂ) (z : Matrix (Fin m) (Fin q) ℂ)
    (hG : Gm.submatrix (Fin.cast h.symm) (Fin.cast h.symm) = κ • (Cᴴ * (Formalism.DegreeFormula.hP z)⁻¹ * C)) :
    (Muᴴ * Gm * Mu)ᵀ = κ • ((C.submatrix (Fin.cast h) (Fin.cast h) * Mu)ᵀ *
      GlobalTheory.PointFormSign.domGram n q' (fun a b => z (Fin.cast h a) (Fin.cast h' b)) *
        (C.submatrix (Fin.cast h) (Fin.cast h) * Mu)ᴴᵀ) := by
  subst h h'
  have hG' : Gm = κ • (Cᴴ * (Formalism.DegreeFormula.hP z)⁻¹ * C) := by simpa using hG
  subst hG'
  simp only [GlobalTheory.PointFormSign.domGram, Formalism.DegreeFormula.hP, Fin.cast_eq_self, Matrix.submatrix_id_id, Matrix.of_apply]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.conjTranspose_mul,
    Matrix.mul_assoc]
  rfl

theorem posDef_cast {n m q q' : ℕ} (h : n = m) (h' : q' = q) (z : Matrix (Fin m) (Fin q) ℂ)
    (hz : (1 - z * zᴴ).PosDef) :
    (1 - Matrix.of (fun a b => z (Fin.cast h a) (Fin.cast h' b)) *
      (Matrix.of (fun a b => z (Fin.cast h a) (Fin.cast h' b)))ᴴ).PosDef := by
  subst h h'
  simp only [Fin.cast_eq_self]
  exact hz

theorem lieGram_local_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ τ : GlobalTheory.AllWt.Psi H, ∃ (κ : ℝ) (W : V X.dim → Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) ℂ) (Z : V X.dim → (Fin (Dw.mult τ.1) → Fin (Dw.p + Dw.q - Dw.mult τ.1) → ℂ)), 0 < κ ∧ (∀ᶠ u in 𝓝 (c'.e y), lieGram e U hj f₀ A₀ A (c'.e.symm u) τ.1 = (κ : ℂ) • ((W u)ᵀ * domGram _ _ (Z u) * (W u)ᴴᵀ)) ∧ (∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ Z u) ∧ (∀ i j, ∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ (fun u => W u i j) u) ∧ IsUnit (W (c'.e y)).det ∧ (1 - Matrix.of (Z (c'.e y)) * (Matrix.of (Z (c'.e y)))ᴴ).PosDef := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hLie y hy c' hyc A hA τ
  obtain ⟨kU, G, hG⟩ := GlobalTheory.LieBase.HoloFrame.exists_holo_frame_chart E H Dw l Xo c O β Y T F e σ U hσ hU X j hLie.1
    hj y hy c' hyc
  have hF : ∀ᶠ u in 𝓝 (c'.e y), ∃ h : G u ∈ (U.X kU).dom,
      cxPt T.Z (U.un kU ⟨G u, h⟩) = cxOf e σ hj (c'.e.symm u) := hG.mono fun u ⟨h, h1, _⟩ => ⟨h, h1⟩
  have hGd : ∀ τ' a b, ∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ' a b) u :=
    fun τ' a b => hG.mono fun u ⟨_, _, h2⟩ => h2 τ' a b
  obtain ⟨M, hMd, hMu, hMc⟩ := GlobalTheory.LieBase.exists_holo_coord_frameAt E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀
    Eb A₀ hj hLie y hy c' hyc A hA τ kU G hF hGd
  have hle : Dw.p ≤ Dw.p + Dw.q := Nat.le_add_right _ _
  have hp : (U.X kU).p0 = Dw.p + Dw.q - Dw.p := by rw [(hU.2.1 kU).1]; omega
  have hm : Dw.mult τ.1 = Dw.p := GlobalTheory.HodgeGenUnf.mult_psi τ
  have hq : Dw.p + Dw.q - Dw.mult τ.1 = Dw.p + Dw.q - Dw.p := by rw [hm]
  set τ' := GlobalTheory.HodgeGenUnf.letter hσ hU kU τ with hτ'

  have hco : ∀ u, (∀ τ'' a b, DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ'' a b) u) →
      ∀ a b, DifferentiableAt ℂ (fun v => GlobalTheory.TrueCx.frameCo (U.X kU) hle (G v) τ' a b) u := by
    intro u hd a b
    simp only [GlobalTheory.TrueCx.frameCo, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]
    exact DifferentiableAt.fun_sum fun c _ => (hd _ _ _).const_mul _
  have hmo : ∀ u, (∀ τ'' a b, DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ'' a b) u) →
      G u ∈ (U.X kU).dom → ∀ a b,
      DifferentiableAt ℂ (fun v => Formalism.MJ.moeb (GlobalTheory.TrueCx.frameCo (U.X kU) hle (G v) τ') 0 a b) u := by
    intro u hd hdom a b
    simp only [GlobalTheory.TrueCx.moeb_zero]
    refine differentiableAt_mul (fun i k => hco u hd _ _) (differentiableAt_inv (fun i k => hco u hd _ _) ?_) a b
    exact (GlobalTheory.TrueCx.frameCo_isUnit₂₂ (U.X kU) hle hp hdom τ').ne_zero
  refine ⟨2 * Real.pi,
    fun u => (GlobalTheory.ShFam.coW (U.X kU) hle (G u) τ').submatrix (Fin.cast hm) (Fin.cast hm) * M u,
    fun u a b => Formalism.MJ.moeb (GlobalTheory.TrueCx.frameCo (U.X kU) hle (G u) τ') 0 (Fin.cast hm a) (Fin.cast hq b),
    Real.two_pi_pos, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hMc, hF] with u hu1 hu2
    obtain ⟨h, ⟨g, hg⟩, hc⟩ := hu1
    obtain ⟨h', hx⟩ := hu2
    have hex : ∃ g : EigFrame T.Z σ ((cxOf e σ hj (c'.e.symm u)).1 ≫ genι T.Z), FrameAt e f₀ A₀ A (c'.e.symm u) g :=
      ⟨g, hg⟩
    rw [lieGram, dif_pos hex]
    show ((hodgeMet T.Z U).gram _ hex.choose τ.1)ᵀ = _
    rw [GlobalTheory.HodgeOnDomain.eigGram_transport (hodgeMet T.Z U) hx.symm hex.choose (cxFrame T.Z (U.un kU ⟨G u, h⟩)) τ.1
      (M u) (hc _ _ hex.choose_spec)]
    exact gram_cast hm hq _ _ _ _ _ (GlobalTheory.HodgeGenUnf.hodgeMet_gram_frame T.Z hσ hU kU ⟨G u, h⟩ τ τ' rfl hle)
  · filter_upwards [hG] with u hu
    obtain ⟨h, -, hd⟩ := hu
    exact differentiableAt_pi.2 fun a => differentiableAt_pi.2 fun b => hmo u hd h _ _
  · intro a b
    filter_upwards [hG, Filter.eventually_all.2 fun c => Filter.eventually_all.2 fun d => hMd c d] with u hu hM
    obtain ⟨h, -, hd⟩ := hu
    refine differentiableAt_mul (fun i k => ?_) (fun i k => hM i k) a b
    simp only [Matrix.submatrix_apply, GlobalTheory.ShFam.coW, Matrix.sub_apply]
    exact (hco u hd _ _).sub (differentiableAt_mul (fun i k => hmo u hd h _ _) (fun i k => hco u hd _ _) _ _)
  · obtain ⟨h, -, -⟩ := hG.self_of_nhds
    rw [Matrix.det_mul]
    refine IsUnit.mul ?_ hMu
    have e1 : ((GlobalTheory.ShFam.coW (U.X kU) hle (G (c'.e y)) τ').submatrix (Fin.cast hm) (Fin.cast hm)).det =
        (GlobalTheory.ShFam.coW (U.X kU) hle (G (c'.e y)) τ').det := Matrix.det_submatrix_equiv_self (finCongr hm) _
    rw [e1]
    exact GlobalTheory.ShFam.isUnit_coW (U.X kU) hle hp h τ'
  · obtain ⟨h, -, -⟩ := hG.self_of_nhds
    have hz := GlobalTheory.TrueCx.domPt_mem (U.X kU) hle id hp h τ'
    exact posDef_cast hm hq _ (GlobalTheory.HodgeDomain.hP_posDef hz)

end GlobalTheory.LieBase.LocalModel
end
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open GlobalTheory.PointFormSign Matrix
open ReciprocityTheory.L2DbarEstimates (V)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieEigenspaceHodgeGram_local_holomorphic_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ τ : GlobalTheory.AllWt.Psi H, ∃ (κ : ℝ) (W : V X.dim → Matrix (Fin (Dw.mult τ.1)) (Fin (Dw.mult τ.1)) ℂ) (Z : V X.dim → (Fin (Dw.mult τ.1) → Fin (Dw.p + Dw.q - Dw.mult τ.1) → ℂ)), 0 < κ ∧ (∀ᶠ u in 𝓝 (c'.e y), lieGram e U hj f₀ A₀ A (c'.e.symm u) τ.1 = (κ : ℂ) • ((W u)ᵀ * domGram _ _ (Z u) * (W u)ᴴᵀ)) ∧ (∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ Z u) ∧ (∀ i j, ∀ᶠ u in 𝓝 (c'.e y), DifferentiableAt ℂ (fun u => W u i j) u) ∧ IsUnit (W (c'.e y)).det ∧ (1 - Matrix.of (Z (c'.e y)) * (Matrix.of (Z (c'.e y)))ᴴ).PosDef := by
  atlas_forward_decl GlobalTheory.LieBase.LocalModel.lieGram_local_model
end

section
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

open scoped ComplexOrder Topology
open GlobalTheory.PointFormSign Matrix
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.PointFormSign

theorem chernTop_pointPoly_nonneg {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    {n : ℕ} (G : V n → Mat Dw.mult ℂ) (v : V n)
    (h : ∀ τ : GlobalTheory.AllWt.Psi H, IsNegSq (curv (fun u => G u τ.1) v) (Dw.p + Dw.q - Dw.mult τ.1)) :
    0 ≤ chernTop (pointPoly H Dw) G v := by
  choose S T hS hF using h
  have key : aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => G u x.1) v x.2) (pointPoly H Dw) =
      ∏ τ : GlobalTheory.AllWt.Psi H, (sqPoly (T τ)).det ^ (Dw.p + Dw.q - Dw.mult τ.1) := by
    rw [pointPoly, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_pow, map_mul, aeval_C, aeval_X, GlobalTheory.T.chernFormPolyCoeff_top_of_neg_hermitianSquare _ _ _ _ (hS τ) (hF τ)]
    congr 1
    simp only [map_pow, map_neg, map_one]
    rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  have h0 : 0 ≤ topCoeff (aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => G u x.1) v x.2) (pointPoly H Dw)) := by
    rw [key]; exact GlobalTheory.T.topDegreeFormCoeff_prod_det_hermitianSquare_pow_nonneg _ _ _ T
  have hre : 0 ≤ (topCoeff (aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => G u x.1) v x.2) (pointPoly H Dw))).re :=
    (Complex.nonneg_iff.1 h0).1
  unfold chernTop
  exact mul_nonneg (inv_nonneg.2 (pow_nonneg Real.pi_pos.le _)) hre

end GlobalTheory.PointFormSign

theorem GlobalTheory.PointFormSign.chernTop_pointPoly_lieGram_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), 0 ≤ chernTop (pointPoly H Dw) (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL y hy c' hyc A hA
  refine GlobalTheory.PointFormSign.chernTop_pointPoly_nonneg H Dw _ _ fun τ => ?_
  obtain ⟨κ, W, Z, hκ, hG, hZ, hW, hWu, hZd⟩ := GlobalTheory.T.lieEigenspaceHodgeGram_local_holomorphic_model E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL y hy c' hyc A hA τ
  exact GlobalTheory.T.isNegHermitianSquare_curvature_of_holomorphic_frameChange _ _ W Z κ hκ hG hZ hW hWu hZd (GlobalTheory.T.isNegHermitianSquare_curvature_boundedDomainHodgeGram _ _ _ hZd)
end

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernTop_pointClass_hodge_metric_lie_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), 0 ≤ chernTop (pointPoly H Dw) (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y) := by
  atlas_forward_decl GlobalTheory.PointFormSign.chernTop_pointPoly_lieGram_nonneg
end
