import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismDescendsToAlgebraic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertFactorOfHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAppellHumbertLineBundle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DifferentiableOnProdOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfAppellHumbertThetaFunction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ChiEqOneOrOfSym
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfHolUnif

section
section
open Matrix Polynomial

namespace GlobalTheory.Desc.SqLin

section Alg
variable {A : Type} [CommRing A] [Algebra ℚ A] [Module.Finite ℚ A]

theorem exists_casimir (τ : A →ₗ[ℚ] ℚ) (y : A) (hy : ∀ a, a ≠ 0 → 0 < τ (y * a ^ 2)) :
    ∃ (r : ℕ) (c : Fin r → ℚ) (e : Fin r → A), (∀ i, 0 < c i) ∧
      (∀ a, (∀ i, e i * a = 0) → a = 0) ∧
      ∀ a, τ (y * (∑ i, c i • e i ^ 2) * a) = LinearMap.trace ℚ A (LinearMap.mulLeft ℚ a) := by
  classical
  let β : LinearMap.BilinForm ℚ A := ((LinearMap.mul ℚ A).compr₂ (τ ∘ₗ LinearMap.mulLeft ℚ y))
  have hβ : ∀ a b, β a b = τ (y * (a * b)) := fun a b => rfl
  have hs : β.IsSymm := ⟨fun a b => by simp only [hβ, mul_comm a b, RingHom.id_apply]⟩
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (K := ℚ) (V := A) (B := β) ⟨hs.eq⟩
  have hpos : ∀ i, 0 < β (v i) (v i) := fun i => by
    rw [hβ, ← sq]; exact hy _ (v.ne_zero i)
  have hco : ∀ a i, β a (v i) = v.repr a i * β (v i) (v i) := by
    intro a i
    conv_lhs => rw [← v.sum_repr a]
    rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      have : β (v j) (v i) = 0 := hv hj
      simp [this]
    · simp
  refine ⟨_, fun i => (β (v i) (v i))⁻¹, v, fun i => inv_pos.2 (hpos i), ?_, ?_⟩
  · intro a ha
    have : (1 : A) * a = 0 := by
      rw [← v.sum_repr 1, Finset.sum_mul]
      simp [ha]
    simpa using this
  · intro a
    rw [LinearMap.trace_eq_matrix_trace ℚ v, Matrix.trace, Finset.mul_sum, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := hco (a * v i) i
    rw [hβ] at h1
    have h2 : y * (β (v i) (v i))⁻¹ • v i ^ 2 * a = (β (v i) (v i))⁻¹ • (y * (a * v i * v i)) := by
      rw [mul_smul_comm, smul_mul_assoc]; congr 1; ring
    rw [h2, map_smul, h1, smul_eq_mul, Matrix.diag_apply, LinearMap.toMatrix_apply]
    have := (hpos i).ne'
    simp only [LinearMap.mulLeft_apply]
    field_simp

theorem exists_inv (y : A) (hy : ∀ a, y * a = 0 → a = 0) : ∃ u, y * u = 1 := by
  have hinj : Function.Injective (LinearMap.mulLeft ℚ y) := by
    rw [injective_iff_map_eq_zero]; exact hy
  exact (LinearMap.injective_iff_surjective.1 hinj) 1

theorem exists_sum_sq (τ : A →ₗ[ℚ] ℚ) (h1 : ∀ a, a ≠ 0 → 0 < τ (a ^ 2)) (y : A)
    (hy : ∀ a, a ≠ 0 → 0 < τ (y * a ^ 2)) :
    ∃ (r : ℕ) (c : Fin r → ℚ) (e : Fin r → A), (∀ i, 0 < c i) ∧ y = ∑ i, c i • e i ^ 2 := by
  classical
  obtain ⟨r, c, e, hc, he, hK⟩ := exists_casimir τ y hy
  obtain ⟨s, d, f, hd, -, hL⟩ := exists_casimir τ 1 (by simpa using h1)
  have hnn : ∀ a, 0 ≤ τ (a ^ 2) := fun a => by
    by_cases h : a = 0
    · simp [h]
    · exact (h1 a h).le
  have hz : ∀ a, τ (a ^ 2) = 0 → a = 0 := fun a h => by
    by_contra h'
    exact (h1 a h').ne' h
  set K := ∑ i, c i • e i ^ 2 with hKd
  set L := ∑ i, d i • f i ^ 2 with hLd
  have hKL : y * K = L := by
    have := hK (y * K - L)
    rw [← hL, one_mul] at this
    refine sub_eq_zero.1 (hz _ ?_)
    rw [sq, sub_mul, map_sub, this, sub_self]
  obtain ⟨u, hu⟩ := exists_inv K (by
    intro a ha
    refine he a fun i => hz _ ?_
    have h0 : ∑ i, c i * τ ((e i * a) ^ 2) = 0 := by
      have : τ (K * a * a) = 0 := by rw [ha]; simp
      rw [← this, hKd, Finset.sum_mul, Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_mul_assoc, smul_mul_assoc, map_smul, smul_eq_mul]
      congr 2; ring
    rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hc i).le (hnn _)] at h0
    exact (mul_eq_zero.1 (h0 i (Finset.mem_univ _))).resolve_left (hc i).ne')
  refine ⟨r * s, fun k => c (finProdFinEquiv.symm k).1 * d (finProdFinEquiv.symm k).2,
    fun k => e (finProdFinEquiv.symm k).1 * f (finProdFinEquiv.symm k).2 * u,
    fun k => mul_pos (hc _) (hd _), ?_⟩
  rw [Equiv.sum_comp finProdFinEquiv.symm
    (fun k : Fin r × Fin s => (c k.1 * d k.2) • (e k.1 * f k.2 * u) ^ 2), Fintype.sum_prod_type]
  have : y = K * L * u ^ 2 := by
    rw [← hKL]; linear_combination (-y * (K * u + 1)) * hu
  rw [this, hKd, hLd, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Algebra.smul_def, map_mul]
  ring

end Alg

open scoped MatrixOrder in

theorem exists_diag {n : ℕ} (T B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef)
    (hT : (B * T).PosDef) :
    ∃ (P Q : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ), P * Q = 1 ∧ Q * P = 1 ∧ (∀ i, 0 < d i) ∧
      T = P * diagonal d * Q := by
  obtain ⟨C, hC, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hB.isStrictlyPositive
  obtain ⟨C, rfl⟩ := hC
  have hH : (star (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ) * (star (C : Matrix (Fin n) (Fin n) ℝ) * C * T) *
      (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ)).PosDef :=
    (Matrix.IsUnit.posDef_star_left_conjugate_iff (Units.isUnit _)).2 hT
  have e : star (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ) * (star (C : Matrix (Fin n) (Fin n) ℝ) * C * T) *
      (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ) = C * T * (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ) := by
    rw [mul_assoc (star (C : Matrix (Fin n) (Fin n) ℝ)), ← mul_assoc (star _), ← star_mul,
      Units.mul_inv, star_one, one_mul]
  rw [e] at hH
  have hs := hH.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  set U := hH.1.eigenvectorUnitary
  have h1 : (U : Matrix (Fin n) (Fin n) ℝ) * star (U : Matrix (Fin n) (Fin n) ℝ) = 1 := U.2.2
  have h2 : star (U : Matrix (Fin n) (Fin n) ℝ) * (U : Matrix (Fin n) (Fin n) ℝ) = 1 := U.2.1
  refine ⟨(↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ) * U, star (U : Matrix (Fin n) (Fin n) ℝ) * C,
    hH.1.eigenvalues, ?_, ?_, hH.eigenvalues_pos, ?_⟩
  · rw [mul_assoc, ← mul_assoc (U : Matrix (Fin n) (Fin n) ℝ), h1, one_mul, Units.inv_mul]
  · rw [mul_assoc, ← mul_assoc (C : Matrix (Fin n) (Fin n) ℝ), Units.mul_inv, one_mul, h2]
  · have : T = (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ) * (C * T * (↑C⁻¹ : Matrix (Fin n) (Fin n) ℝ)) * C := by
      simp [mul_assoc]
    refine this.trans ?_
    conv_lhs => rw [hs]
    simp [mul_assoc]

theorem aeval_map_eq {n : ℕ} (T : Matrix (Fin n) (Fin n) ℚ) (P Q : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) (h1 : P * Q = 1) (h2 : Q * P = 1)
    (hT : T.map (Rat.cast : ℚ → ℝ) = P * diagonal d * Q) (p : ℚ[X]) :
    (aeval T p).map (Rat.cast : ℚ → ℝ) = P * diagonal (fun k => aeval (d k) p) * Q := by
  have hm : ∀ M : Matrix (Fin n) (Fin n) ℚ,
      M.map (Rat.cast : ℚ → ℝ) = (Rat.castHom ℝ).mapMatrix M := fun M => rfl
  induction p using Polynomial.induction_on with
  | C a =>
    have : (diagonal fun _ : Fin n => (a : ℝ)) = (a : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
      ext i j; by_cases h : i = j <;> simp [h, one_apply]
    simp only [aeval_C, eq_ratCast, this, Matrix.mul_smul, Matrix.smul_mul, mul_one, h1]
    ext i j; by_cases h : i = j <;> simp [h, one_apply, Matrix.algebraMap_matrix_apply]
  | add p q hp hq =>
    simp only [map_add]
    rw [hm, map_add, ← hm, ← hm, hp, hq, ← diagonal_add, mul_add, add_mul]
  | monomial m a h =>
    rw [pow_succ, ← mul_assoc, map_mul, hm, map_mul, ← hm, ← hm, h, aeval_X, hT]
    have : ∀ D E : Matrix (Fin n) (Fin n) ℝ, P * D * Q * (P * E * Q) = P * (D * E) * Q := by
      intro D E
      calc P * D * Q * (P * E * Q) = P * D * (Q * P) * E * Q := by simp only [mul_assoc]
        _ = _ := by rw [h2]; simp only [mul_assoc, one_mul]
    rw [this, diagonal_mul_diagonal]
    simp [mul_assoc]

theorem main (n : ℕ) (Tm : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.PosDef) (hT : (B * Tm.map (Rat.cast : ℚ → ℝ)).PosDef) :
    ∃ (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ), 0 < c₀ ∧ (∀ i, 0 < c i) ∧
      (1 : Matrix (Fin n) (Fin n) ℚ) =
        c₀ • Tm + ∑ i, c i • ((Polynomial.aeval Tm (p i)) ^ 2 * Tm) := by
  classical
  obtain ⟨P, Q, d, h1, h2, hd, hD⟩ := exists_diag _ B hB hT
  have key := aeval_map_eq Tm P Q d h1 h2 hD
  let f : ℚ[X] →ₐ[ℚ] Matrix (Fin n) (Fin n) ℚ := aeval Tm
  let ι := Ideal.kerLiftAlg f
  have hι : Function.Injective ι := Ideal.kerLiftAlg_injective f
  have hιm : ∀ p, ι (Ideal.Quotient.mk _ p) = aeval Tm p := Ideal.kerLiftAlg_mk f
  haveI : Module.Finite ℚ (ℚ[X] ⧸ RingHom.ker f) := Module.Finite.of_injective ι.toLinearMap hι
  let τ : (ℚ[X] ⧸ RingHom.ker f) →ₗ[ℚ] ℚ := Matrix.traceLinearMap (Fin n) ℚ ℚ ∘ₗ ι.toLinearMap
  have hτ : ∀ p, ((τ (Ideal.Quotient.mk _ p) : ℚ) : ℝ) = ∑ k, aeval (d k) p := by
    intro p
    have : τ (Ideal.Quotient.mk _ p) = (aeval Tm p).trace := by rw [← hιm]; rfl
    have h3 : (((aeval Tm p).trace : ℚ) : ℝ) = ((aeval Tm p).map (Rat.cast : ℚ → ℝ)).trace := by
      simp [Matrix.trace]
    rw [this, h3, key, trace_mul_comm, ← mul_assoc, h2, one_mul, trace_diagonal]
  have hpos : ∀ q : ℚ[X], (∀ k, 0 < aeval (d k) q) → ∀ a : ℚ[X] ⧸ RingHom.ker f, a ≠ 0 →
      0 < τ (Ideal.Quotient.mk _ q * a ^ 2) := by
    intro q hq a ha
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [← map_pow, ← map_mul, ← Rat.cast_pos (K := ℝ), hτ]
    have : ∃ k, aeval (d k) p ≠ 0 := by
      by_contra h
      push Not at h
      apply ha
      apply hι
      rw [hιm, map_zero]
      have := key p
      simp only [h, diagonal_zero, mul_zero, zero_mul] at this
      ext i j
      simpa using congrFun (congrFun this i) j
    obtain ⟨k, hk⟩ := this
    refine Finset.sum_pos' (fun i _ => ?_) ⟨k, Finset.mem_univ _, ?_⟩
    · rw [map_mul, map_pow]; exact mul_nonneg (hq i).le (sq_nonneg _)
    · rw [map_mul, map_pow]; exact mul_pos (hq k) (by positivity)
  obtain ⟨N, hN⟩ := exists_rat_gt (∑ k, d k)
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (Finset.sum_nonneg fun i _ => (hd i).le) hN
  have hN0' : 0 < N := by exact_mod_cast hN0
  have hNk : ∀ k, d k < N := fun k =>
    lt_of_le_of_lt (Finset.single_le_sum (fun i _ => (hd i).le) (Finset.mem_univ k)) hN
  set x : ℚ[X] ⧸ RingHom.ker f := Ideal.Quotient.mk _ X with hx
  obtain ⟨u, hu⟩ := exists_inv x (by
    intro a ha
    by_contra h
    have := hpos X (by simpa using hd) a h
    rw [sq, ← mul_assoc, ← hx, ha] at this
    simp at this)
  obtain ⟨r, c, e, hc, he⟩ := exists_sum_sq τ (by simpa using hpos 1 (by simp)) _
    (hpos ((C N - X) * X) (fun k => by
      simpa using mul_pos (sub_pos.2 (hNk k)) (hd k)))
  choose p hp using fun i => Ideal.Quotient.mk_surjective (e i * u)
  refine ⟨N⁻¹, r, fun i => N⁻¹ * c i, p, inv_pos.2 hN0', fun i => mul_pos (inv_pos.2 hN0') (hc i), ?_⟩
  have hmain : (1 : ℚ[X] ⧸ RingHom.ker f) =
      N⁻¹ • x + ∑ i, (N⁻¹ * c i) • ((Ideal.Quotient.mk _ (p i)) ^ 2 * x) := by
    have e1 : ∑ i, (N⁻¹ * c i) • ((Ideal.Quotient.mk (RingHom.ker f) (p i)) ^ 2 * x) =
        N⁻¹ • ((∑ i, c i • e i ^ 2) * (u ^ 2 * x)) := by
      rw [Finset.sum_mul, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hp, mul_smul, smul_mul_assoc, mul_pow, mul_assoc]
    have e2 : Ideal.Quotient.mk (RingHom.ker f) (C N) = algebraMap ℚ _ N := rfl
    rw [e1, ← he, map_mul, map_sub, e2, ← hx, ← smul_add]
    have e3 : x + (algebraMap ℚ _ N - x) * x * (u ^ 2 * x) = algebraMap ℚ _ N := by
      linear_combination ((algebraMap ℚ _ N - x) * (x * u + 1)) * hu
    rw [e3, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hN0'.ne', map_one]
  have := congrArg ι hmain
  simpa only [map_one, map_add, map_smul, map_sum, map_mul, map_pow, hx, hιm, aeval_X] using this

end GlobalTheory.Desc.SqLin
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_eq_positive_squares_times_selfAdjoint : ∀ (n : ℕ) (Tm : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin n) (Fin n) ℝ), B.PosDef → (B * Tm.map (Rat.cast : ℚ → ℝ)).PosDef → ∃ (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ), 0 < c₀ ∧ (∀ i, 0 < c i) ∧ (1 : Matrix (Fin n) (Fin n) ℚ) = c₀ • Tm + ∑ i, c i • ((Polynomial.aeval Tm (p i)) ^ 2 * Tm) := by
  atlas_forward_decl GlobalTheory.Desc.SqLin.main
end

section
section
open Matrix

namespace GlobalTheory

theorem herm_gamma_star_map_mulVec {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℂ) :
    star (M.map star *ᵥ v) = M *ᵥ star v := by
  funext i
  simp only [mulVec, dotProduct, Pi.star_apply, star_sum, map_apply, star_mul', star_star]

theorem herm_gamma_map_mulVec_dot {g : ℕ} (B : Matrix (Fin g) (Fin g) ℂ) (z u : Fin g → ℂ) :
    (B *ᵥ z) ⬝ᵥ u = z ⬝ᵥ (Bᵀ *ᵥ u) := by
  rw [dotProduct_comm, dotProduct_mulVec, mulVec_transpose, dotProduct_comm]

theorem herm_gamma_det_ne_zero {g : ℕ} (H₁ : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) : H₁.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hHv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet
  have hz : star v ≠ 0 := by
    intro h; apply hv; simpa using congrArg star h
  have := hpos (star v) hz
  rw [star_star, hHv, dotProduct_zero] at this
  simp at this

theorem herm_gamma : ∀ (g : ℕ) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ), H₁.IsHermitian → H₂.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) →
    ∃ γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) ∧
      ∀ z w, z ⬝ᵥ H₂.mulVec (star (γ w)) = γ z ⬝ᵥ H₂.mulVec (star w) := by
  intro g H₁ H₂ h1 h2 hpos
  have hdet : IsUnit H₁.det := isUnit_iff_ne_zero.2 (herm_gamma_det_ne_zero H₁ hpos)
  refine ⟨Matrix.toLin' ((H₁⁻¹ * H₂).map star), ?_, ?_⟩
  · intro z w
    rw [Matrix.toLin'_apply, herm_gamma_star_map_mulVec, mulVec_mulVec, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
  · intro z w
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, herm_gamma_star_map_mulVec, mulVec_mulVec,
      herm_gamma_map_mulVec_dot, mulVec_mulVec]
    congr 2
    have hT : ((H₁⁻¹ * H₂).map star)ᵀ = (H₁⁻¹ * H₂)ᴴ := rfl
    rw [hT, conjTranspose_mul, h2.eq, conjTranspose_nonsing_inv, h1.eq, Matrix.mul_assoc]

end GlobalTheory
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfAdjoint_endo_relating_hermitian_forms : ∀ (g : ℕ) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ), H₁.IsHermitian → H₂.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) →
    ∃ γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) ∧
      ∀ z w, z ⬝ᵥ H₂.mulVec (star (γ w)) = γ z ⬝ᵥ H₂.mulVec (star w) := by
  atlas_forward_decl GlobalTheory.herm_gamma
end

section
section
open Matrix

namespace GlobalTheory

def imFormRight {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] ℝ where
  toFun w := (z ⬝ᵥ H *ᵥ star w).im
  map_add' a b := by simp [star_add, mulVec_add, dotProduct_add]
  map_smul' r w := by
    simp [star_smul, mulVec_smul, dotProduct_smul, Complex.smul_im]

def imFormLeft {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (w : Fin g → ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] ℝ where
  toFun z := (z ⬝ᵥ H *ᵥ star w).im
  map_add' a b := by simp [add_dotProduct]
  map_smul' r z := by
    simp [smul_dotProduct, Complex.smul_im]

theorem herm_endo_matrix_rat : ∀ (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ),
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) →
    (∀ k l, ∃ m : ℤ, (m : ℝ) = (e k ⬝ᵥ H₁.mulVec (star (e l))).im) →
    (∀ k l, ∃ m : ℤ, (m : ℝ) = (e k ⬝ᵥ H₂.mulVec (star (e l))).im) →
    ∀ (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
    (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) →
    ∃ Tq : Matrix (Fin n) (Fin n) ℚ,
      Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ) := by
  intro g n e H₁ H₂ hpos h1 h2 γ hγ
  classical
  set T := LinearMap.toMatrix e e (γ.restrictScalars ℝ) with hT
  let A₁ : Matrix (Fin n) (Fin n) ℝ := fun k l => (e k ⬝ᵥ H₁ *ᵥ star (e l)).im
  let A₂ : Matrix (Fin n) (Fin n) ℝ := fun k l => (e k ⬝ᵥ H₂ *ᵥ star (e l)).im

  have hγe : ∀ l, γ (e l) = ∑ m, T m l • e m := by
    intro l
    have := e.sum_repr (γ (e l))
    rw [← this]
    simp [hT, LinearMap.toMatrix_apply]

  have key : A₁ * T = A₂ := by
    ext k l
    rw [mul_apply]
    show _ = (e k ⬝ᵥ H₂ *ᵥ star (e l)).im
    rw [hγ, hγe l]
    have := map_sum (imFormRight H₁ (e k)) (fun m : Fin n => T m l • e m) (Finset.univ : Finset (Fin n))
    simp only [map_smul, smul_eq_mul] at this
    change _ = imFormRight H₁ (e k) _
    rw [this]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_comm]; rfl

  have hdet : A₁.det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
    set v := ∑ l, x l • e l with hv
    have hk : ∀ k, imFormRight H₁ (e k) v = 0 := by
      intro k
      have := congrFun hx k
      rw [hv, map_sum]
      simp only [map_smul, smul_eq_mul]
      simp only [mulVec, dotProduct, Pi.zero_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_comm]; rfl
    have hu : ∀ u, imFormLeft H₁ v u = 0 := by
      intro u
      rw [← e.sum_repr u, map_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [map_smul]
      have := hk k
      simp only [imFormRight, imFormLeft, LinearMap.coe_mk, AddHom.coe_mk] at this ⊢
      rw [this, smul_zero]
    have hre : (v ⬝ᵥ H₁ *ᵥ star v).re = 0 := by
      have := hu (Complex.I • v)
      simp only [imFormLeft, LinearMap.coe_mk, AddHom.coe_mk, smul_dotProduct, smul_eq_mul,
        Complex.mul_im, Complex.I_re, Complex.I_im] at this
      simpa using this
    have hv0 : v = 0 := by
      by_contra hne
      have := hpos v hne
      linarith
    apply hx0
    have : e.equivFun.symm x = 0 := by rw [Module.Basis.equivFun_symm_apply]; exact hv0
    exact e.equivFun.symm.injective (by rw [this, map_zero])

  choose m₁ hm₁ using h1
  choose m₂ hm₂ using h2
  let A₁q : Matrix (Fin n) (Fin n) ℚ := fun k l => (m₁ k l : ℚ)
  let A₂q : Matrix (Fin n) (Fin n) ℚ := fun k l => (m₂ k l : ℚ)
  have hA₁ : A₁q.map (Rat.castHom ℝ) = A₁ := by
    ext k l
    show ((m₁ k l : ℚ) : ℝ) = _
    rw [Rat.cast_intCast, hm₁]
  have hA₂ : A₂q.map (Rat.castHom ℝ) = A₂ := by
    ext k l
    show ((m₂ k l : ℚ) : ℝ) = _
    rw [Rat.cast_intCast, hm₂]
  have hdetq : IsUnit A₁q.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hdet
    have := (Rat.castHom ℝ).map_det A₁q
    rw [h0, map_zero] at this
    rw [← hA₁]
    exact this.symm
  have hdetR : IsUnit A₁.det := isUnit_iff_ne_zero.2 hdet
  refine ⟨A₁q⁻¹ * A₂q, ?_⟩
  have h3 : A₁ * (A₁q⁻¹ * A₂q).map (Rat.castHom ℝ) = A₂ := by
    have := congrArg (fun M => M.map (Rat.castHom ℝ)) (Matrix.mul_nonsing_inv_cancel_left A₁q A₂q hdetq)
    rw [Matrix.map_mul, hA₁, hA₂] at this
    exact this
  have h4 : (A₁q⁻¹ * A₂q).map (Rat.castHom ℝ) = T := by
    calc (A₁q⁻¹ * A₂q).map (Rat.castHom ℝ)
        = A₁⁻¹ * (A₁ * (A₁q⁻¹ * A₂q).map (Rat.castHom ℝ)) :=
          (Matrix.nonsing_inv_mul_cancel_left A₁ _ hdetR).symm
      _ = A₁⁻¹ * (A₁ * T) := by rw [h3, key]
      _ = T := Matrix.nonsing_inv_mul_cancel_left A₁ T hdetR
  simpa using h4

end GlobalTheory
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_endo_matrix_rational_in_lattice_basis : ∀ (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ),
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) →
    (∀ k l, ∃ m : ℤ, (m : ℝ) = (e k ⬝ᵥ H₁.mulVec (star (e l))).im) →
    (∀ k l, ∃ m : ℤ, (m : ℝ) = (e k ⬝ᵥ H₂.mulVec (star (e l))).im) →
    ∀ (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
    (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) →
    ∃ Tq : Matrix (Fin n) (Fin n) ℚ,
      Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ) := by
  atlas_forward_decl GlobalTheory.herm_endo_matrix_rat
end

section
section
open Matrix

namespace GlobalTheory.HermGram

noncomputable def reForm {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (z ⬝ᵥ H *ᵥ star w).re)
    (by intro a b c; simp [add_dotProduct])
    (by intro c a b; simp [smul_dotProduct, Complex.smul_re])
    (by intro a b c; simp [star_add, mulVec_add, dotProduct_add])
    (by intro c a b
        have : star (c • b) = c • star b := by
          ext i; simp [Complex.conj_ofReal]
        rw [this, mulVec_smul, dotProduct_smul, Complex.smul_re])

theorem reForm_apply {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    reForm H z w = (z ⬝ᵥ H *ᵥ star w).re := rfl

theorem reForm_symm {g : ℕ} {H : Matrix (Fin g) (Fin g) ℂ} (hH : H.IsHermitian)
    (z w : Fin g → ℂ) : reForm H z w = reForm H w z := by
  simp only [reForm_apply]
  have : star (z ⬝ᵥ H *ᵥ star w) = w ⬝ᵥ H *ᵥ star z := by
    simp only [dotProduct, mulVec, star_sum, star_mul', Pi.star_apply, star_star]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hH.apply i j]; ring
  rw [← this]; simp

theorem gram_posDef {g n : ℕ} (e : Module.Basis (Fin n) ℝ (Fin g → ℂ))
    {H : Matrix (Fin g) (Fin g) ℂ} (hH : H.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H.mulVec (star z)).re) :
    (Matrix.of fun k l => (e k ⬝ᵥ H.mulVec (star (e l))).re).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · ext k l
    simp only [conjTranspose_apply, of_apply, star_trivial]
    exact reForm_symm hH (e l) (e k)
  · intro x hx
    set v : Fin g → ℂ := ∑ k, x k • e k with hvdef
    have hv : v ≠ 0 := by
      intro h0
      apply hx
      apply e.equivFun.symm.injective
      rw [map_zero, Module.Basis.equivFun_symm_apply]
      exact h0
    have key : star x ⬝ᵥ (Matrix.of fun k l => (e k ⬝ᵥ H.mulVec (star (e l))).re) *ᵥ x
        = reForm H v v := by
      rw [hvdef]
      change star x ⬝ᵥ (Matrix.of fun k l => reForm H (e k) (e l)) *ᵥ x = _
      simp only [star_trivial, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, dotProduct, mulVec, of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [reForm_symm hH (e l) (e k)]; ring
    rw [key, reForm_apply]
    exact hpos v hv

theorem gram_posDef_pair (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ)
    (h₁ : H₁.IsHermitian) (h₂ : H₂.IsHermitian)
    (p₁ : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re)
    (p₂ : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₂.mulVec (star z)).re)
    (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hγ : ∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) :
    (Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re).PosDef ∧
    ((Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re) *
      LinearMap.toMatrix e e (γ.restrictScalars ℝ)).PosDef := by
  refine ⟨gram_posDef e h₁ p₁, ?_⟩
  have hG : (Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re) *
      LinearMap.toMatrix e e (γ.restrictScalars ℝ) =
      Matrix.of fun k l => (e k ⬝ᵥ H₂.mulVec (star (e l))).re := by
    ext k l
    rw [of_apply, hγ, mul_apply]
    have hs : γ (e l) = ∑ m, e.repr (γ (e l)) m • e m := (e.sum_repr _).symm
    have : (e k ⬝ᵥ H₁.mulVec (star (γ (e l)))).re = reForm H₁ (e k) (γ (e l)) := rfl
    rw [this, hs]
    simp only [map_sum, map_smul, smul_eq_mul, LinearMap.toMatrix_apply, of_apply,
      LinearMap.restrictScalars_apply, reForm_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [hG]
  exact gram_posDef e h₂ p₂

end GlobalTheory.HermGram
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.posDef_real_gram_pair_hermitian_forms : ∀ (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ), H₁.IsHermitian → H₂.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₂.mulVec (star z)).re) →
    ∀ (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
    (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) →
    (Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re).PosDef ∧
    ((Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re) *
      LinearMap.toMatrix e e (γ.restrictScalars ℝ)).PosDef := by
  atlas_forward_decl GlobalTheory.HermGram.gram_posDef_pair
end

section
section
open Matrix

namespace GlobalTheory

noncomputable def endRealMatrixRingHom {g n : ℕ} (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) :
    Module.End ℂ (Fin g → ℂ) →+* Matrix (Fin n) (Fin n) ℝ where
  toFun f := LinearMap.toMatrix e e (f.restrictScalars ℝ)
  map_one' := by
    have : ((1 : Module.End ℂ (Fin g → ℂ)).restrictScalars ℝ) = 1 := rfl
    rw [this]; exact LinearMap.toMatrix_one e
  map_mul' f h := by
    have : ((f * h).restrictScalars ℝ) = f.restrictScalars ℝ * h.restrictScalars ℝ := rfl
    rw [this]; exact LinearMap.toMatrix_mul e _ _
  map_zero' := by
    have : ((0 : Module.End ℂ (Fin g → ℂ)).restrictScalars ℝ) = 0 := rfl
    rw [this]; exact map_zero _
  map_add' f h := by
    have : ((f + h).restrictScalars ℝ) = f.restrictScalars ℝ + h.restrictScalars ℝ := rfl
    rw [this]; exact map_add _ _ _

theorem endRealMatrixRingHom_injective {g n : ℕ} (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) :
    Function.Injective (endRealMatrixRingHom e) := by
  intro f h hfh
  have h1 : f.restrictScalars ℝ = h.restrictScalars ℝ := (LinearMap.toMatrix e e).injective hfh
  exact LinearMap.restrictScalars_injective ℝ h1

theorem matrix_identity_transfer (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ))
    (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Tq : Matrix (Fin n) (Fin n) ℚ)
    (hT : Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ))
    (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ)
    (hid : (1 : Matrix (Fin n) (Fin n) ℚ) = c₀ • Tq + ∑ i, c i • ((Polynomial.aeval Tq (p i)) ^ 2 * Tq)) :
    (1 : Module.End ℂ (Fin g → ℂ)) = c₀ • γ + ∑ i, c i • ((Polynomial.aeval γ (p i)) ^ 2 * γ) := by
  let F := (endRealMatrixRingHom e).toRatAlgHom
  let ψ : Matrix (Fin n) (Fin n) ℚ →ₐ[ℚ] Matrix (Fin n) (Fin n) ℝ := (Algebra.ofId ℚ ℝ).mapMatrix
  have hψ : ∀ M, ψ M = M.map (Rat.cast : ℚ → ℝ) := by
    intro M; ext i j; simp [ψ]
  have hFγ : F γ = ψ Tq := by rw [hψ, hT]; rfl
  apply endRealMatrixRingHom_injective e
  change F 1 = F _
  have key := congrArg ψ hid
  rw [map_one] at key
  rw [map_one, key]
  simp only [map_add, map_sum, map_smul, map_mul, map_pow, ← Polynomial.aeval_algHom_apply, hFγ]

end GlobalTheory
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_matrix_identity_transfer_to_complex_map : ∀ (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Tq : Matrix (Fin n) (Fin n) ℚ),
    Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ) →
    ∀ (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ),
    (1 : Matrix (Fin n) (Fin n) ℚ) = c₀ • Tq + ∑ i, c i • ((Polynomial.aeval Tq (p i)) ^ 2 * Tq) →
    (1 : Module.End ℂ (Fin g → ℂ)) = c₀ • γ + ∑ i, c i • ((Polynomial.aeval γ (p i)) ^ 2 * γ) := by
  atlas_forward_decl GlobalTheory.matrix_identity_transfer
end

section
section
open Matrix

namespace GlobalTheory

theorem herm_form_identity (g : ℕ) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ)
    (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h1 : ∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w)))
    (h2 : ∀ z w, z ⬝ᵥ H₂.mulVec (star (γ w)) = γ z ⬝ᵥ H₂.mulVec (star w))
    (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ)
    (hid : (1 : Module.End ℂ (Fin g → ℂ)) = c₀ • γ + ∑ i, c i • ((Polynomial.aeval γ (p i)) ^ 2 * γ))
    (z w : Fin g → ℂ) :
    z ⬝ᵥ H₁.mulVec (star w) = (c₀ : ℂ) * (z ⬝ᵥ H₂.mulVec (star w)) +
      ∑ i, (c i : ℂ) * (Polynomial.aeval γ (p i) z ⬝ᵥ H₂.mulVec (star (Polynomial.aeval γ (p i) w))) := by
  have hadd : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (z u v : Fin g → ℂ),
      z ⬝ᵥ H.mulVec (star (u + v)) = z ⬝ᵥ H.mulVec (star u) + z ⬝ᵥ H.mulVec (star v) := by
    intro H z u v; rw [star_add, mulVec_add, dotProduct_add]
  have hsmul : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (z v : Fin g → ℂ) (a : ℚ),
      z ⬝ᵥ H.mulVec (star (a • v)) = (a : ℂ) * (z ⬝ᵥ H.mulVec (star v)) := by
    intro H z v a
    rw [← Rat.cast_smul_eq_qsmul ℂ, star_smul, mulVec_smul, dotProduct_smul, smul_eq_mul]
    simp
  have hsmulL : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (z v : Fin g → ℂ) (a : ℚ),
      (a • z) ⬝ᵥ H.mulVec (star v) = (a : ℂ) * (z ⬝ᵥ H.mulVec (star v)) := by
    intro H z v a
    rw [← Rat.cast_smul_eq_qsmul ℂ, smul_dotProduct, smul_eq_mul]
  have hsum : ∀ (H : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) (f : Fin r → (Fin g → ℂ)),
      z ⬝ᵥ H.mulVec (star (∑ i, f i)) = ∑ i, z ⬝ᵥ H.mulVec (star (f i)) := by
    intro H z f
    rw [star_sum, mulVec_sum, dotProduct_sum]
  have hsa : ∀ (q : Polynomial ℚ) (z w : Fin g → ℂ),
      z ⬝ᵥ H₂.mulVec (star (Polynomial.aeval γ q w)) =
        Polynomial.aeval γ q z ⬝ᵥ H₂.mulVec (star w) := by
    intro q
    induction q using Polynomial.induction_on with
    | C a =>
      intro z w
      simp only [Polynomial.aeval_C, Module.algebraMap_end_apply]
      rw [hsmul, hsmulL]
    | add p q hp hq =>
      intro z w
      simp only [map_add, LinearMap.add_apply]
      rw [hadd, hp, hq, add_dotProduct]
    | monomial n a ih =>
      intro z w
      have e : Polynomial.C a * Polynomial.X ^ (n+1) =
          (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
      have e' : Polynomial.C a * Polynomial.X ^ (n+1) =
          Polynomial.X * (Polynomial.C a * Polynomial.X ^ n) := by ring
      calc z ⬝ᵥ H₂.mulVec (star (Polynomial.aeval γ (Polynomial.C a * Polynomial.X ^ (n+1)) w))
          = z ⬝ᵥ H₂.mulVec (star (Polynomial.aeval γ (Polynomial.C a * Polynomial.X ^ n) (γ w))) := by
            rw [e, map_mul (Polynomial.aeval γ) (Polynomial.C a * Polynomial.X ^ n) Polynomial.X,
              Polynomial.aeval_X, Module.End.mul_apply]
        _ = Polynomial.aeval γ (Polynomial.C a * Polynomial.X ^ n) z ⬝ᵥ H₂.mulVec (star (γ w)) :=
            ih _ _
        _ = γ (Polynomial.aeval γ (Polynomial.C a * Polynomial.X ^ n) z) ⬝ᵥ H₂.mulVec (star w) :=
            h2 _ _
        _ = _ := by
            rw [e', map_mul (Polynomial.aeval γ) Polynomial.X (Polynomial.C a * Polynomial.X ^ n),
              Polynomial.aeval_X, Module.End.mul_apply]
  have comm : ∀ q : Polynomial ℚ, (Polynomial.aeval γ q) ^ 2 * γ =
      γ * (Polynomial.aeval γ q * Polynomial.aeval γ q) := by
    intro q
    rw [show (Polynomial.aeval γ q) ^ 2 * γ = Polynomial.aeval γ (q ^ 2 * Polynomial.X) by
          simp [map_mul, map_pow],
      show q ^ 2 * Polynomial.X = Polynomial.X * (q * q) by ring]
    simp [map_mul]
  have hw : w = c₀ • γ w + ∑ i, c i • (γ (Polynomial.aeval γ (p i) (Polynomial.aeval γ (p i) w))) := by
    have := congrArg (fun f : Module.End ℂ (Fin g → ℂ) => f w) hid
    simp only [Module.End.one_apply, LinearMap.add_apply, LinearMap.smul_apply,
      comm] at this
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply] at this
    exact this
  conv_lhs => rw [hw]
  rw [hadd, hsmul, hsum, ← h1]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsmul, ← h1, hsa]

end GlobalTheory
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_eq_combination_of_selfAdjoint_identity : ∀ (g : ℕ) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ) (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
    (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) →
    (∀ z w, z ⬝ᵥ H₂.mulVec (star (γ w)) = γ z ⬝ᵥ H₂.mulVec (star w)) →
    ∀ (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ),
    (1 : Module.End ℂ (Fin g → ℂ)) = c₀ • γ + ∑ i, c i • ((Polynomial.aeval γ (p i)) ^ 2 * γ) →
    ∀ z w : Fin g → ℂ, z ⬝ᵥ H₁.mulVec (star w) = (c₀ : ℂ) * (z ⬝ᵥ H₂.mulVec (star w)) +
      ∑ i, (c i : ℂ) * (Polynomial.aeval γ (p i) z ⬝ᵥ H₂.mulVec (star (Polynomial.aeval γ (p i) w))) := by
  atlas_forward_decl GlobalTheory.herm_form_identity
end

section
section
open Matrix

namespace GlobalTheory

theorem nsmul_aeval_mem_lattice_of_intMatrix_basis (g n : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ))
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ k, ∃ m : ℤ, e.repr x k = m)
    (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Tq : Matrix (Fin n) (Fin n) ℚ)
    (hT : Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ))
    (p : Polynomial ℚ) (D : ℕ) (hD : ∀ k l, ∃ m : ℤ, (D : ℚ) * Polynomial.aeval Tq p k l = m) :
    ∀ x ∈ Λ, (D • Polynomial.aeval γ p) x ∈ Λ := by
  let φ : Module.End ℂ (Fin g → ℂ) →ₐ[ℚ] Matrix (Fin n) (Fin n) ℝ :=
    { toFun := fun f => LinearMap.toMatrix e e (f.restrictScalars ℝ)
      map_one' := by
        rw [show ((1 : Module.End ℂ (Fin g → ℂ)).restrictScalars ℝ) = 1 from rfl]
        exact LinearMap.toMatrix_one e
      map_mul' := fun f h => by
        rw [show ((f * h).restrictScalars ℝ) = (f.restrictScalars ℝ) * (h.restrictScalars ℝ) from rfl]
        exact LinearMap.toMatrix_mul e _ _
      map_zero' := by
        rw [show ((0 : Module.End ℂ (Fin g → ℂ)).restrictScalars ℝ) = 0 from rfl]
        simp
      map_add' := fun f h => by
        rw [show ((f + h).restrictScalars ℝ) = (f.restrictScalars ℝ) + (h.restrictScalars ℝ) from rfl]
        simp
      commutes' := fun r => by
        have : ((algebraMap ℚ (Module.End ℂ (Fin g → ℂ)) r).restrictScalars ℝ) = algebraMap ℝ (Module.End ℝ (Fin g → ℂ)) (r : ℝ) := by
          refine LinearMap.ext fun x => funext fun i => ?_
          simp [Module.algebraMap_end_apply, Rat.smul_def]
        rw [this, LinearMap.toMatrix_algebraMap]
        ext i j
        simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply]
        }
  let ψ : Matrix (Fin n) (Fin n) ℚ →ₐ[ℚ] Matrix (Fin n) (Fin n) ℝ := (Algebra.ofId ℚ ℝ).mapMatrix
  have hψ : ∀ M : Matrix (Fin n) (Fin n) ℚ, ψ M = M.map (Rat.cast : ℚ → ℝ) := by
    intro M
    ext i j
    simp [ψ]
  have hφ : ∀ f : Module.End ℂ (Fin g → ℂ), φ f = LinearMap.toMatrix e e (f.restrictScalars ℝ) :=
    fun f => rfl
  have key : LinearMap.toMatrix e e ((Polynomial.aeval γ p).restrictScalars ℝ)
      = (Polynomial.aeval Tq p).map (Rat.cast : ℚ → ℝ) := by
    rw [← hφ, ← hψ, ← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply, hφ, hψ, hT]
  intro x hx
  choose m hm using (hΛ x).mp hx
  choose z hz using hD
  rw [hΛ]
  intro k
  refine ⟨∑ l, z k l * m l, ?_⟩
  have hv : ⇑(e.repr ((Polynomial.aeval γ p) x))
      = (Polynomial.aeval Tq p).map (Rat.cast : ℚ → ℝ) *ᵥ ⇑(e.repr x) := by
    rw [← key, LinearMap.toMatrix_mulVec_repr]
    rfl
  rw [LinearMap.smul_apply, map_nsmul, Finsupp.smul_apply, hv]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hm, nsmul_eq_mul, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun l _ => ?_
  have := congrArg (Rat.cast : ℚ → ℝ) (hz k l)
  push_cast at this
  rw [← this]
  ring

theorem nsmul_aeval_mem_lattice_of_intMatrix : ∀ (g n : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)),
    (∀ x, x ∈ Λ ↔ ∀ k, ∃ m : ℤ, e.repr x k = m) →
    ∀ (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Tq : Matrix (Fin n) (Fin n) ℚ),
    Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ) →
    ∀ (p : Polynomial ℚ) (D : ℕ), (∀ k l, ∃ m : ℤ, (D : ℚ) * Polynomial.aeval Tq p k l = m) →
    ∀ x ∈ Λ, (D • Polynomial.aeval γ p) x ∈ Λ :=
  fun g n Λ e hΛ γ Tq hT p D hD => nsmul_aeval_mem_lattice_of_intMatrix_basis g n Λ e hΛ γ Tq hT p D hD

end GlobalTheory
end

open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nsmul_aeval_mem_lattice_of_int_rational_matrix : ∀ (g n : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)),
    (∀ x, x ∈ Λ ↔ ∀ k, ∃ m : ℤ, e.repr x k = m) →
    ∀ (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Tq : Matrix (Fin n) (Fin n) ℚ),
    Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ) →
    ∀ (p : Polynomial ℚ) (D : ℕ), (∀ k l, ∃ m : ℤ, (D : ℚ) * Polynomial.aeval Tq p k l = m) →
    ∀ x ∈ Λ, (D • Polynomial.aeval γ p) x ∈ Λ := by
  atlas_forward_decl GlobalTheory.nsmul_aeval_mem_lattice_of_intMatrix
end

section
section
open Matrix

namespace GlobalTheory.Desc.HermComb

theorem lat_basis (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (hd : DiscreteTopology Λ)
    (hs : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) :
    ∃ (n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)),
      ∀ x, x ∈ Λ ↔ ∀ k, ∃ m : ℤ, e.repr x k = m := by
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  let b := Module.finBasis ℤ Λ
  refine ⟨_, b.ofZLatticeBasis ℝ Λ, fun x => ⟨fun hx k => ⟨b.repr ⟨x, hx⟩ k, ?_⟩, fun h => ?_⟩⟩
  · exact b.ofZLatticeBasis_repr_apply ℝ Λ ⟨x, hx⟩ k
  · choose m hm using h
    have hx : x = ∑ k, m k • (b k : Fin g → ℂ) := by
      conv_lhs => rw [← (b.ofZLatticeBasis ℝ Λ).sum_repr x]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hm k, Module.Basis.ofZLatticeBasis_apply, Int.cast_smul_eq_zsmul]
    rw [hx]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (b k).2

theorem int_of_den_dvd (q : ℚ) (D : ℕ) (h : q.den ∣ D) : ∃ m : ℤ, (D : ℚ) * q = m := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨k * q.num, ?_⟩
  push_cast
  rw [mul_comm (q.den : ℚ) k, mul_assoc, mul_comm (q.den : ℚ), Rat.mul_den_eq_num]

theorem common_den (n r : ℕ) (c₀ : ℚ) (c : Fin r → ℚ) (M : Fin r → Matrix (Fin n) (Fin n) ℚ) :
    ∃ D : ℕ, 1 ≤ D ∧ (∃ m : ℤ, (D : ℚ) * c₀ = m) ∧ (∀ i, ∃ m : ℤ, (D : ℚ) * c i = m) ∧
      ∀ i k l, ∃ m : ℤ, (D : ℚ) * M i k l = m := by
  classical
  let S : Finset ℚ := insert c₀ (Finset.univ.image c ∪
    Finset.univ.image (fun x : Fin r × Fin n × Fin n => M x.1 x.2.1 x.2.2))
  have hdv : ∀ q ∈ S, q.den ∣ ∏ q ∈ S, q.den := fun q hq => Finset.dvd_prod_of_mem _ hq
  refine ⟨∏ q ∈ S, q.den, Finset.prod_pos fun (q : ℚ) _ => q.den_pos, int_of_den_dvd _ _ (hdv _ ?_),
    fun i => int_of_den_dvd _ _ (hdv _ ?_), fun i k l => int_of_den_dvd _ _ (hdv _ ?_)⟩
  · simp [S]
  · simp [S]
  · simp only [S, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr (Or.inr ⟨(i, k, l), rfl⟩)

end GlobalTheory.Desc.HermComb

namespace GlobalTheory.Desc.HermComb

theorem main : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    ∀ (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ), H₁.IsHermitian → H₂.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₂.mulVec (star z)).re) →
    (∀ l ∈ Λ, ∀ m ∈ Λ, ∃ n : ℤ, (n : ℝ) = (l ⬝ᵥ H₁.mulVec (star m)).im) →
    (∀ l ∈ Λ, ∀ m ∈ Λ, ∃ n : ℤ, (n : ℝ) = (l ⬝ᵥ H₂.mulVec (star m)).im) →
    ∃ (N a₀ r : ℕ) (a : Fin r → ℕ) (F : Fin r → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), 1 ≤ N ∧ 1 ≤ a₀ ∧ Even N ∧ Even a₀ ∧
      (∀ i, Even (a i)) ∧ (∀ i, ∀ l ∈ Λ, F i l ∈ Λ) ∧
      ∀ z w : Fin g → ℂ, (N : ℂ) * (z ⬝ᵥ H₁.mulVec (star w)) =
        (a₀ : ℂ) * (z ⬝ᵥ H₂.mulVec (star w)) + ∑ i, (a i : ℂ) * (F i z ⬝ᵥ H₂.mulVec (star (F i w))) := by
  intro g Λ hd hs H₁ H₂ h₁ h₂ hp₁ hp₂ hi₁ hi₂
  obtain ⟨n, e, he⟩ := lat_basis g Λ hd hs
  have hek : ∀ k, e k ∈ Λ := fun k => (he _).2 fun j =>
    ⟨if k = j then 1 else 0, by rw [e.repr_self, Finsupp.single_apply]; split_ifs <;> simp⟩
  obtain ⟨γ, hγ, hsa⟩ := GlobalTheory.T.exists_selfAdjoint_endo_relating_hermitian_forms g H₁ H₂ h₁ h₂ hp₁
  obtain ⟨Tq, hT⟩ := GlobalTheory.T.hermitian_endo_matrix_rational_in_lattice_basis g n e H₁ H₂ hp₁ (fun k l => hi₁ _ (hek k) _ (hek l))
    (fun k l => hi₂ _ (hek k) _ (hek l)) γ hγ
  obtain ⟨hB, hBT⟩ := GlobalTheory.T.posDef_real_gram_pair_hermitian_forms g n e H₁ H₂ h₁ h₂ hp₁ hp₂ γ hγ
  rw [← hT] at hBT
  obtain ⟨c₀, r, c, p, hc₀, hc, hid⟩ := GlobalTheory.T.exists_unit_eq_positive_squares_times_selfAdjoint n Tq _ hB hBT
  have hform := GlobalTheory.T.hermitian_form_eq_combination_of_selfAdjoint_identity g H₁ H₂ γ hγ hsa c₀ r c p (GlobalTheory.T.rational_matrix_identity_transfer_to_complex_map g n e γ Tq hT c₀ r c p hid)
  obtain ⟨D, hD1, ⟨m₀, hm₀⟩, hci, hM⟩ := common_den n r c₀ c (fun i => Polynomial.aeval Tq (p i))
  choose m hm using hci
  have hm₀p : 0 < m₀ := by
    have : (0 : ℚ) < m₀ := by rw [← hm₀]; exact mul_pos (by exact_mod_cast hD1) hc₀
    exact_mod_cast this
  have hmp : ∀ i, 0 ≤ m i := fun i => by
    have : (0 : ℚ) ≤ m i := by rw [← hm i]; exact (mul_pos (by exact_mod_cast hD1) (hc i)).le
    exact_mod_cast this
  refine ⟨2 * D ^ 3, 2 * D ^ 2 * m₀.toNat, r, fun i => 2 * (m i).toNat,
    fun i => D • Polynomial.aeval γ (p i), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : 1 ≤ D ^ 3 := Nat.one_le_pow _ _ hD1; omega
  · have h1 : 1 ≤ D ^ 2 := Nat.one_le_pow _ _ hD1
    have h2 : 1 ≤ m₀.toNat := by omega
    nlinarith
  · exact even_two_mul _
  · rw [mul_assoc]; exact even_two_mul _
  · exact fun i => even_two_mul _
  · exact fun i => GlobalTheory.T.nsmul_aeval_mem_lattice_of_int_rational_matrix g n Λ e he γ Tq hT (p i) D (hM i)
  · intro z w
    have hm₀' : ((m₀.toNat : ℕ) : ℂ) = (D : ℂ) * (c₀ : ℂ) := by
      have : ((m₀.toNat : ℤ) : ℚ) = (D : ℚ) * c₀ := by rw [Int.toNat_of_nonneg hm₀p.le, hm₀]
      exact_mod_cast congrArg (fun q : ℚ => (q : ℂ)) this
    have hm' : ∀ i, (((m i).toNat : ℕ) : ℂ) = (D : ℂ) * (c i : ℂ) := fun i => by
      have : (((m i).toNat : ℤ) : ℚ) = (D : ℚ) * c i := by rw [Int.toNat_of_nonneg (hmp i), hm i]
      exact_mod_cast congrArg (fun q : ℚ => (q : ℂ)) this
    have hsc : ∀ a b : Fin g → ℂ, (D • a) ⬝ᵥ H₂.mulVec (star (D • b)) = (D : ℂ) * D * (a ⬝ᵥ H₂.mulVec (star b)) := by
      intro a b
      rw [star_nsmul, mulVec_smul, dotProduct_smul, smul_dotProduct, nsmul_eq_mul, nsmul_eq_mul]; ring
    simp only [LinearMap.smul_apply, hsc]
    rw [hform z w]
    push_cast [hm₀', hm']
    rw [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      ring

end GlobalTheory.Desc.HermComb
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_even_multiple_hermitian_positive_combination : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    ∀ (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ), H₁.IsHermitian → H₂.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₂.mulVec (star z)).re) →
    (∀ l ∈ Λ, ∀ m ∈ Λ, ∃ n : ℤ, (n : ℝ) = (l ⬝ᵥ H₁.mulVec (star m)).im) →
    (∀ l ∈ Λ, ∀ m ∈ Λ, ∃ n : ℤ, (n : ℝ) = (l ⬝ᵥ H₂.mulVec (star m)).im) →
    ∃ (N a₀ r : ℕ) (a : Fin r → ℕ) (F : Fin r → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), 1 ≤ N ∧ 1 ≤ a₀ ∧ Even N ∧ Even a₀ ∧
      (∀ i, Even (a i)) ∧ (∀ i, ∀ l ∈ Λ, F i l ∈ Λ) ∧
      ∀ z w : Fin g → ℂ, (N : ℂ) * (z ⬝ᵥ H₁.mulVec (star w)) =
        (a₀ : ℂ) * (z ⬝ᵥ H₂.mulVec (star w)) + ∑ i, (a i : ℂ) * (F i z ⬝ᵥ H₂.mulVec (star (F i w))) := by
  atlas_forward_decl GlobalTheory.Desc.HermComb.main
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.UnifEndo

theorem exists_isMonHom_of_map_lattice : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g : ℕ) (u : HolUnif A L g)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ l ∈ u.Λ, F l ∈ u.Λ) → ∃ f : A ⟶ A, IsMonHom f ∧ ∀ z, u.ex (F z) = u.ex z ≫ f := by
  intro A _ hA L g u F hF
  exact GlobalTheory.HolUnifEnd.exists_isMonHom_of_map_lattice A g hA
    (GlobalTheory.TorusAction.smoothOfRelativeDimension_of_holUnif A hA u) L u F hF

end GlobalTheory.UnifEndo
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_endomorphism_of_lattice_preserving_linear : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (g : ℕ) (u : HolUnif A L g)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ l ∈ u.Λ, F l ∈ u.Λ) → ∃ f : A ⟶ A, IsMonHom f ∧ ∀ z, u.ex (F z) = u.ex z ≫ f := by
  atlas_forward_decl GlobalTheory.UnifEndo.exists_isMonHom_of_map_lattice
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SqDecC

theorem frame_power_identity : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L M : LB A.left) (g : ℕ) (uL : HolUnif A L g) (uM : HolUnif A M g)
    (HL HM : Matrix (Fin g) (Fin g) ℂ) (χL : uL.Λ → ℂ) (χM : uM.Λ → ℂ), uM.ex = uL.ex →
    GlobalTheory.TorusRM.IsFactorAH uL HL χL → GlobalTheory.TorusRM.IsFactorAH uM HM χM →
    (∀ l, χL l = 1 ∨ χL l = -1) → (∀ l, χM l = 1 ∨ χM l = -1) →
    ∀ (N : ℕ) (K : Type) [Fintype K] (F : K → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ε : K → ℤ), Even N → (∀ k, Even (ε k)) →
    (∀ k, ∀ l ∈ uL.Λ, F k l ∈ uM.Λ) →
    (∀ z w : Fin g → ℂ, (N : ℂ) * (z ⬝ᵥ HL.mulVec (star w)) = ∑ k, (ε k : ℂ) * (F k z ⬝ᵥ HM.mulVec (star (F k w)))) →
    ∀ (l : uL.Λ) (i : L.ι) (j : K → M.ι) (z : Fin g → ℂ), ⊤ ≤ (uL.ex z).left ⁻¹ᵁ L.U i →
      (∀ k, ⊤ ≤ (uM.ex (F k z)).left ⁻¹ᵁ M.U (j k)) →
      uL.fr i z ^ N * ∏ k, uM.fr (j k) (F k (z + l)) ^ ε k = uL.fr i (z + l) ^ N * ∏ k, uM.fr (j k) (F k z) ^ ε k := by
  intro A _ L M g uL uM HL HM χL χM _ hfL hfM hχL hχM N K _ F ε hN hε hF hdec l i j z hi hj
  have hL1 := hfL.2.2 l i z hi
  have hM1 : ∀ k, uM.fr (j k) (F k z) = χM ⟨F k l, hF k l l.2⟩ *
      Complex.exp (Real.pi * (F k z ⬝ᵥ HM.mulVec (star (F k l))) +
        Real.pi / 2 * (F k l ⬝ᵥ HM.mulVec (star (F k l)))) * uM.fr (j k) (F k (z + l)) := fun k => by
    rw [map_add]
    exact hfM.2.2 ⟨F k l, hF k l l.2⟩ (j k) (F k z) (hj k)
  have hcL : χL l ^ N = 1 := by
    rcases hχL l with h | h <;> rw [h]
    · exact one_pow N
    · exact hN.neg_one_pow
  have hcM : ∀ k, χM ⟨F k l, hF k l l.2⟩ ^ ε k = 1 := fun k => by
    rcases hχM ⟨F k l, hF k l l.2⟩ with h | h <;> rw [h]
    · exact one_zpow _
    · exact (hε k).neg_one_zpow
  have hR : ∏ k, uM.fr (j k) (F k z) ^ ε k = (∏ k, χM ⟨F k l, hF k l l.2⟩ ^ ε k) *
      (∏ k, Complex.exp (Real.pi * (F k z ⬝ᵥ HM.mulVec (star (F k l))) +
        Real.pi / 2 * (F k l ⬝ᵥ HM.mulVec (star (F k l)))) ^ ε k) * ∏ k, uM.fr (j k) (F k (z + l)) ^ ε k := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hM1 k, mul_zpow, mul_zpow]
  have key : Complex.exp (Real.pi * (z ⬝ᵥ HL.mulVec (star (l : Fin g → ℂ))) +
      Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ HL.mulVec (star (l : Fin g → ℂ)))) ^ N =
      ∏ k, Complex.exp (Real.pi * (F k z ⬝ᵥ HM.mulVec (star (F k l))) +
        Real.pi / 2 * (F k l ⬝ᵥ HM.mulVec (star (F k l)))) ^ ε k := by
    rw [← Complex.exp_nat_mul, Finset.prod_congr rfl (fun k _ => (Complex.exp_int_mul _ (ε k)).symm),
      ← Complex.exp_sum]
    congr 1
    have h1 := hdec z l
    have h2 := hdec l l
    calc (N : ℂ) * (Real.pi * (z ⬝ᵥ HL.mulVec (star (l : Fin g → ℂ))) +
          Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ HL.mulVec (star (l : Fin g → ℂ))))
        = Real.pi * ((N : ℂ) * (z ⬝ᵥ HL.mulVec (star (l : Fin g → ℂ)))) +
          Real.pi / 2 * ((N : ℂ) * ((l : Fin g → ℂ) ⬝ᵥ HL.mulVec (star (l : Fin g → ℂ)))) := by ring
      _ = Real.pi * ∑ k, (ε k : ℂ) * (F k z ⬝ᵥ HM.mulVec (star (F k l))) +
          Real.pi / 2 * ∑ k, (ε k : ℂ) * (F k l ⬝ᵥ HM.mulVec (star (F k l))) := by rw [h1, h2]
      _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
  rw [hR, hL1, mul_pow, mul_pow, hcL, Finset.prod_eq_one (fun k _ => hcM k), key]
  ring

theorem lbIso_of_sameFactor (A : Over (Sp ℂ)) [GrpObj A] (hA : IsAbelianScheme A) (X Y : LB A.left) (g : ℕ)
    (u : HolUnif A X g) (v : HolUnif A Y g) (hX : X.IsLB) (hY : Y.IsLB) (hex : v.ex = u.ex)
    (hper : ∀ (l : u.Λ) i j z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ X.U i → ⊤ ≤ (u.ex z).left ⁻¹ᵁ Y.U j →
      u.fr i z * v.fr j (z + l) = u.fr i (z + l) * v.fr j z) : LBIso X Y := by
  haveI := hA.comm
  haveI := hA.smooth
  have hp : IsProjOver A.hom := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver A.hom).1
    (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA)
  obtain ⟨s, hs⟩ := HolUnifSec.exists_isFn (SameFactor.divUnif u v hex) hA hp (LB.isLB_div hY hX)
    (θ := fun _ => 1) (differentiable_const _) (by
      intro l hl p z hz
      obtain ⟨hz1, hz2⟩ := (top_le_preimage_inf _ _ _).1 hz
      have e := hper ⟨l, hl⟩ p.2 p.1 z hz2 hz1
      have hl' : u.ex (z + l) = u.ex z := by
        rw [u.ex_add, (u.ker _).2 hl, _root_.mul_one]
      have n1 := u.fr_ne p.2 z hz2
      have n2 := u.fr_ne p.2 (z + l) (by rw [hl']; exact hz2)
      change 1 * (v.fr p.1 (z + l) * (u.fr p.2 (z + l))⁻¹) = 1 * (v.fr p.1 z * (u.fr p.2 z)⁻¹)
      field_simp
      linear_combination e)
  exact SameFactor.exists_gen_of_isFn _ s _ hs fun _ => one_ne_zero

theorem sqDec_complex : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L M : LB A.left), L.IsLB → M.IsLB →
    RelAmple A L → RelAmple A M → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L →
    LBIso (M.pull (GrpObj.inv : A ⟶ A).left) M → SqDec A L M := by
  intro A _ hA L M hL hM haL haM hsL hsM
  haveI := hA.comm
  obtain ⟨g, hg⟩ := AbelianDim.exists_relDim ℂ A hA
  obtain ⟨L₀, ⟨u₀⟩⟩ := HomDescentQb.exists_holUnif A g hA hg
  obtain ⟨uL, HL, χL, hexL, hfL⟩ := exists_isFactorAH_frame_of_unif A hA L₀ g u₀ L hL
  obtain ⟨uM, HM, χM, hexM, hfM⟩ := exists_isFactorAH_frame_of_unif A hA L₀ g u₀ M hM
  have hposL := AmpleHermPos.re_form_pos_of_relAmple A hA L hL haL g uL HL χL hfL.1 hfL.2.1 hfL.2.2
  have hposM := AmpleHermPos.re_form_pos_of_relAmple A hA M hM haM g uM HM χM hfM.1 hfM.2.1 hfM.2.2
  have hAHL := TorusRM.isAH_of_isFactorAH hfL hposL
  have hAHM := TorusRM.isAH_of_isFactorAH hfM hposM
  have hex : uM.ex = uL.ex := hexM.trans hexL.symm
  have hΛ : ∀ z, z ∈ uM.Λ ↔ z ∈ uL.Λ := fun z => by rw [← uM.ker, ← uL.ker, hex]
  have hχL := ThetaUnifCompare.chi_eq_one_or_of_sym hL (sym_of_lbIso_neg hsL.symm) hAHL
  have hχM := ThetaUnifCompare.chi_eq_one_or_of_sym hM (sym_of_lbIso_neg hsM.symm) hAHM
  have hiL : ∀ l ∈ uL.Λ, ∀ m ∈ uL.Λ, ∃ n : ℤ, (n : ℝ) = (l ⬝ᵥ HL.mulVec (star m)).im :=
    fun l hl m hm => FrameValue.exists_int_im hL hAHL ⟨l, hl⟩ ⟨m, hm⟩
  have hiM : ∀ l ∈ uL.Λ, ∀ m ∈ uL.Λ, ∃ n : ℤ, (n : ℝ) = (l ⬝ᵥ HM.mulVec (star m)).im :=
    fun l hl m hm => FrameValue.exists_int_im hM hAHM ⟨l, (hΛ l).2 hl⟩ ⟨m, (hΛ m).2 hm⟩
  obtain ⟨N, a₀, r, a, F, hN, ha₀, hNe, ha₀e, hae, hF, hdec⟩ :=
    GlobalTheory.T.exists_even_multiple_hermitian_positive_combination g uL.Λ uL.discrete uL.full HL HM hAHL.1 hAHM.1 hposL hposM hiL hiM
  choose β hβ hβF using fun i => GlobalTheory.T.exists_endomorphism_of_lattice_preserving_linear A hA L g uL (F i) (hF i)
  let f : Option (Fin r) → (A ⟶ A) := fun o => o.elim (𝟙 A) β
  let FF : Option (Fin r) → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := fun o => o.elim LinearMap.id F
  let ε : Option (Fin r) → ℤ := fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)
  have hfF : ∀ k z, uM.ex (FF k z) = uL.ex z ≫ f k := by
    intro k z
    cases k with
    | none => simp [FF, f, hex]
    | some i => simpa [FF, f, hex] using hβF i z
  obtain ⟨u₁, hex₁, -, hfr₁⟩ := exists_holUnif_linComb A A L M g g uL uM _ f FF ε hfF
  have hcomb : LB.LinComb M (fun k => (f k).left) ε = LB.LinComb M (fun (o : Option (Fin r)) => o.elim (𝟙 A.left) fun i => (β i).left)
      (fun (o : Option (Fin r)) => o.elim (a₀ : ℤ) fun i => (a i : ℤ)) := by
    congr 1
    funext o
    cases o <;> rfl
  refine ⟨N, a₀, r, a, β, hN, ha₀, hβ, ?_⟩
  rw [← hcomb]
  refine lbIso_of_sameFactor A hA _ _ g (ThetaGAGA.powFrame uL N) u₁ (isLB_lbPow hL N) (LB.isLB_linComb hM _ _)
    hex₁ ?_
  intro l i j z hi hj
  refine (congrArg₂ (· * ·) rfl (hfr₁ j (z + l))).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (hfr₁ j z)).symm)
  have hi' := ThetaGAGA.top_le_of_lbPow uL N i hi
  have hj' : ∀ k, ⊤ ≤ (uM.ex (FF k z)).left ⁻¹ᵁ M.U (j k) := fun k => by
    rw [hfF k z]
    exact (CubeValues.le_preimage_wchart (uL.ex z).left M (fun k => (f k).left) j).1 hj k
  exact frame_power_identity A L M g uL uM HL HM χL χM hex hfL hfM hχL hχM N _ FF ε hNe
    (fun k => by cases k with | none => exact (Int.even_coe_nat _).2 ha₀e | some i => exact (Int.even_coe_nat _).2 (hae i))
    (fun k l hl => by cases k with | none => exact (hΛ l).2 hl | some i => exact (hΛ _).2 (hF i l hl))
    (fun z w => by rw [Fintype.sum_option, hdec z w]; simp [FF, ε]) l (i PUnit.unit) j z hi' hj'

end GlobalTheory.SqDecC
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_symmetricAmple_square_decomposition : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L M : LB A.left), L.IsLB → M.IsLB → RelAmple A L → RelAmple A M → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso (M.pull (GrpObj.inv : A ⟶ A).left) M → SqDec A L M := by
  atlas_forward_decl GlobalTheory.SqDecC.sqDec_complex
end
