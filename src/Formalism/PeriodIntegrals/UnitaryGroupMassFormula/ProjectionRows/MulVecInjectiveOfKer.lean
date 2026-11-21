import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionRows.Pieces

noncomputable section

namespace PI.DvRows

namespace GramDeterminantPositive

open Matrix
open scoped ComplexOrder

section Mat

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma psd_det_real {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    A.det = ((A.det.re : ℝ) : ℂ) ∧ 0 ≤ A.det.re := by
  have h := hA.det_nonneg
  rw [Complex.nonneg_iff] at h
  exact ⟨Complex.ext (by simp) (by simp [← h.2]), h.1⟩




variable {m : Type*} [Fintype m] [DecidableEq m]


theorem gram_block {k d : Type*} [Fintype k] [DecidableEq k] [Fintype d] [DecidableEq d]
    (Uc : Matrix m k ℂ) (Zc Ac : Matrix m d ℂ) (T : Matrix (k ⊕ d) d ℂ)
    (hT : Ac = fromCols Uc Zc * T) (hAU : Acᴴ * Uc = 0) (hg : (Ucᴴ * Uc).det ≠ 0) :
    (Ucᴴ * Uc).det * ((Acᴴ * Zc).det * star (Acᴴ * Zc).det) =
      (Acᴴ * Ac).det * ((fromCols Uc Zc)ᴴ * fromCols Uc Zc).det := by
  set B := fromCols Uc Zc with hBdef
  set Rm : Matrix (k ⊕ d) (k ⊕ d) ℂ := fromBlocks 1 T.toRows₁ 0 T.toRows₂ with hRm
  have hBR : B * Rm = fromCols Uc Ac := by
    rw [hBdef, hRm, fromCols_mul_fromBlocks, hT, ← fromRows_toRows T, fromCols_mul_fromRows]
    simp
  have e1 : (fromCols Uc Ac)ᴴ * B = fromBlocks (Ucᴴ * Uc) (Ucᴴ * Zc) 0 (Acᴴ * Zc) := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, hBdef, fromRows_mul_fromCols, hAU]
  have e2 : (fromCols Uc Ac)ᴴ * fromCols Uc Ac =
      fromBlocks (Ucᴴ * Uc) (Ucᴴ * Ac) 0 (Acᴴ * Ac) := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols, hAU]
  have f1 : (Ucᴴ * Uc).det * (Acᴴ * Zc).det = star Rm.det * (Bᴴ * B).det := by
    rw [← det_fromBlocks_zero₂₁ (Ucᴴ * Uc) (Ucᴴ * Zc) (Acᴴ * Zc), ← e1, ← hBR]
    have : (B * Rm)ᴴ * B = Rmᴴ * (Bᴴ * B) := by rw [conjTranspose_mul, Matrix.mul_assoc]
    rw [this, det_mul, det_conjTranspose]
  have f2 : (Ucᴴ * Uc).det * (Acᴴ * Ac).det = star Rm.det * (Bᴴ * B).det * Rm.det := by
    rw [← det_fromBlocks_zero₂₁ (Ucᴴ * Uc) (Ucᴴ * Ac) (Acᴴ * Ac), ← e2, ← hBR]
    have : (B * Rm)ᴴ * (B * Rm) = Rmᴴ * (Bᴴ * B) * Rm := by
      rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [this, det_mul, det_mul, det_conjTranspose]
  have hgs : star (Ucᴴ * Uc).det = (Ucᴴ * Uc).det := by
    rw [← det_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
  have hGs : star (Bᴴ * B).det = (Bᴴ * B).det := by
    rw [← det_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
  set g := (Ucᴴ * Uc).det
  set p := (Acᴴ * Zc).det
  set a := (Acᴴ * Ac).det
  set G := (Bᴴ * B).det
  set r := Rm.det
  have h3 : g * star p = r * G := by
    have := congrArg star f1
    rw [star_mul', star_mul', hgs, hGs, star_star] at this
    linear_combination this
  apply mul_left_cancel₀ hg
  linear_combination (g * star p) * f1 + (star r * G) * h3 - G * f2

end Mat

section NF

open NumberField Formalism.BasicNotions PI.Dv

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def cmat (A : HLat K) (φ : K →+* ℂ) {m : ℕ} (f : Fin m → A.V) : Matrix A.ι (Fin m) ℂ :=
  Matrix.of fun k i => φ (A.b.repr (f i) k)

def hmat (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) (φ : K →+* ℂ) : Matrix A.ι A.ι ℂ :=
  Matrix.of fun k l => φ (h (A.b k) (A.b l))

def rho (φ : K →+* ℂ) : K →+* ℂ := (starRingEnd ℂ).comp (φ.comp (starRingEnd K))

lemma rho_apply (φ : K →+* ℂ) (x : K) : rho φ x = star (φ (star x)) := rfl

def gmat (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) (φ : K →+* ℂ) {m : ℕ} (f : Fin m → A.V) :
    Matrix (Fin m) (Fin m) ℂ :=
  (cmat A φ f)ᴴ * hmat A h φ * cmat A φ f

lemma gramPl_eq (A : HLat K) (v : InfinitePlace K) {m : ℕ} (f : Fin m → A.V) :
    Formalism.HN.gramPl A.b A.X v f =
      ((A.X v)⁻¹ * cmat A v.embedding f)ᴴ * ((A.X v)⁻¹ * cmat A v.embedding f) := by
  ext a c
  simp [Formalism.HN.gramPl, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, cmat, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, conjTranspose_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

lemma frame_majAt (A : HLat K) (v : InfinitePlace K) :
    ((A.X v)⁻¹)ᴴ * (A.X v)⁻¹ =
      Matrix.of fun k l => Formalism.HermitianLatticesTheory.majAt A.b A.X v (A.b k) (A.b l) := by
  ext k l
  simp [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, conjTranspose_apply, Finsupp.single_apply, apply_ite]

lemma h_expand (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) (x y : A.V) :
    h x y = ∑ k, ∑ l, star (A.b.repr x k) * A.b.repr y l * h (A.b k) (A.b l) := by
  conv_lhs => rw [← A.b.sum_repr x, ← A.b.sum_repr y]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul,
    smul_eq_mul, starRingEnd_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring



variable (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)

section Hyp

variable (hC1 : ∀ i j, IsCM (h (A.b i) (A.b j)))
  (hC3 : ∀ (v : InfinitePlace K) i j,
    Formalism.HermitianLatticesTheory.majAt A.b A.X v (A.b i) (A.b j) = v.embedding (h (A.b i) (A.b j)))
include hC3

lemma frame_hmat (v : InfinitePlace K) : ((A.X v)⁻¹)ᴴ * (A.X v)⁻¹ = hmat A h v.embedding := by
  rw [frame_majAt]; ext k l; simp [hmat, hC3]


lemma gmat_place (v : InfinitePlace K) {m : ℕ} (f : Fin m → A.V) :
    gmat A h v.embedding f = Formalism.HN.gramPl A.b A.X v f := by
  rw [gramPl_eq, gmat, ← frame_hmat A h hC3, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

omit hC3 in
lemma gmat_conj (φ : K →+* ℂ) {m : ℕ} (f : Fin m → A.V) :
    gmat A h (ComplexEmbedding.conjugate φ) f = (gmat A h φ f).map (starRingEnd ℂ) := by
  ext i j
  simp [gmat, cmat, hmat, Matrix.mul_apply, conjTranspose_apply, map_sum]

omit hC3 in
lemma gramPl_psd (v : InfinitePlace K) {m : ℕ} (f : Fin m → A.V) :
    (Formalism.HN.gramPl A.b A.X v f).PosSemidef := by
  rw [gramPl_eq]; exact posSemidef_conjTranspose_mul_self _

lemma det_gmat (φ : K →+* ℂ) {m : ℕ} (f : Fin m → A.V) :
    (gmat A h φ f).det = (Formalism.HN.gramPl A.b A.X (InfinitePlace.mk φ) f).det := by
  have hreal := (psd_det_real (gramPl_psd A (InfinitePlace.mk φ) f)).1
  rcases InfinitePlace.embedding_mk_eq φ with h1 | h1
  · rw [← gmat_place A h hC3, h1]
  · have hφ : φ = ComplexEmbedding.conjugate (InfinitePlace.mk φ).embedding := by
      rw [h1]; ext x; simp
    conv_lhs => rw [hφ]
    rw [gmat_conj, ← RingHom.mapMatrix_apply, ← RingHom.map_det, gmat_place A h hC3, hreal]
    simp

omit hC3 in
include hC1 in
lemma hmat_rho (φ : K →+* ℂ) : hmat A h (rho φ) = hmat A h φ := by
  ext k l
  simp only [hmat, of_apply, rho_apply]
  rw [hC1 k l φ, star_star]

include hC1 in
lemma rhoGram_det (v : InfinitePlace K) {m : ℕ} (f : Fin m → A.V) :
    (((A.X v)⁻¹ * cmat A (rho v.embedding) f)ᴴ * ((A.X v)⁻¹ * cmat A (rho v.embedding) f)).det =
      (Formalism.HN.gramPl A.b A.X (InfinitePlace.mk (v.embedding.comp (starRingEnd K))) f).det := by
  have e1 : ((A.X v)⁻¹ * cmat A (rho v.embedding) f)ᴴ * ((A.X v)⁻¹ * cmat A (rho v.embedding) f) =
      gmat A h (rho v.embedding) f := by
    rw [gmat, hmat_rho A h hC1, ← frame_hmat A h hC3, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have e2 : rho v.embedding = ComplexEmbedding.conjugate (v.embedding.comp (starRingEnd K)) := by
    ext x
    simp only [rho_apply, ComplexEmbedding.conjugate_coe_eq, RingHom.coe_comp, Function.comp_apply,
      starRingEnd_apply]
  rw [e1, det_gmat A h hC3, e2, InfinitePlace.mk_conjugate_eq]

end Hyp

def piv (v : InfinitePlace K) : InfinitePlace K := InfinitePlace.mk (v.embedding.comp (starRingEnd K))






lemma log_abs_norm [IsTotallyComplex K] (x : K) (hx : x ≠ 0) :
    Real.log |((Algebra.norm ℚ x : ℚ) : ℝ)| = ∑ v : InfinitePlace K, 2 * Real.log ‖v.embedding x‖ := by
  have h := InfinitePlace.prod_eq_abs_norm x
  rw [← Rat.cast_abs, ← h, Real.log_prod]
  · refine Finset.sum_congr rfl fun v _ => ?_
    have hm : v.mult = 2 := InfinitePlace.mult_isComplex ⟨v, IsTotallyComplex.isComplex v⟩
    rw [Real.log_pow, InfinitePlace.norm_embedding_eq, hm]; push_cast; ring
  · intro v _
    exact pow_ne_zero _ (InfinitePlace.pos_iff.2 hx).ne'


end NF

end GramDeterminantPositive

open NumberField Formalism.BasicNotions PI.Dv GramDeterminantPositive Matrix



end PI.DvRows
