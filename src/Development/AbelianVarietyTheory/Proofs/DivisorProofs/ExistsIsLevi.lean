import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviTorus

open Matrix

variable {R : Type} [CommRing R] {n m : ℕ}

def torusMat (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (X Y : Fin n → R) (t : Rˣ) : Matrix (Fin n) (Fin n) R :=
  1 + ((t : R) - 1) • vecMulVec X (J *ᵥ fun i => c (Y i)) + (1 - c (↑t⁻¹ : R)) • vecMulVec Y (J *ᵥ fun i => c (X i))

section
variable (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (X Y : Fin n → R)

theorem conj_mulVec (hJ : ∀ i j, c (J j i) = -J i j) (V : Fin n → R) (hc : ∀ r, c (c r) = r) :
    (fun i => c ((J *ᵥ fun k => c (V k)) i)) = -(V ᵥ* J) := by
  funext i
  simp only [mulVec, vecMul, dotProduct, map_sum, map_mul, hc, Pi.neg_apply]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hJ k i]; ring

theorem conj_dot (a b : Fin n → R) : c (a ⬝ᵥ b) = (fun i => c (a i)) ⬝ᵥ (fun i => c (b i)) := by
  simp [dotProduct, map_sum, map_mul]

theorem vmv_mulVec (u v w : Fin n → R) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp [mulVec, dotProduct, vecMulVec, Finset.mul_sum, mul_comm, mul_left_comm]

end

section Props

variable {c : R →+* R} {J : Matrix (Fin n) (Fin n) R} {X Y : Fin n → R}
  (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = -J i j)
  (hXX : X ⬝ᵥ J *ᵥ (fun i => c (X i)) = 0) (hYY : Y ⬝ᵥ J *ᵥ (fun i => c (Y i)) = 0)
  (hXY : X ⬝ᵥ J *ᵥ (fun i => c (Y i)) = 1)
include hc hJ hXY

theorem dot_yx : Y ⬝ᵥ J *ᵥ (fun i => c (X i)) = -1 := by
  rw [dotProduct_mulVec]
  have h := conj_mulVec c J hJ Y hc
  rw [show Y ᵥ* J = -(fun i => c ((J *ᵥ fun k => c (Y k)) i)) by rw [h, neg_neg]]
  rw [neg_dotProduct, ← conj_dot, dotProduct_comm (J *ᵥ _) X, hXY, map_one]

omit hc hJ in
theorem torus_mulVec_x (t : Rˣ) (hXX : X ⬝ᵥ J *ᵥ (fun i => c (X i)) = 0) :
    torusMat c J X Y t *ᵥ X = (t : R) • X := by
  simp only [torusMat, add_mulVec, one_mulVec, smul_mulVec, vmv_mulVec]
  rw [dotProduct_comm (J *ᵥ _) X, dotProduct_comm (J *ᵥ _) X, hXY, hXX]
  module

theorem torus_mulVec_y (t : Rˣ) (hYY : Y ⬝ᵥ J *ᵥ (fun i => c (Y i)) = 0) :
    torusMat c J X Y t *ᵥ Y = c (↑t⁻¹ : R) • Y := by
  have hyx := dot_yx hc hJ hXY
  simp only [torusMat, add_mulVec, one_mulVec, smul_mulVec, vmv_mulVec]
  rw [dotProduct_comm (J *ᵥ _) Y, dotProduct_comm (J *ᵥ _) Y, hyx, hYY]
  module

theorem torus_mul_of (t : Rˣ) (A : Matrix (Fin n) (Fin m) R) (hu : (J *ᵥ fun i => c (Y i)) ᵥ* A = 0)
    (hw : (J *ᵥ fun i => c (X i)) ᵥ* A = 0) : torusMat c J X Y t * A = A := by
  have hz : ∀ v : Fin n → R, vecMulVec v (0 : Fin m → R) = 0 := fun v => by ext; simp [vecMulVec]
  simp only [torusMat, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, vecMulVec_mul, hu, hw, hz, smul_zero, add_zero]

theorem torus_mul_inv (t : Rˣ) (hXX : X ⬝ᵥ J *ᵥ (fun i => c (X i)) = 0)
    (hYY : Y ⬝ᵥ J *ᵥ (fun i => c (Y i)) = 0) : torusMat c J X Y t * torusMat c J X Y t⁻¹ = 1 := by
  have hyx := dot_yx hc hJ hXY
  have ht : (t : R) * (↑t⁻¹ : R) = 1 := Units.mul_inv t
  have hct : c (t : R) * c (↑t⁻¹ : R) = 1 := by rw [← map_mul, ht, map_one]
  simp only [torusMat, inv_inv, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, vecMulVec_mul_vecMulVec]
  rw [dotProduct_comm (J *ᵥ fun i => c (Y i)) X, dotProduct_comm (J *ᵥ fun i => c (Y i)) Y,
    dotProduct_comm (J *ᵥ fun i => c (X i)) X, dotProduct_comm (J *ᵥ fun i => c (X i)) Y, hXY, hYY, hXX, hyx]
  simp only [vecMulVec_smul, vecMulVec_neg, zero_smul, vecMulVec_zero, smul_zero, add_zero, zero_add, one_smul, neg_smul, smul_neg,
    smul_smul]
  match_scalars <;> first | linear_combination ht | linear_combination -hct | ring1

theorem torus_unitary (t : Rˣ) (hXX : X ⬝ᵥ J *ᵥ (fun i => c (X i)) = 0)
    (hYY : Y ⬝ᵥ J *ᵥ (fun i => c (Y i)) = 0) :
    (torusMat c J X Y t)ᵀ * J * (torusMat c J X Y t).map c = J := by
  have hyx := dot_yx hc hJ hXY
  have ht : (t : R) * (↑t⁻¹ : R) = 1 := Units.mul_inv t
  have hct : c (t : R) * c (↑t⁻¹ : R) = 1 := by rw [← map_mul, ht, map_one]
  have hu := conj_mulVec c J hJ Y hc
  have hw := conj_mulVec c J hJ X hc
  have hmap : (torusMat c J X Y t).map c = 1 + c ((t : R) - 1) • vecMulVec (fun i => c (X i)) (-(Y ᵥ* J)) +
      c (1 - c (↑t⁻¹ : R)) • vecMulVec (fun i => c (Y i)) (-(X ᵥ* J)) := by
    rw [← hu, ← hw]
    ext i j
    by_cases h : i = j <;> simp [torusMat, Matrix.map_apply, vecMulVec_apply, one_apply, h]
  have htr : (torusMat c J X Y t)ᵀ = 1 + ((t : R) - 1) • vecMulVec (J *ᵥ fun i => c (Y i)) X +
      (1 - c (↑t⁻¹ : R)) • vecMulVec (J *ᵥ fun i => c (X i)) Y := by
    simp [torusMat, transpose_add, transpose_smul, transpose_vecMulVec]
  have d1 : (X ᵥ* J) ⬝ᵥ (fun i => c (X i)) = 0 := by rw [← dotProduct_mulVec]; exact hXX
  have d2 : (X ᵥ* J) ⬝ᵥ (fun i => c (Y i)) = 1 := by rw [← dotProduct_mulVec]; exact hXY
  have d3 : (Y ᵥ* J) ⬝ᵥ (fun i => c (X i)) = -1 := by rw [← dotProduct_mulVec]; exact hyx
  have d4 : (Y ᵥ* J) ⬝ᵥ (fun i => c (Y i)) = 0 := by rw [← dotProduct_mulVec]; exact hYY
  rw [hmap, htr]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    vecMulVec_neg, Matrix.mul_neg, Matrix.neg_mul, smul_neg]
  simp only [vecMulVec_mul, mul_vecMulVec, vmv_mulVec, vecMul_vecMulVec, d1, d2, d3, d4, smul_vecMulVec, vecMulVec_smul,
    vecMulVec_neg, dotProduct_neg, dotProduct_smul, neg_dotProduct, smul_dotProduct]
  simp only [vecMulVec_smul, smul_vecMulVec, vecMulVec_neg, zero_smul, vecMulVec_zero, smul_zero, add_zero, zero_add, one_smul,
    neg_smul, smul_neg, smul_smul, neg_neg, map_sub, map_one, hc]
  match_scalars <;> first | linear_combination ht | linear_combination -ht | linear_combination hct |
    linear_combination -hct | ring1

end Props

end GlobalTheory.LeviTorus

namespace GlobalTheory.LeviTorus

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem cA_invol {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (a : AE F E) : cA σ (cA σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cA, h]
  | add a b ha hb => simp [map_add, ha, hb]

theorem cA_incl (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem form_incl (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    incV F x ⬝ᵥ incM F J *ᵥ (fun i => cA σ (incV F y i)) = inclR (F := F) (AF F) (form σ J x y) := by
  simp [form, incV, incM, cA_incl, dotProduct, mulVec, map_sum, map_mul]

theorem vecMul_incM (σ : E →ₐ[F] E) {n k : ℕ} (J : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) (Fin k) E) (y : Fin n → E) :
    (incM F J *ᵥ fun i => cA σ (incV F y i)) ᵥ* incM F A =
      fun j => inclR (F := F) (AF F) (form σ J (A *ᵥ Pi.single j 1) y) := by
  funext j
  rw [← form_incl]
  simp only [vecMul, dotProduct, incV, incM, Matrix.map_apply, mulVec_single_one]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]; rfl

end GlobalTheory.LeviTorus

theorem GlobalTheory.LeviTorus.exists_levi : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ t : (AE F E)ˣ, ∃ m : UA σ W.J, IsLevi (W₁ := W₁) H' t 1 m := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA _ t
  have hσ := GlobalTheory.LeviTorus.sigma_invol hP.base.cm
  have hc : ∀ a : AE F E, (cA σ).toRingHom ((cA σ).toRingHom a) = a := GlobalTheory.LeviTorus.cA_invol hσ
  have hJ : ∀ i j, (cA σ).toRingHom (incM F W.J j i) = -incM F W.J i j := by
    intro i j
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, incM, Matrix.map_apply, GlobalTheory.LeviTorus.cA_incl, hP.skew.skew i j, map_neg]
  have hXX : incV F H'.x ⬝ᵥ incM F W.J *ᵥ (fun i => (cA σ).toRingHom (incV F H'.x i)) = 0 := by
    rw [show (fun i => (cA σ).toRingHom (incV F H'.x i)) = fun i => cA σ (incV F H'.x i) from rfl,
      GlobalTheory.LeviTorus.form_incl, hA.xx, map_zero]
  have hYY : incV F H'.y ⬝ᵥ incM F W.J *ᵥ (fun i => (cA σ).toRingHom (incV F H'.y i)) = 0 := by
    rw [show (fun i => (cA σ).toRingHom (incV F H'.y i)) = fun i => cA σ (incV F H'.y i) from rfl,
      GlobalTheory.LeviTorus.form_incl, hA.yy, map_zero]
  have hXY : incV F H'.x ⬝ᵥ incM F W.J *ᵥ (fun i => (cA σ).toRingHom (incV F H'.y i)) = 1 := by
    rw [show (fun i => (cA σ).toRingHom (incV F H'.y i)) = fun i => cA σ (incV F H'.y i) from rfl,
      GlobalTheory.LeviTorus.form_incl, hA.xy, map_one]
  have h01 := GlobalTheory.LeviTorus.torus_mul_inv hc hJ hXY t hXX hYY
  have h10 : GlobalTheory.LeviTorus.torusMat (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) t⁻¹ *
      GlobalTheory.LeviTorus.torusMat (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) t = 1 :=
    by simpa only [inv_inv] using GlobalTheory.LeviTorus.torus_mul_inv hc hJ hXY t⁻¹ hXX hYY
  refine ⟨⟨⟨GlobalTheory.LeviTorus.torusMat (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) t, _, h01, h10⟩, ?_⟩, ?_, ?_, ?_⟩
  · exact GlobalTheory.LeviTorus.torus_unitary hc hJ hXY t hXX hYY
  · exact GlobalTheory.LeviTorus.torus_mulVec_x hXY t hXX
  · exact GlobalTheory.LeviTorus.torus_mulVec_y hc hJ hXY t hYY
  · have hu : (incM F W.J *ᵥ fun i => (cA σ).toRingHom (incV F H'.y i)) ᵥ* incM F H'.ι = 0 := by
      rw [show (fun i => (cA σ).toRingHom (incV F H'.y i)) = fun i => cA σ (incV F H'.y i) from rfl,
        GlobalTheory.LeviTorus.vecMul_incM]
      funext j
      rw [(hA.orth _).2, map_zero]; rfl
    have hw : (incM F W.J *ᵥ fun i => (cA σ).toRingHom (incV F H'.x i)) ᵥ* incM F H'.ι = 0 := by
      rw [show (fun i => (cA σ).toRingHom (incV F H'.x i)) = fun i => cA σ (incV F H'.x i) from rfl,
        GlobalTheory.LeviTorus.vecMul_incM]
      funext j
      rw [(hA.orth _).1, map_zero]; rfl
    show GlobalTheory.LeviTorus.torusMat (cA σ).toRingHom (incM F W.J) (incV F H'.x) (incV F H'.y) t * incM F H'.ι =
      incM F H'.ι * 1
    rw [Matrix.mul_one]
    exact GlobalTheory.LeviTorus.torus_mul_of hc hJ hXY t _ hu hw
end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.LeviUnitary

open Matrix

section Ring

variable {R : Type} [CommRing R] {n m : ℕ} {ι : Matrix (Fin n) (Fin m) R} {π : Matrix (Fin m) (Fin n) R}

theorem ext_mul (hπ : π * ι = 1) (g h : Matrix (Fin m) (Fin m) R) :
    (1 + ι * (g - 1) * π) * (1 + ι * (h - 1) * π) = 1 + ι * (g * h - 1) * π := by
  have h1 : ι * (g - 1) * π * (ι * (h - 1) * π) = ι * ((g - 1) * (h - 1)) * π := by
    calc _ = ι * (g - 1) * (π * ι) * (h - 1) * π := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hπ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have h2 : g * h - 1 = (h - 1) + (g - 1) + (g - 1) * (h - 1) := by noncomm_ring
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, h1, h2]
  simp only [Matrix.mul_add, Matrix.add_mul, add_assoc]

theorem ext_unitary (c : R →+* R) {J : Matrix (Fin n) (Fin n) R} {J₁ : Matrix (Fin m) (Fin m) R} (hπ : π * ι = 1)
    (h1 : J * ι.map c = πᵀ * J₁) (h2 : ιᵀ * J = J₁ * π.map c) {g : Matrix (Fin m) (Fin m) R} (hg : gᵀ * J₁ * g.map c = J₁) :
    (1 + ι * (g - 1) * π)ᵀ * J * (1 + ι * (g - 1) * π).map c = J := by
  have hm : (1 + ι * (g - 1) * π).map c = 1 + ι.map c * (g.map c - 1) * π.map c := by
    rw [Matrix.map_add _ (map_add c), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub c),
      Matrix.map_one _ (map_zero c) (map_one c), Matrix.map_one _ (map_zero c) (map_one c)]
  have h3 : π.map c * ι.map c = 1 := by rw [← Matrix.map_mul, hπ, Matrix.map_one _ (map_zero c) (map_one c)]
  have ht : (1 + ι * (g - 1) * π)ᵀ = 1 + πᵀ * (gᵀ - 1) * ιᵀ := by
    simp only [transpose_add, transpose_mul, transpose_sub, transpose_one, Matrix.mul_assoc]
  have e1 : πᵀ * (gᵀ - 1) * ιᵀ * J = πᵀ * ((gᵀ - 1) * J₁) * π.map c := by
    rw [Matrix.mul_assoc _ ιᵀ, h2]; simp only [Matrix.mul_assoc]
  have e2 : J * (ι.map c * (g.map c - 1) * π.map c) = πᵀ * (J₁ * (g.map c - 1)) * π.map c := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1]; simp only [Matrix.mul_assoc]
  have e3 : πᵀ * ((gᵀ - 1) * J₁) * π.map c * (ι.map c * (g.map c - 1) * π.map c) =
      πᵀ * ((gᵀ - 1) * J₁ * (g.map c - 1)) * π.map c := by
    calc _ = πᵀ * ((gᵀ - 1) * J₁) * (π.map c * ι.map c) * (g.map c - 1) * π.map c := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h3, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have e4 : (gᵀ - 1) * J₁ + (J₁ * (g.map c - 1) + (gᵀ - 1) * J₁ * (g.map c - 1)) = 0 := by
    have : (gᵀ - 1) * J₁ + (J₁ * (g.map c - 1) + (gᵀ - 1) * J₁ * (g.map c - 1)) = gᵀ * J₁ * g.map c - J₁ := by noncomm_ring
    rw [this, hg, sub_self]
  rw [hm, ht, Matrix.add_mul, Matrix.one_mul, e1, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, e2, e3, add_assoc,
    ← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.mul_add, e4]
  simp

end Ring

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨rfl, A, hA⟩ := h
  intro h0
  let A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply]
  have h2 := congrArg Matrix.det h1
  rw [det_mul, det_mul, h0, det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, det_neg, det_one] at h2
  simp at h2
  exact absurd h2.symm (by simp)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem incM_mul {k l p : ℕ} (A : Matrix (Fin k) (Fin l) E) (A' : Matrix (Fin l) (Fin p) E) :
    incM F (A * A') = incM F A * incM F A' := Matrix.map_mul

theorem incM_conj {k l : ℕ} (A : Matrix (Fin k) (Fin l) E) :
    (incM F A).map (cA σ).toRingHom = incM F (A.map σ) := by
  ext i j
  exact GlobalTheory.LeviTorus.cA_incl σ (A i j)

theorem incM_mulVec {k l : ℕ} (A : Matrix (Fin k) (Fin l) E) (x : Fin l → E) :
    incM F A *ᵥ incV F x = incV F (A *ᵥ x) := by
  funext i
  simp [incM, incV, mulVec, dotProduct, map_sum, map_mul]

theorem exists_proj {B : Base F E} (hB : B.IsGood σ) {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {r s r₁ s₁ : ℕ}
    (hW : W.IsSkew σ B r s) (hW₁ : W₁.IsSkew σ B r₁ s₁) {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hA : H'.IsAdapted σ B W W₁ i₀ i₁) :
    ∃ π : Matrix (Fin d₁) (Fin d) E, π * H'.ι = 1 ∧ W.J * H'.ι.map σ = πᵀ * W₁.J ∧ H'.ιᵀ * W.J = W₁.J * π.map σ ∧
      π *ᵥ H'.x = 0 ∧ π *ᵥ H'.y = 0 := by
  have hσ := GlobalTheory.LeviTorus.sigma_invol hB.cm
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdet : IsUnit W₁.J.det := by
    have h := det_ne_zero_of_hasSig (hW₁.sig w)
    rw [det_smul] at h
    have h' := right_ne_zero_of_mul h
    rw [isUnit_iff_ne_zero]
    intro h0
    apply h'
    have := RingHom.map_det (B.emb w).1 W₁.J
    rw [h0, map_zero] at this
    exact this.symm
  have mm : ∀ {k l : ℕ} (A : Matrix (Fin k) (Fin l) E), (A.map σ).map σ = A := fun A => by
    ext i j; exact hσ _
  have mul : ∀ {k l p : ℕ} (A : Matrix (Fin k) (Fin l) E) (A' : Matrix (Fin l) (Fin p) E),
      (A * A').map σ = A.map σ * A'.map σ := fun A A' => Matrix.map_mul (f := σ.toRingHom)
  have sk : W.J.map σ = -W.Jᵀ := by ext i j; exact hW.skew j i
  have sk₁ : W₁.J.map σ = -W₁.Jᵀ := by ext i j; exact hW₁.skew j i
  set P : Matrix (Fin d₁) (Fin d) E := W₁.J⁻¹ * (H'.ιᵀ * W.J) with hP
  have h2 : H'.ιᵀ * W.J = W₁.J * P := by rw [hP, Matrix.mul_nonsing_inv_cancel_left _ _ hdet]
  have hz : ∀ z : Fin d → E, (∀ u, form σ W.J (H'.ι *ᵥ u) z = 0) → P.map σ *ᵥ z = 0 := by
    intro z hz
    have e1 : (H'.ιᵀ * W.J) *ᵥ (fun i => σ (z i)) = 0 := by
      funext j
      have := hz (Pi.single j 1)
      rw [form, mulVec_single_one] at this
      rw [← mulVec_mulVec]
      exact this
    have e2 : P *ᵥ (fun i => σ (z i)) = 0 := by rw [hP, ← mulVec_mulVec, e1, mulVec_zero]
    funext j
    have := congrArg σ (congrFun e2 j)
    simpa [mulVec, dotProduct, map_sum, map_mul, hσ] using this
  refine ⟨P.map σ, ?_, ?_, by rw [mm, h2], hz _ fun u => (hA.orth u).1, hz _ fun u => (hA.orth u).2⟩
  · have : P * H'.ι.map σ = 1 := by rw [hP, Matrix.mul_assoc, hA.gram, Matrix.nonsing_inv_mul _ hdet]
    rw [← mm H'.ι, ← mul, this]
    exact Matrix.map_one _ (map_zero σ) (map_one σ)
  · have := congrArg (fun A => (Matrix.map A σ)ᵀ) h2
    simp only [mul, sk, sk₁, transpose_mul, transpose_neg, transpose_transpose, Matrix.neg_mul, Matrix.mul_neg,
      neg_inj] at this
    exact this

theorem exists_isLevi {B : Base F E} (hB : B.IsGood σ) {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {r s r₁ s₁ : ℕ}
    (hW : W.IsSkew σ B r s) (hW₁ : W₁.IsSkew σ B r₁ s₁) {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hA : H'.IsAdapted σ B W W₁ i₀ i₁)
    (h₁ : UA σ W₁.J) : ∃ m : UA σ W.J, IsLevi H' 1 h₁ m := by
  obtain ⟨π, p1, p2, p3, p4, p5⟩ := exists_proj hB hW hW₁ hA
  have q1 : incM F π * incM F H'.ι = 1 := by
    rw [← incM_mul, p1]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have q2 : incM F W.J * (incM F H'.ι).map (cA σ).toRingHom = (incM F π)ᵀ * incM F W₁.J := by
    rw [incM_conj, ← incM_mul, p2, incM_mul]; rfl
  have q3 : (incM F H'.ι)ᵀ * incM F W.J = incM F W₁.J * (incM F π).map (cA σ).toRingHom := by
    rw [incM_conj, ← incM_mul, ← p3, incM_mul]; rfl
  have hfix : ∀ z, π *ᵥ z = 0 → (1 + incM F H'.ι * (mat h₁ - 1) * incM F π) *ᵥ incV F z = incV F z := by
    intro z hz
    have h0 : incV F (0 : Fin d₁ → E) = 0 := by funext i; exact map_zero _
    rw [add_mulVec, one_mulVec, ← mulVec_mulVec, incM_mulVec, hz, h0, mulVec_zero, add_zero]
  refine ⟨⟨⟨1 + incM F H'.ι * (mat h₁ - 1) * incM F π, 1 + incM F H'.ι * ((h₁.1⁻¹).1 - 1) * incM F π, ?_, ?_⟩, ?_⟩,
    ?_, ?_, ?_⟩
  · rw [ext_mul q1, mat, Units.mul_inv]; simp
  · rw [ext_mul q1, mat, Units.inv_mul]; simp
  · exact ext_unitary (cA σ).toRingHom q1 q2 q3 h₁.2
  · rw [Units.val_one, one_smul]; exact hfix _ p4
  · rw [inv_one, Units.val_one, map_one, one_smul]; exact hfix _ p5
  · show (1 + incM F H'.ι * (mat h₁ - 1) * incM F π) * incM F H'.ι = _
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, q1, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]

end GlobalTheory.LeviUnitary

end
end
