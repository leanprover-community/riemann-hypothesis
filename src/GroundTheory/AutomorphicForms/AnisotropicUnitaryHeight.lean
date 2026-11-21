import Mathlib
import GroundTheory.AutomorphicForms.AnisotropicRestrict
import GroundTheory.AutomorphicForms.AdelicUnitaryGroups
import GroundTheory.AutomorphicForms.AnisotropicHeight

section
set_option maxSynthPendingDepth 1

open Module Matrix TensorProduct

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

noncomputable section

namespace Anisotropic

variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']

local notation "𝒩" => Fintype.card (ι × κ)

def resHom : Matrix ι ι (R ⊗[K] E) →ₐ[R] Matrix (Fin 𝒩) (Fin 𝒩) R :=
  (Matrix.reindexAlgEquiv R R (Fintype.equivFin (ι × κ))).toAlgHom.comp (blockHom b R)

theorem resHom_apply (M : Matrix ι ι (R ⊗[K] E)) (p q : Fin 𝒩) :
    resHom b R M p q = blockHom b R M ((Fintype.equivFin (ι × κ)).symm p) ((Fintype.equivFin (ι × κ)).symm q) := rfl

theorem resHom_injective : Function.Injective (resHom (ι := ι) b R) := by
  intro M M' h
  apply blockHom_injective b R
  ext p q
  have := congrFun (congrFun h (Fintype.equivFin (ι × κ) p)) (Fintype.equivFin (ι × κ) q)
  simpa [resHom_apply] using this

def resVec (x : ι → R ⊗[K] E) : Fin 𝒩 → R := coordsVec b R x ∘ (Fintype.equivFin (ι × κ)).symm

def ofResVec (y : Fin 𝒩 → R) : ι → R ⊗[K] E :=
  fun i => (coords b R).symm fun k => y (Fintype.equivFin (ι × κ) (i, k))

theorem resVec_ofResVec (y : Fin 𝒩 → R) : resVec b R (ofResVec b R y) = y := by
  funext p
  simp [resVec, ofResVec, coordsVec]

theorem ofResVec_resVec (x : ι → R ⊗[K] E) : ofResVec b R (resVec b R x) = x := by
  funext i
  simp [resVec, ofResVec, coordsVec]

theorem resVec_injective : Function.Injective (resVec (ι := ι) b R) :=
  Function.LeftInverse.injective (ofResVec_resVec b R)

theorem ofResVec_smul (t : R) (y : Fin 𝒩 → R) : ofResVec b R (t • y) = t • ofResVec b R y := by
  funext i
  simp only [ofResVec, Pi.smul_apply]
  rw [← map_smul]
  rfl

theorem resVec_vecMul (x : ι → R ⊗[K] E) (M : Matrix ι ι (R ⊗[K] E)) :
    resVec b R (x ᵥ* M) = resVec b R x ᵥ* resHom b R M := by
  funext q
  simp only [resVec, Function.comp_apply, coordsVec_vecMul, vecMul, dotProduct, resHom_apply]
  exact (Equiv.sum_comp (Fintype.equivFin (ι × κ)).symm
    (fun a => coordsVec b R x a * blockHom b R M a ((Fintype.equivFin (ι × κ)).symm q))).symm

variable {R}

theorem resHom_baseMap (f : R →ₐ[K] R') (M : Matrix ι ι (R ⊗[K] E)) :
    resHom b R' (M.map (baseMap f)) = (resHom b R M).map f := by
  ext p q
  simp only [resHom_apply, blockHom_baseMap, Matrix.map_apply]

theorem resVec_baseMap (f : R →ₐ[K] R') (x : ι → R ⊗[K] E) :
    resVec b R' (fun i => baseMap f (x i)) = f ∘ resVec b R x := by
  funext p
  simp only [resVec, Function.comp_apply, coordsVec_baseMap]

variable (R)

def trHom : GL ι (R ⊗[K] E) →* GL (Fin 𝒩) R where
  toFun g := ⟨resHom b R ((↑g⁻¹ : Matrix ι ι (R ⊗[K] E))ᵀ), resHom b R (((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E))ᵀ),
    by rw [← map_mul, ← transpose_mul, g.mul_inv, transpose_one, map_one],
    by rw [← map_mul, ← transpose_mul, g.inv_mul, transpose_one, map_one]⟩
  map_one' := by
    ext : 1
    simp
  map_mul' g h := by
    ext : 1
    simp [_root_.mul_inv_rev, transpose_mul, map_mul]

theorem trHom_val (g : GL ι (R ⊗[K] E)) :
    (trHom b R g : Matrix (Fin 𝒩) (Fin 𝒩) R) = resHom b R ((↑g⁻¹ : Matrix ι ι (R ⊗[K] E))ᵀ) := rfl

theorem resVec_vecMul_trHom (x : ι → R ⊗[K] E) (g : GL ι (R ⊗[K] E)) :
    resVec b R x ᵥ* (trHom b R g : Matrix (Fin 𝒩) (Fin 𝒩) R) =
      resVec b R ((↑g⁻¹ : Matrix ι ι (R ⊗[K] E)) *ᵥ x) := by
  rw [trHom_val, ← resVec_vecMul, vecMul_transpose]

def resScalar (j : κ) : Matrix (Fin 𝒩) (Fin 𝒩) K :=
  resHom (ι := ι) b K (Matrix.scalar ι (baseBasis b K j))

variable {R}

theorem resScalar_map (f : K →ₐ[K] R) (j : κ) :
    (resScalar (ι := ι) b j).map f = resHom b R (Matrix.scalar ι (baseBasis b R j)) := by
  rw [resScalar, ← resHom_baseMap, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _),
    baseMap_baseBasis, Matrix.scalar_apply]

variable (R)

theorem resHom_commute_scalar (M : Matrix ι ι (R ⊗[K] E)) (s : R ⊗[K] E) :
    resHom b R M * resHom b R (Matrix.scalar ι s) = resHom b R (Matrix.scalar ι s) * resHom b R M := by
  rw [← map_mul, ← map_mul, (Matrix.scalar_commute s (fun _ => mul_comm _ _) M).eq]

theorem exists_resHom_eq_of_commute (γ : GL (Fin 𝒩) K)
    (hγ : ∀ j, (γ : Matrix (Fin 𝒩) (Fin 𝒩) K) * resScalar (ι := ι) b j =
      resScalar (ι := ι) b j * γ) :
    ∃ M : GL ι (K ⊗[K] E), resHom b K (M : Matrix ι ι (K ⊗[K] E)) = γ := by
  have key : ∀ g : Matrix (Fin 𝒩) (Fin 𝒩) K, (∀ j, g * resScalar (ι := ι) b j =
      resScalar (ι := ι) b j * g) → ∃ M, resHom b K M = g := by
    intro g hg
    obtain ⟨M, hM⟩ := exists_blockHom_eq b K ((Matrix.reindexAlgEquiv K K (Fintype.equivFin (ι × κ))).symm g) fun j => by
      have h := congrArg (Matrix.reindexAlgEquiv K K (Fintype.equivFin (ι × κ))).symm (hg j)
      rw [map_mul, map_mul] at h
      have e : (Matrix.reindexAlgEquiv K K (Fintype.equivFin (ι × κ))).symm (resScalar (ι := ι) b j) =
          blockHom b K (Matrix.scalar ι (baseBasis b K j)) := by
        show (Matrix.reindexAlgEquiv K K (Fintype.equivFin (ι × κ))).symm
          (Matrix.reindexAlgEquiv K K (Fintype.equivFin (ι × κ))
            (blockHom b K (Matrix.scalar ι (baseBasis b K j)))) = _
        exact AlgEquiv.symm_apply_apply _ _
      rw [e] at h
      exact h.symm
    refine ⟨M, ?_⟩
    show Matrix.reindexAlgEquiv K K (Fintype.equivFin (ι × κ)) (blockHom b K M) = g
    rw [hM]
    exact AlgEquiv.apply_symm_apply _ _
  obtain ⟨M₀, h₀⟩ := key γ hγ
  obtain ⟨M₁, h₁⟩ := key (↑γ⁻¹ : Matrix (Fin 𝒩) (Fin 𝒩) K) fun j => by
    calc (↑γ⁻¹ : Matrix (Fin 𝒩) (Fin 𝒩) K) * resScalar (ι := ι) b j
        = ↑γ⁻¹ * (resScalar (ι := ι) b j * ↑γ) * ↑γ⁻¹ := by simp [mul_assoc]
      _ = ↑γ⁻¹ * (↑γ * resScalar (ι := ι) b j) * ↑γ⁻¹ := by rw [hγ]
      _ = resScalar (ι := ι) b j * ↑γ⁻¹ := by simp
  have e1 : M₀ * M₁ = 1 := resHom_injective b K (by rw [map_mul, map_one, h₀, h₁, γ.mul_inv])
  have e2 : M₁ * M₀ = 1 := resHom_injective b K (by rw [map_mul, map_one, h₀, h₁, γ.inv_mul])
  exact ⟨⟨M₀, M₁, e1, e2⟩, h₀⟩

theorem det_resHom (M : Matrix ι ι (R ⊗[K] E)) :
    (resHom b R M).det = (rmat b R M.det).det := by
  show (Matrix.reindex (Fintype.equivFin (ι × κ)) (Fintype.equivFin (ι × κ)) (blockHom b R M)).det = _
  rw [Matrix.det_reindex_self]
  exact (Matrix.det_det M (rmatHom b R).toRingHom).symm

def conjMat : Matrix κ κ R := fun k => coords b R (conjBase K E R (baseBasis b R k))

theorem coords_conjBase (z : R ⊗[K] E) :
    coords b R (conjBase K E R z) = coords b R z ᵥ* conjMat b R := by
  conv_lhs => rw [eq_sum_coords b R z]
  rw [map_sum, map_sum]
  funext l
  simp only [conjBase_smul, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecMul,
    dotProduct, conjMat]

theorem conjBase_conjBase (z : R ⊗[K] E) : conjBase K E R (conjBase K E R z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rw [conjBase_tmul, conjBase_tmul, conj_conj]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem conjMat_mul_self : conjMat b R * conjMat b R = 1 := by
  ext k l
  have h := congrFun (coords_conjBase b R (conjBase K E R (baseBasis b R k))) l
  rw [conjBase_conjBase, coords_baseBasis] at h
  have h' : (conjMat b R * conjMat b R) k l = (conjMat b R k ᵥ* conjMat b R) l := by
    simp [Matrix.mul_apply, vecMul, dotProduct]
  rw [h', conjMat, ← h, Pi.single_apply, Matrix.one_apply]
  exact if_congr eq_comm rfl rfl

theorem det_rmat_conjBase (z : R ⊗[K] E) :
    (rmat b R (conjBase K E R z)).det = (rmat b R z).det := by
  have hT : IsUnit (conjMat b R).det := by
    refine isUnit_iff_exists_inv.2 ⟨(conjMat b R).det, ?_⟩
    rw [← det_mul, conjMat_mul_self, det_one]
  have hrow : rmat b R z * conjMat b R = conjMat b R * rmat b R (conjBase K E R z) := by
    ext k l
    have h : rmat b R z k ᵥ* conjMat b R = conjMat b R k ᵥ* rmat b R (conjBase K E R z) := by
      simp only [rmat, conjMat]
      rw [← coords_conjBase, map_mul, coords_mul]
    have := congrFun h l
    simpa [Matrix.mul_apply, vecMul, dotProduct] using this
  have h := congrArg Matrix.det hrow
  rw [det_mul, det_mul, mul_comm] at h
  exact (hT.mul_left_cancel h).symm

theorem conjBase_det_mul_det (H : Matrix ι ι E) (hH : IsUnit H.det) (g : unitaryPoints K E H R) :
    conjBase K E R ((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)).det * ((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)).det = 1 := by
  have hg : (((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)).map (conjBase K E R))ᵀ * baseMatrix K H R *
      ((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)) = baseMatrix K H R := g.2
  have h := congrArg Matrix.det hg
  have hd : (((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)).map (conjBase K E R)).det =
      conjBase K E R ((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)).det :=
    (RingHom.map_det (conjBase K E R) _).symm
  rw [det_mul, det_mul, det_transpose, hd] at h
  have hu : IsUnit (baseMatrix K H R).det := isUnit_det_baseMatrix H R hH
  have : conjBase K E R ((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)).det * ((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)).det *
      (baseMatrix K H R).det = 1 * (baseMatrix K H R).det := by
    linear_combination h
  exact hu.mul_right_cancel this

theorem det_trHom_mul_self (H : Matrix ι ι E) (hH : IsUnit H.det) (g : unitaryPoints K E H R) :
    (trHom b R (g : GL ι (R ⊗[K] E)) : Matrix (Fin 𝒩) (Fin 𝒩) R).det *
      (trHom b R (g : GL ι (R ⊗[K] E)) : Matrix (Fin 𝒩) (Fin 𝒩) R).det = 1 := by
  rw [trHom_val, det_resHom, det_transpose]
  have h := conjBase_det_mul_det R H hH g⁻¹
  have e : (((g⁻¹ : unitaryPoints K E H R) : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)) =
      (↑(g : GL ι (R ⊗[K] E))⁻¹ : Matrix ι ι (R ⊗[K] E)) := rfl
  rw [e] at h
  conv_lhs => arg 1; rw [← det_rmat_conjBase b R]
  rw [← det_mul, ← rmat_mul, h, rmat_one, det_one]

end Anisotropic

end

end GroundTheory.Automorphic
end

section
set_option maxSynthPendingDepth 1

open Module Matrix TensorProduct NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

noncomputable section

namespace Anisotropic

variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ K E)

local notation "𝒩" => Fintype.card (ι × κ)

section Algebraic

variable (R : Type*) [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']

theorem baseMap_eq_tensorMap (f : R →ₐ[K] R') :
    (baseMap f : R ⊗[K] E →ₐ[K] R' ⊗[K] E) = tensorMap E f := rfl

variable {R}

theorem hermValue_baseMap (f : R →ₐ[K] R') (x : ι → R ⊗[K] E) :
    baseMap f (hermValue K H R x) = hermValue K H R' (fun i => baseMap f (x i)) := by
  rw [baseMap_eq_tensorMap]
  unfold hermValue
  change (tensorMap E f : R ⊗[K] E →+* R' ⊗[K] E) (_ ⬝ᵥ _) = _
  rw [RingHom.map_dotProduct]
  congr 1
  · funext i
    simp [tensorMap_conjBase]
  · funext i
    rw [Function.comp_apply, RingHom.map_mulVec]
    congr 1
    ext a c
    simp [baseMatrix]

variable (R)

def hermCoords (y : Fin 𝒩 → R) : κ → R := coords b R (hermValue K H R (ofResVec b R y))

theorem hermCoords_smul (t : R) (y : Fin 𝒩 → R) :
    hermCoords H b R (t • y) = t ^ 2 • hermCoords H b R y := by
  rw [hermCoords, ofResVec_smul, hermValue_smul, map_smul, sq]
  rfl

variable {R}

theorem ofResVec_comp (f : R →ₐ[K] R') (y : Fin 𝒩 → R) :
    ofResVec b R' (f ∘ y) = fun i => baseMap f (ofResVec b R y i) := by
  apply resVec_injective b R'
  rw [resVec_ofResVec, resVec_baseMap, resVec_ofResVec]

theorem hermCoords_comp (f : R →ₐ[K] R') (y : Fin 𝒩 → R) :
    hermCoords H b R' (f ∘ y) = f ∘ hermCoords H b R y := by
  rw [hermCoords, ofResVec_comp, ← hermValue_baseMap, coords_baseMap]
  rfl

def hermPoly (k : κ) : MvPolynomial (Fin 𝒩) K :=
  hermCoords H b (MvPolynomial (Fin 𝒩) K) MvPolynomial.X k

theorem aeval_hermPoly (y : Fin 𝒩 → R) (k : κ) :
    MvPolynomial.aeval y (hermPoly H b k) = hermCoords H b R y k := by
  have h := congrFun (hermCoords_comp H b (MvPolynomial.aeval y) MvPolynomial.X) k
  have hy : (MvPolynomial.aeval y : MvPolynomial (Fin 𝒩) K →ₐ[K] R) ∘ MvPolynomial.X = y := by
    funext p
    simp
  rw [hy] at h
  exact h.symm

def inside₂ (S : Type*) [CommRing S] : GL ι S →* GL ι S where
  toFun g := ⟨(↑g⁻¹ : Matrix ι ι S)ᵀ, (g : Matrix ι ι S)ᵀ,
    by rw [← transpose_mul, g.mul_inv, transpose_one],
    by rw [← transpose_mul, g.inv_mul, transpose_one]⟩
  map_one' := by
    ext : 1
    simp
  map_mul' g h := by
    ext : 1
    simp [_root_.mul_inv_rev, transpose_mul]

theorem trHom_invTr (g : GL ι (R ⊗[K] E)) :
    (trHom b R (inside₂ (R ⊗[K] E) g) : Matrix (Fin 𝒩) (Fin 𝒩) R) = resHom b R ↑g := by
  rw [trHom_val]
  congr 1

def diagGL (f : R →ₐ[K] R') : GL ι (R ⊗[K] E) →* GL ι (R' ⊗[K] E) :=
  Units.map ((AlgHom.mapMatrix (baseMap f) : Matrix ι ι (R ⊗[K] E) →ₐ[K] Matrix ι ι (R' ⊗[K] E)).toRingHom.toMonoidHom)

theorem diagGL_val (f : R →ₐ[K] R') (g : GL ι (R ⊗[K] E)) :
    (diagGL f g : Matrix ι ι (R' ⊗[K] E)) = (g : Matrix ι ι (R ⊗[K] E)).map (baseMap f) := rfl

theorem invTr_diagGL (f : R →ₐ[K] R') (g : GL ι (R ⊗[K] E)) :
    inside₂ (R' ⊗[K] E) (diagGL f g) = diagGL f (inside₂ (R ⊗[K] E) g) := by
  ext : 1
  simp only [diagGL_val]
  show ((↑(diagGL f g)⁻¹ : Matrix ι ι (R' ⊗[K] E)))ᵀ = ((↑g⁻¹ : Matrix ι ι (R ⊗[K] E))ᵀ).map _
  rw [← map_inv, diagGL_val, transpose_map]

end Algebraic

section Heights

variable [NumberField K] {d : ℕ} (b : Basis (Fin d) K E)

local notation "𝒩'" => Fintype.card (ι × Fin d)

theorem hermCoords_vecMul_trHom (x : Fin 𝒩' → K) (u : unitaryPoints K E H 𝔸[K]) :
    hermCoords H b 𝔸[K] (Reduction.ratVec x ᵥ* (trHom b 𝔸[K] (u : GL ι (𝔸[K] ⊗[K] E)) :
      Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K])) = Reduction.ratVec (hermCoords H b K x) := by
  have hx : Reduction.ratVec x = resVec b 𝔸[K]
      (fun i => baseMap (Algebra.ofId K 𝔸[K]) (ofResVec b K x i)) := by
    rw [resVec_baseMap, resVec_ofResVec]
    rfl
  rw [hx, resVec_vecMul_trHom, hermCoords, ofResVec_resVec]
  have h := hermValue_mulVec (K := K) (H := H) (u⁻¹)
    (fun i => baseMap (Algebra.ofId K 𝔸[K]) (ofResVec b K x i))
  rw [show unitaryMat (u⁻¹) = (↑(u : GL ι (𝔸[K] ⊗[K] E))⁻¹ : Matrix ι ι (𝔸[K] ⊗[K] E)) from rfl]
    at h
  rw [h, ← hermValue_baseMap, coords_baseMap]
  rfl

theorem exists_pos_le_height_trHom
    (haniso : ∀ ξ : ι → K ⊗[K] E, hermValue K H K ξ = 0 → ξ = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : unitaryPoints K E H 𝔸[K], ∀ x : Fin 𝒩' → K, x ≠ 0 →
      ε ≤ Reduction.height (trHom b 𝔸[K] (u : GL ι (𝔸[K] ⊗[K] E))) x := by
  obtain ⟨C, hC, hCb⟩ := exists_adelicNorm_aeval_le (K := K) (d := 2) two_pos (hermPoly H b)
    (fun v t y k => by
      rw [aeval_hermPoly, aeval_hermPoly, hermCoords_smul]
      rfl)
    (fun w t y k => by
      rw [aeval_hermPoly, aeval_hermPoly, hermCoords_smul]
      rfl)
  have hG : ∀ g ∈ Set.range fun u : unitaryPoints K E H 𝔸[K] =>
      trHom b 𝔸[K] (u : GL ι (𝔸[K] ⊗[K] E)), ∀ x : Fin 𝒩' → K, x ≠ 0 →
      ∃ s : GroundTheory.Global.IdeleGroup K, 1 ≤ (GroundTheory.Global.IdeleGroup.ideleModule K s : ℝ) ∧
        ∃ z : Fin d → K, z ≠ 0 ∧ (fun y k => MvPolynomial.aeval y (hermPoly H b k))
          (Reduction.ratVec x ᵥ* (g : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K])) =
            (s : 𝔸[K]) • Reduction.ratVec z := by
    rintro _ ⟨u, rfl⟩ x hx
    refine ⟨1, by simp, hermCoords H b K x, ?_, ?_⟩
    · intro h0
      apply hx
      have h1 : hermValue K H K (ofResVec b K x) = 0 := by
        apply (coords b K).injective
        rw [map_zero]
        exact h0
      have h2 := haniso _ h1
      rw [← resVec_ofResVec b K x, h2]
      funext p
      simp [resVec, coordsVec]
    · funext k
      simp only [aeval_hermPoly, Units.val_one, one_smul]
      rw [hermCoords_vecMul_trHom]
  obtain ⟨ε, hε, h⟩ := exists_pos_le_height_of_bound
    (Set.range fun u : unitaryPoints K E H 𝔸[K] => trHom b 𝔸[K] (u : GL ι (𝔸[K] ⊗[K] E)))
    (fun y k => MvPolynomial.aeval y (hermPoly H b k)) hC two_pos hCb hG
  exact ⟨ε, hε, fun u x hx => h _ ⟨u, rfl⟩ x hx⟩

theorem exists_isCompact_trHom (hH : IsUnit H.det)
    (haniso : ∀ ξ : ι → K ⊗[K] E, hermValue K H K ξ = 0 → ξ = 0) :
    ∃ C : Set (GL (Fin 𝒩') 𝔸[K]), IsCompact C ∧ ∀ u : unitaryPoints K E H 𝔸[K],
      ∃ M : GL ι (K ⊗[K] E), trHom b 𝔸[K]
        ((diagGL (Algebra.ofId K 𝔸[K]) M)⁻¹ * (u : GL ι (𝔸[K] ⊗[K] E))) ∈ C := by
  classical
  obtain ⟨ε, hε, hh⟩ := exists_pos_le_height_trHom H b haniso
  let G : Subgroup (AdelicGLn.AdelicGL K 𝒩') :=
    ((trHom b 𝔸[K]).comp (unitaryPoints K E H 𝔸[K]).subtype).range
  have hG1 : G ≤ Reduction.normOneGL K 𝒩' := by
    rintro _ ⟨u, rfl⟩
    rw [Reduction.mem_normOneGL]
    set a := AdelicGLn.det K 𝒩' ((trHom b 𝔸[K]).comp (unitaryPoints K E H 𝔸[K]).subtype u)
    have ha : a * a = 1 := by
      ext
      simpa [a] using det_trHom_mul_self b 𝔸[K] H hH u
    have h2 : (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) *
        (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) = 1 := by
      have h3 := congrArg (GroundTheory.Global.IdeleGroup.ideleModule K) ha
      rw [map_mul, map_one] at h3
      simpa using congrArg Subtype.val h3
    have hpos := (GroundTheory.Global.IdeleGroup.ideleModule K a).2
    nlinarith
  have hGL : G ≤ adelicCentralizer (resScalar (ι := ι) b) := by
    rintro _ ⟨u, rfl⟩ j
    have e := resScalar_map (ι := ι) b (Algebra.ofId K 𝔸[K]) j
    change _ * (resScalar (ι := ι) b j).map (Algebra.ofId K 𝔸[K]) =
      (resScalar (ι := ι) b j).map (Algebra.ofId K 𝔸[K]) * _
    rw [e]
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [trHom_val]
    exact resHom_commute_scalar b 𝔸[K] _ _
  obtain ⟨C, hC, hred⟩ := exists_isCompact_centralizer_reduction (resScalar (ι := ι) b) G hG1 hGL hε
    (by rintro _ ⟨u, rfl⟩ x hx; exact hh u x hx)
  refine ⟨C, hC, fun u => ?_⟩
  obtain ⟨γ, hγ, hγC⟩ := hred _ ⟨u, rfl⟩
  obtain ⟨M, hM⟩ := exists_resHom_eq_of_commute b γ hγ
  refine ⟨inside₂ (K ⊗[K] E) M, ?_⟩
  have e : trHom b 𝔸[K] (diagGL (Algebra.ofId K 𝔸[K]) (inside₂ (K ⊗[K] E) M)) =
      AdelicGLn.diagonal K 𝒩' γ := by
    ext : 1
    rw [← invTr_diagGL, trHom_invTr, diagGL_val, resHom_baseMap, hM]
    rfl
  rw [map_mul, map_inv, e]
  exact hγC

end Heights

end Anisotropic

end

end GroundTheory.Automorphic
end
