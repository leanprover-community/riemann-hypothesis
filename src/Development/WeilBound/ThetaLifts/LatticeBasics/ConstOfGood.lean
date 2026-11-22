module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.DeterminantProjection
public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable
public import Development.WeilBound.ThetaLifts.LatticeBasics.ConstIdele

@[expose] public section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.IndefR.DeterminantProjection

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem det_ne_zero_of_sig {M : Matrix (Fin n) (Fin n) ℂ} {r s : ℕ} (h : HasSig M r s) : M.det ≠ 0 := fun z => by
  obtain ⟨e, A, hA⟩ := h
  let q : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr e)
  have := congrArg Matrix.det (show (Aᵀ.submatrix id q * M.submatrix q q) * (A.map star).submatrix q id = Matrix.fromBlocks 1 0 0 (-1) by
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]; exact hA)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self, z, mul_zero, zero_mul, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) this.symm

omit [NumberField E] in
theorem hermND_transpose {B : Base F E} {X : Spc F E n} {r s : ℕ} (h : X.IsHerm σ B r s) : IsHermND σ X.Jᵀ := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  refine ⟨fun i j => h.herm j i, fun z => det_ne_zero_of_sig (h.sig w) ?_⟩
  rw [Matrix.det_transpose] at z
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, z, map_zero]

def sec {A : Type} [CommRing A] (R : Matrix (Fin n) (Fin n) A) (h : R * R = R) : A →* Matrix (Fin n) (Fin n) A where
  toFun z := 1 + (z - 1) • R
  map_one' := by simp
  map_mul' a b := by
    simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, h, smul_smul, add_assoc, ← add_smul]
    congr 2
    ring

omit [NumberField E] in
theorem conj_mem_UAt {X : Spc F E n} {R : Type} [Zero R] {ev : AF F → R} {u : UA σ X.J} (hu : u ∈ UAt σ X ev) (g : UA σ X.J) :
    g⁻¹ * u * g ∈ UAt σ X ev := fun t ht => by
  have : mat (g⁻¹ * u * g) - 1 = mat g⁻¹ * (mat u - 1) * mat g := by
    rw [mul_sub, sub_mul, mul_one]
    exact congrArg₂ (· - ·) rfl (Units.inv_mul g.1).symm
  rw [this, ← smul_mul_assoc, ← mul_smul_comm, hu t ht, mul_zero, zero_mul]

end GlobalTheory.ThK.Dbl

end
