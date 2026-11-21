import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalProductMultiplicity

section
noncomputable section

namespace GlobalTheory.HcIrr

open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

def natBlocks (b : Fin r → Fin s) : Fin r → ℕ := fun i => (b i : ℕ)

theorem blockTri_le_parab (b : Fin r → Fin s) : blockTri (κ := K) (natBlocks b) ≤ parab K b := by
  intro p hp
  refine ⟨fun i j hij => hp hij, fun i j hij => ?_⟩
  exact (inv_mem hp : p⁻¹ ∈ blockTri (κ := K) (natBlocks b)) hij

theorem parab_le_blockTri (b : Fin r → Fin s) : parab K b ≤ blockTri (κ := K) (natBlocks b) := by
  intro p hp i j hij
  exact hp.1 i j hij

theorem levi_one (b : Fin r → Fin s) (c : Fin s) : levi K b c 1 = 1 := by
  apply Units.ext
  exact Matrix.submatrix_one _ Subtype.val_injective

theorem levi_mul (b : Fin r → Fin s) (c : Fin s) (p q : parab K b) :
    levi K b c (p * q) = levi K b c p * levi K b c q := by
  apply Units.ext
  exact blk_mul b c p.2.1 q.2.1

variable (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))

def leviTensor : Representation ℂ (blockTri (κ := K) (natBlocks b))
    (PiTensorProduct ℂ (fun c => (lam c : Type))) where
  toFun p := infl K b lam (Subgroup.inclusion (blockTri_le_parab b) p)
  map_one' := by
    have : ∀ c, (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) 1)) = LinearMap.id := by
      intro c
      rw [map_one, levi_one, map_one]
      rfl
    simp only [infl, this]
    exact PiTensorProduct.map_id
  map_mul' p q := by
    have : ∀ c, (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) (p * q))) =
        (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) p)) ∘ₗ
          (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) q)) := by
      intro c
      rw [map_mul, levi_mul, map_mul]
      rfl
    simp only [infl, this]
    exact PiTensorProduct.map_comp _ _

theorem leviTensor_apply (p : blockTri (κ := K) (natBlocks b)) :
    leviTensor b lam p = PiTensorProduct.map (fun c =>
      (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) p))) := rfl

instance finiteTensor : FiniteDimensional ℂ (PiTensorProduct ℂ (fun c => (lam c : Type))) :=
  Module.Finite.of_basis (Basis.piTensorProduct fun c => Module.finBasis ℂ (lam c : Type))

end GlobalTheory.HcIrr
end
end

section
noncomputable section

namespace GlobalTheory.HcIrr

open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

def extMat (b : Fin r → Fin s) (c : Fin s) :
    Matrix {i // b i = c} {i // b i = c} K →* Matrix (Fin r) (Fin r) K where
  toFun g := Matrix.reindex (Equiv.sumCompl fun a => b a = c) (Equiv.sumCompl fun a => b a = c)
    (Matrix.fromBlocks g 0 0 1)
  map_one' := by simp
  map_mul' x y := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

theorem extMat_in (b : Fin r → Fin s) (c : Fin s) (g : Matrix {i // b i = c} {i // b i = c} K)
    (i j : {i // b i = c}) : extMat b c g i.1 j.1 = g i j := by
  simp [extMat, Equiv.sumCompl_symm_apply_of_pos (p := fun a => b a = c) i.2,
    Equiv.sumCompl_symm_apply_of_pos (p := fun a => b a = c) j.2]

theorem extMat_out (b : Fin r → Fin s) (c : Fin s) (g : Matrix {i // b i = c} {i // b i = c} K) (i j : Fin r)
    (h : ¬ (b i = c ∧ b j = c)) : extMat b c g i j = (1 : Matrix (Fin r) (Fin r) K) i j := by
  by_cases hi : b i = c <;> by_cases hj : b j = c
  · exact absurd ⟨hi, hj⟩ h
  · have : i ≠ j := fun e => hj (e ▸ hi)
    simp [extMat, Equiv.sumCompl_symm_apply_of_pos (p := fun a => b a = c) hi,
      Equiv.sumCompl_symm_apply_of_neg (p := fun a => b a = c) hj, this]
  · have : i ≠ j := fun e => hi (e ▸ hj)
    simp [extMat, Equiv.sumCompl_symm_apply_of_neg (p := fun a => b a = c) hi,
      Equiv.sumCompl_symm_apply_of_pos (p := fun a => b a = c) hj, this]
  · simp [extMat, Equiv.sumCompl_symm_apply_of_neg (p := fun a => b a = c) hi,
      Equiv.sumCompl_symm_apply_of_neg (p := fun a => b a = c) hj, Matrix.one_apply]

def blockExt (b : Fin r → Fin s) (c : Fin s) :
    GL {i // b i = c} K →* blockTri (κ := K) (natBlocks b) :=
  (Units.map (extMat b c)).codRestrict (blockTri (κ := K) (natBlocks b)) fun g => by
    refine mem_blockTri.2 fun i j hij => ?_
    show extMat b c _ i j = 0
    have hne : b i ≠ b j := fun e => by
      simp only [natBlocks, e] at hij
      exact lt_irrefl _ hij
    rw [extMat_out b c _ i j (fun e => hne (e.1.trans e.2.symm)),
      Matrix.one_apply_ne (fun e => hne (congrArg b e))]

theorem blockExt_in (b : Fin r → Fin s) (c : Fin s) (g : GL {i // b i = c} K) (i j : {i // b i = c}) :
    (((blockExt b c g : blockTri (κ := K) (natBlocks b)) : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i.1 j.1 =
      (g : Matrix _ _ K) i j :=
  extMat_in b c _ i j

theorem blockExt_out (b : Fin r → Fin s) (c : Fin s) (g : GL {i // b i = c} K) (i j : Fin r)
    (h : ¬ (b i = c ∧ b j = c)) :
    (((blockExt b c g : blockTri (κ := K) (natBlocks b)) : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j =
      (1 : Matrix (Fin r) (Fin r) K) i j :=
  extMat_out b c _ i j h

theorem levi_blockExt_same (b : Fin r → Fin s) (c : Fin s) (g : GL {i // b i = c} K) :
    levi K b c (Subgroup.inclusion (blockTri_le_parab b) (blockExt b c g)) = g := by
  apply Units.ext
  ext x y
  exact blockExt_in b c g x y

theorem levi_blockExt_ne (b : Fin r → Fin s) {c c' : Fin s} (h : c' ≠ c) (g : GL {i // b i = c} K) :
    levi K b c' (Subgroup.inclusion (blockTri_le_parab b) (blockExt b c g)) = 1 := by
  apply Units.ext
  ext x y
  have := blockExt_out b c g x.1 y.1 (fun e => h (x.2.symm.trans e.1))
  show (((blockExt b c g : blockTri (κ := K) (natBlocks b)) : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) x.1 y.1 =
    (1 : Matrix _ _ K) x y
  rw [this]
  simp [Matrix.one_apply, Subtype.ext_iff]

variable (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))

theorem leviTensor_blockExt (c : Fin s) (g : GL {i // b i = c} K) :
    leviTensor b lam (blockExt b c g) = PiTensorProduct.map
      (Function.update (fun c' => (LinearMap.id : (lam c' : Type) →ₗ[ℂ] (lam c' : Type))) c ((lam c).ρ g)) := by
  rw [leviTensor_apply]
  congr 1
  funext c'
  by_cases h : c' = c
  · subst h
    rw [levi_blockExt_same, Function.update_self]
  · rw [levi_blockExt_ne b h, Function.update_of_ne h, map_one]
    rfl

end GlobalTheory.HcIrr
end
end
