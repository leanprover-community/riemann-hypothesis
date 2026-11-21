import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS


abbrev EH (n : ℕ) := EuclideanSpace ℂ (Fin n)

def rsM {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (⊤ : Submodule ℂ (EH n)) :=
  ((toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A : EH n →L[ℂ] EH n) : EH n →ₗ[ℂ] EH n).restrict
    (p := ⊤) (q := ⊤) (fun _ _ => Submodule.mem_top)






theorem rsM_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : rsM A + rsM B = rsM (A + B) := by

  apply LinearMap.ext
  intro v
  apply Subtype.ext
  show toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A (v : EH n) + toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B (v : EH n) = toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (A + B) (v : EH n)
  rw [map_add]
  rfl

theorem rsM_smul {n : ℕ} (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) : c • rsM A = rsM (c • A) := by

  apply LinearMap.ext
  intro v
  apply Subtype.ext
  show c • toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A (v : EH n) = toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (c • A) (v : EH n)
  rw [map_smul]
  rfl

def rsL (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (⊤ : Submodule ℂ (EH n)) where
  toFun := rsM
  map_add' A B := (rsM_add A B).symm
  map_smul' c A := (rsM_smul c A).symm









end ReciprocityTheory.ChartRestriction.DS
