module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SecondClosedOfFirstClosed

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.SSComplement

section Rep

variable {Γ k : Type} [Group Γ] [Field k]

def blockM {a b n : ℕ} (e0 : Fin a ⊕ Fin b ≃ Fin n) (ρ₁ : Γ →* GL (Fin a) k) (ρ₂ : Γ →* GL (Fin b) k) :
    Γ →* Matrix (Fin n) (Fin n) k where
  toFun g := Matrix.reindex e0 e0
    (Matrix.fromBlocks (ρ₁ g : Matrix (Fin a) (Fin a) k) 0 0 (ρ₂ g : Matrix (Fin b) (Fin b) k))
  map_one' := by simp
  map_mul' g g' := by simp [Matrix.fromBlocks_multiply]

def diagM {t : ℕ} (χ : Fin t → Γ →* kˣ) : Γ →* Matrix (Fin t) (Fin t) k where
  toFun g := Matrix.diagonal fun c => ((χ c g : kˣ) : k)
  map_one' := by simp
  map_mul' g h := by simp [Matrix.diagonal_mul_diagonal]

theorem blockM_ss {a b n : ℕ} (e0 : Fin a ⊕ Fin b ≃ Fin n) (ρ₁ : Γ →* GL (Fin a) k)
    (ρ₂ : Γ →* GL (Fin b) k) (h₁ : IsSSRep ρ₁) (h₂ : IsSSRep ρ₂) : IsSSRep (blockM e0 ρ₁ ρ₂).toHomUnits := by
  refine GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSSRep_of_prod ((LinearEquiv.funCongrLeft k k e0).trans
    (LinearEquiv.sumArrowLequivProdArrow _ _ k k)) (fun g v => ?_) h₁ h₂
  show _ = _
  ext i <;> simp [blockM, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, LinearMap.funLeft] <;> rfl

end Rep

end GlobalTheory.SSComplement
