import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocallyConstantMajorants.StSmooth

open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.GodementSectionC

open Ad3.K.LC

noncomputable def rightMulLin (h : GL (Fin 3) ℂ) :
    (M23 × (Fin 2 → ℂ)) ≃ₗ[ℝ] (M23 × (Fin 2 → ℂ)) where
  toFun v := (Matrix.of.symm (Matrix.of v.1 * (h : Matrix (Fin 3) (Fin 3) ℂ)), v.2)
  invFun v := (Matrix.of.symm (Matrix.of v.1 * ((h⁻¹ : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)), v.2)
  map_add' v w := by
    refine Prod.ext ?_ rfl
    exact Matrix.add_mul (Matrix.of v.1) (Matrix.of w.1) (h : Matrix (Fin 3) (Fin 3) ℂ)
  map_smul' c v := by
    refine Prod.ext ?_ rfl
    exact Matrix.smul_mul c (Matrix.of v.1) (h : Matrix (Fin 3) (Fin 3) ℂ)
  left_inv v := by
    refine Prod.ext ?_ rfl
    change Matrix.of.symm (Matrix.of (Matrix.of.symm (Matrix.of v.1 * (h : Matrix (Fin 3) (Fin 3) ℂ))) *
      ((h⁻¹ : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ)) = v.1
    rw [Equiv.apply_symm_apply, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one, Equiv.symm_apply_apply]
  right_inv v := by
    refine Prod.ext ?_ rfl
    change Matrix.of.symm (Matrix.of (Matrix.of.symm (Matrix.of v.1 *
      ((h⁻¹ : GL (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ))) * (h : Matrix (Fin 3) (Fin 3) ℂ)) = v.1
    rw [Equiv.apply_symm_apply, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.mul_one, Equiv.symm_apply_apply]

theorem exists_rightTranslate (h : GL (Fin 3) ℂ) (Ψ : Sw) :
    ∃ Ψ' : Sw, ∀ (X : M23) (q : Fin 2 → ℂ),
      Ψ' (X, q) = Ψ (Matrix.of.symm (Matrix.of X * (h : Matrix (Fin 3) (Fin 3) ℂ)), q) :=
  ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rightMulLin h).toContinuousLinearEquiv Ψ,
    fun _ _ => rfl⟩


theorem inn_mul_right (Ψ Ψ₀ : Sw) (g h : GL (Fin 3) ℂ)
    (hΨ : ∀ (X : M23) (q : Fin 2 → ℂ),
      Ψ₀ (X, q) = Ψ (Matrix.of.symm (Matrix.of X * (h : Matrix (Fin 3) (Fin 3) ℂ)), q))
    (M : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    inn Ψ (g * h) M t = inn Ψ₀ g M t := by
  unfold inn
  congr 1
  funext p
  rw [hΨ, Units.val_mul, ← Matrix.mul_assoc]
  simp


end GlobalTheory.CompanionTheory.GodementSectionC
