import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import BuildAid.ForwardExisting

section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem one_mem_strictPeriods_lev (N l : ℕ) :
    (1 : ℝ) ∈ ((lev N l : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem]
  · exact AddSubgroup.mem_zmultiples 1
  · refine ⟨?_, ?_⟩
    · show ModularGroup.T ∈ Gamma1 N
      rw [CongruenceSubgroup.Gamma1_mem]
      simp [ModularGroup.T]
    · show ModularGroup.T ∈ Gamma0 l
      rw [CongruenceSubgroup.Gamma0_mem]
      simp [ModularGroup.T]

theorem lev_hasSum_coef : ∀ (N l : ℕ) (k : ℤ), 0 < N → ∀ (f : ModularForm (lev N l) k) (τ : ℍ),
    HasSum (fun m => coef ⇑f m • Function.Periodic.qParam 1 τ ^ m) (f τ) := by
  intro N l k _ f τ
  have h1 := one_mem_strictPeriods_lev N l
  haveI : Fact (IsCusp OnePoint.infty ((lev N l : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos h1⟩
  exact ModularForm.hasSum_qExpansion f one_pos h1 τ

end GlobalTheory.Hk
end

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gamma1InterGamma0_modularForm_hasSum_qExpansion : ∀ (N l : ℕ) (k : ℤ), 0 < N → ∀ (f : ModularForm (GlobalTheory.Hk.lev N l) k) (τ : ℍ), HasSum (fun m => GlobalTheory.Hk.coef ⇑f m • Function.Periodic.qParam 1 τ ^ m) (f τ) := by
  atlas_forward_decl GlobalTheory.Hk.lev_hasSum_coef
