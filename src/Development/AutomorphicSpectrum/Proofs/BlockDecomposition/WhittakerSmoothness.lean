import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import GroundTheory.AutomorphicForms.GL2.GodementSectionLocal

section
set_option maxSynthPendingDepth 1

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.GodementSectionLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.GodementFix

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_congruence_fix {χ : Fˣ →* ℂˣ} (h : Continuous χ) {Φ : (Fin 2 → F) → ℂ}
    (hΦ : Φ ∈ schwartzBruhat2 F) :
    ∃ m : ℕ, ∀ u ∈ GLnLocal.congruenceSubgroup F 2 m,
      rightTranslate u Φ = Φ ∧ χ (detU u) = 1 ∧ ∀ s : ℂ, modPow ((detU u : Fˣ) : F) s = 1 := by
  obtain ⟨N, M, hMN, hinv, hsupp⟩ := exists_invariant_of_mem_schwartzBruhat2 hΦ
  refine ⟨max (N - M).toNat (max (quasiCharConductor χ) 1), fun u hu ↦ ?_⟩
  set m := max (N - M).toNat (max (quasiCharConductor χ) 1) with hm
  have hu0 : u ∈ GLnLocal.integralGL F 2 := GLnLocal.congruenceSubgroup_le F 2 m hu
  refine ⟨?_, ?_, fun s ↦ ?_⟩
  · funext x
    simp only [rightTranslate]
    by_cases hx : x ∈ box F M
    · set D : Matrix (Fin 2) (Fin 2) F := (u : Matrix (Fin 2) (Fin 2) F) - 1 with hD
      have hxD : x ᵥ* D ∈ box F N := by
        refine box_antitone (show N ≤ M + m by omega) (mem_box.2 fun j ↦ ?_)
        simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
        exact add_mem (mul_mem_valBall (mem_box.1 hx 0)
            (sub_one_mem_valBall_of_mem_congruenceSubgroup hu 0 j))
          (mul_mem_valBall (mem_box.1 hx 1)
            (sub_one_mem_valBall_of_mem_congruenceSubgroup hu 1 j))
      have he : x ᵥ* (u : Matrix (Fin 2) (Fin 2) F) = x + x ᵥ* D := by
        rw [hD, Matrix.vecMul_sub, Matrix.vecMul_one]
        abel
      rw [he, hinv x _ hxD]
    · have h0 : Φ x = 0 := by
        by_contra h
        exact hx (hsupp x h)
      have h1 : Φ (x ᵥ* (u : Matrix (Fin 2) (Fin 2) F)) = 0 := by
        by_contra h
        exact hx ((vecMul_mem_box_iff hu0 M x).1 (hsupp _ h))
      rw [h0, h1]
  · have hmem : detU u ∈ unitFiltrationUnits F m :=
      (mem_unitFiltrationUnits_iff_valBall (by omega)).2 (det_sub_one_mem_valBall hu)
    exact unitFiltrationUnits_quasiCharConductor_le_ker h
      (unitFiltrationUnits_antitone (by omega) hmem)
  · rw [modPow_units_eq_zpow, ord_det_eq_zero hu0]
    simp

end GlobalTheory.CompanionTheory.GodementFix
end

section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.WhittakerSmooth

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem whittaker_invariant_under_fixing_subgroup (ψ : AddChar F Circle) (μ₁ μ₂ : Fˣ →* ℂˣ) (φ : (Fin 2 → F) → ℂ)
    (u : GL (Fin 2) F) (hφ : GodementSectionLocal.rightTranslate u φ = φ)
    (hμ : μ₂ (GeneralLinearGroup.det u) = 1)
    (hm : GodementSectionLocal.modPow ((GeneralLinearGroup.det u : Fˣ) : F) (1 / 2) = 1)
    (g : GL (Fin 2) F) : W2 ψ μ₁ μ₂ φ (g * u) = W2 ψ μ₁ μ₂ φ g := by
  have hv : ∀ v : Fin 2 → F, φ (v ᵥ* ((g * u : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) =
      φ (v ᵥ* (g : Matrix (Fin 2) (Fin 2) F)) := by
    intro v
    rw [Units.val_mul, ← Matrix.vecMul_vecMul]
    exact congrFun hφ _
  have hmp : mp (GeneralLinearGroup.det (g * u)) (1 / 2) = mp (GeneralLinearGroup.det g) (1 / 2) := by
    change GodementSectionLocal.modPow ((GeneralLinearGroup.det (g * u) : Fˣ) : F) (1 / 2) =
      GodementSectionLocal.modPow ((GeneralLinearGroup.det g : Fˣ) : F) (1 / 2)
    rw [map_mul, Units.val_mul, GodementSectionLocal.modPow_mul, hm, mul_one]
  unfold W2
  rw [hmp, map_mul (GeneralLinearGroup.det) g u, map_mul μ₂, hμ, mul_one]
  simp only [hv]

theorem sSmooth : Ad3.SchwartzSpaceL2.SSmooth := by
  intro F _ _ _ _ _ _ ψ _ μ₁ μ₂ _ hμ₂ φ hφ
  obtain ⟨m, hm⟩ := GlobalTheory.CompanionTheory.GodementFix.exists_congruence_fix hμ₂.1 hφ
  refine ⟨⟨GLnLocal.congruenceSubgroup F 2 m, GLnLocal.isOpen_congruenceSubgroup F 2 m⟩,
    fun g u hu ↦ ?_⟩
  obtain ⟨h1, h2, h3⟩ := hm u hu
  exact whittaker_invariant_under_fixing_subgroup ψ μ₁ μ₂ φ u h1 h2 (h3 _) g

end GlobalTheory.CompanionTheory.WhittakerSmooth
end
end
