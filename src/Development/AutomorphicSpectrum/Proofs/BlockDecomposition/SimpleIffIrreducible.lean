module

public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HarishChandraLabels.Basics
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

@[expose] public section

open CategoryTheory ReciprocityTheory.Ty.Fin PI.GreenHCLabel

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin

theorem nonempty_iso_iff_intertwiner {Γ : Type} [Group Γ] (τ σ : FDRep ℂ Γ) :
    Nonempty (τ ≅ σ) ↔ ∃ e : τ ≃ₗ[ℂ] σ, ∀ γ v, e (τ.ρ γ v) = σ.ρ γ (e v) := by
  constructor
  · rintro ⟨i⟩
    refine ⟨FDRep.isoToLinearEquiv i, fun γ v => ?_⟩
    rw [FDRep.Iso.conj_ρ i γ, LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  · rintro ⟨e, he⟩
    have h1 : ∀ g, e.toLinearMap ∘ₗ τ.ρ g = σ.ρ g ∘ₗ e.toLinearMap :=
      fun g => LinearMap.ext fun v => he g v
    have h2 : ∀ g, e.symm.toLinearMap ∘ₗ σ.ρ g = τ.ρ g ∘ₗ e.symm.toLinearMap := by
      intro g
      refine LinearMap.ext fun v => ?_
      show e.symm (σ.ρ g v) = τ.ρ g (e.symm v)
      apply e.injective
      rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    refine ⟨{ hom := basicsMk e.toLinearMap h1
              inv := basicsMk e.symm.toLinearMap h2
              hom_inv_id := ?_
              inv_hom_id := ?_ }⟩
    · ext v
      simp [basicsMk]
    · ext v
      simp [basicsMk]

theorem simpleIffIrr : ReciprocityTheory.Ty.Fin.St.SimpleIffIrr := by
  unfold ReciprocityTheory.Ty.Fin.St.SimpleIffIrr
  exact ⟨fun Γ _ _ τ => simple_irreducible Γ τ,
    fun Γ _ _ τ σ => nonempty_iso_iff_intertwiner τ σ⟩

end GlobalTheory.CompanionTheory.TyFin
