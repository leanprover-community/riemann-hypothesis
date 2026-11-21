import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor

section
namespace GlobalTheory.WeightSubspaceComponent

open Formalism.BasicNotions.TH

theorem mem_wtSub_iff {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (x : V) :
    x ∈ wtSub act μ ↔ ∀ a, act (Eab a a) x = ((μ a : ℚ) : ℂ) • x := by
  unfold wtSub
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem weight_component_mem {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V)
    (hN : ∀ (a : Ix p q), ∀ x ∈ N, act (Eab a a) x ∈ N)
    (S : Finset (Ix p q → ℚ)) (f : (Ix p q → ℚ) → V)
    (hf : ∀ ν, f ν ∈ wtSub act ν) (hS : ∑ ν ∈ S, f ν ∈ N) : ∀ ν ∈ S, f ν ∈ N := by
  classical
  induction S using Finset.strongInduction generalizing f with
  | H S ih =>
    intro ν hν
    by_cases h : ∃ μ ∈ S, μ ≠ ν
    · obtain ⟨μ, hμ, hne⟩ := h
      obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
      let g : (Ix p q → ℚ) → V := fun l => (((l a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ)) • f l
      have hg : ∀ l, g l ∈ wtSub act l := fun l => Submodule.smul_mem _ _ (hf l)
      have hsum : ∑ l ∈ S.erase μ, g l
          = act (Eab a a) (∑ l ∈ S, f l) - ((μ a : ℚ) : ℂ) • ∑ l ∈ S, f l := by
        rw [Finset.sum_erase S (by simp [g]), map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [(mem_wtSub_iff act l (f l)).mp (hf l) a]
        exact sub_smul _ _ _
      have hmem : ∑ l ∈ S.erase μ, g l ∈ N := by
        rw [hsum]
        exact N.sub_mem (hN a _ hS) (N.smul_mem _ hS)
      have hgν := ih (S.erase μ) (Finset.erase_ssubset hμ) g hg hmem ν
        (Finset.mem_erase.mpr ⟨hne.symm, hν⟩)
      have hc : (((ν a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ)) ≠ 0 := by
        rw [sub_ne_zero]
        exact_mod_cast ha.symm
      exact (N.smul_mem_iff hc).mp hgν
    · have hone : ∑ l ∈ S, f l = f ν :=
        Finset.sum_eq_single_of_mem ν hν fun μ hμ hne => absurd ⟨μ, hμ, hne⟩ h
      rwa [hone] at hS

end GlobalTheory.WeightSubspaceComponent
end

section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.WeightDecomp

lemma comp_mem {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V)
    (hN : ∀ a, ∀ x ∈ N, act (Eab a a) x ∈ N) (S : Finset (Ix p q → ℚ)) :
    ∀ f : (Ix p q → ℚ) → V, (∀ ν, f ν ∈ wtSub act ν) → ∑ ν ∈ S, f ν ∈ N → ∀ ν ∈ S, f ν ∈ N := by
  first
  | exact @_root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem
  | exact _root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem
  | (apply _root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.WeightSubspaceComponent.weight_component_mem ..)

theorem mem_iSup_inf_wtSub : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V),
    (∀ a, ∀ x ∈ N, act (Eab a a) x ∈ N) → ∀ x ∈ N, x ∈ (⨆ μ : Ix p q → ℚ, wtSub act μ) →
      x ∈ ⨆ μ : Ix p q → ℚ, N ⊓ wtSub act μ := by
  intro p q V _ _ act N hN x hx hx'
  obtain ⟨f, hf, rfl⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx'
  have h := comp_mem act N hN f.support f hf hx
  refine Submodule.sum_mem _ fun ν hν => ?_
  exact Submodule.mem_iSup_of_mem ν ⟨h ν hν, hf ν⟩

end GlobalTheory.WeightDecomp
end
