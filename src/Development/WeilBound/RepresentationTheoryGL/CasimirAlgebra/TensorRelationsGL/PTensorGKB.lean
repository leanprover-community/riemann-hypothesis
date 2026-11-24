module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.KTypeData
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Finiteness.Lattice
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.TGK

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]

theorem actT_fin {ι Γ : Type} (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M)
    (hfin : ∀ y, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun γ => ρ γ y))) (y : TV n M P) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun γ => actT lab κ ρ γ y)) := by
  classical
  haveI hS : ∀ J : P → Fin n, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun γ => ρ γ (y J))) :=
    fun J => hfin (y J)
  set T : Submodule ℂ M := ⨆ J : P → Fin n, Submodule.span ℂ (Set.range fun γ => ρ γ (y J)) with hT
  haveI : FiniteDimensional ℂ T := by rw [hT]; infer_instance
  let L : ((P → Fin n) → T) →ₗ[ℂ] TV n M P := LinearMap.pi fun I => T.subtype ∘ₗ LinearMap.proj I
  have hle : Submodule.span ℂ (Set.range fun γ => actT lab κ ρ γ y) ≤ LinearMap.range L := by
    rw [Submodule.span_le]
    rintro _ ⟨γ, rfl⟩
    have hmem : ∀ I, actT lab κ ρ γ y I ∈ T := by
      intro I
      simp only [actT, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        LinearMap.comp_apply, LinearMap.proj_apply]
      refine Submodule.sum_mem _ fun J _ => Submodule.smul_mem _ _ ?_
      exact Submodule.mem_iSup_of_mem J (Submodule.subset_span ⟨γ, rfl⟩)
    exact ⟨fun I => ⟨_, hmem I⟩, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

theorem actT_cont {ι Γ : Type} [TopologicalSpace Γ] (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Γ → Module.End ℂ M) (hκ : ∀ τ i j, Continuous fun γ => κ τ γ i j)
    (hc : ∀ y (lam : M →ₗ[ℂ] ℂ), Continuous fun γ => lam (ρ γ y)) (y : TV n M P) (lam : TV n M P →ₗ[ℂ] ℂ) :
    Continuous fun γ => lam (actT lab κ ρ γ y) := by
  classical
  have h1 : ∀ x : TV n M P, lam x = ∑ I : P → Fin n, (lam ∘ₗ LinearMap.single ℂ (fun _ : P → Fin n => M) I) (x I) := by
    intro x
    conv_lhs => rw [← Finset.univ_sum_single x]

    simp [map_sum]
  have key : (fun γ => lam (actT lab κ ρ γ y)) = fun γ => ∑ I : P → Fin n, ∑ J : P → Fin n,
      (∏ p : P, κ (lab p) γ (I p) (J p)) * (lam ∘ₗ LinearMap.single ℂ (fun _ : P → Fin n => M) I) (ρ γ (y J)) := by
    funext γ
    rw [h1]
    refine Finset.sum_congr rfl fun I _ => ?_
    simp only [actT, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, LinearMap.proj_apply]

    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [map_smul, map_smul, smul_eq_mul]
  rw [key]
  refine continuous_finsetSum _ fun I _ => continuous_finsetSum _ fun J _ => ?_
  exact (continuous_finsetProd _ fun p _ => hκ _ _ _).mul (hc (y J) _)

end PositivityTheory.Rg.Cz.TGK

end
