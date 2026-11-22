module

public import Mathlib
public import GroundTheory.AutomorphicForms.GKModules.SmoothVectors

@[expose] public section

namespace GroundTheory.Automorphic

open NormedSpace Set Filter Topology
open scoped Manifold ContDiff

set_option linter.unusedSectionVars false

attribute [local instance 100] LieRing.ofAssociativeRing

section KHom

variable {K : Type*} [Monoid K]
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {V : Type*} [AddCommGroup V] [Module ℂ V]

end KHom

def Representation.HasContinuousCoeff {K : Type*} [Monoid K] [TopologicalSpace K]
    {W : Type*} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ K W) : Prop :=
  ∀ (φ : Module.Dual ℂ W) (w : W), Continuous fun k => φ (τ k w)

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

structure GKModule (K : Subgroup G) (V : Type*) [AddCommGroup V] [Module ℂ V] where

  ρ : h.lieSubalgebra →ₗ⁅ℝ⁆ Module.End ℂ V

  σ : Representation ℂ K V

  locallyFinite : ∀ v : V, FiniteDimensional ℂ (Submodule.span ℂ (range fun k : K => σ k v))

  hasContinuousCoeff : Representation.HasContinuousCoeff σ

  hasDerivAt_coeff : ∀ (X : 𝔤) (hX : ∀ t : ℝ, h.expG (t • X) ∈ K) (φ : Module.Dual ℂ V) (v : V),
    HasDerivAt (fun t : ℝ => φ (σ ⟨h.expG (t • X), hX t⟩ v)) (φ (ρ (h.toLie X) v)) 0

  map_ρ : ∀ (k : K) (X : 𝔤) (v : V), σ k (ρ (h.toLie X) v) = ρ (h.toLie (h.Ad k X)) (σ k v)

end IsExpLieAlgebra

namespace BanachRep

variable {K' : Type*} [Group K'] [TopologicalSpace K']
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def toRepresentation (π : BanachRep K' E) : Representation ℂ K' E where
  toFun k := (π k : E →ₗ[ℂ] E)
  map_one' := by ext v; simp
  map_mul' k k' := by ext v; simp [map_mul_apply]

noncomputable def restrict (π : BanachRep K' E) (K : Subgroup K') : BanachRep K E where
  toHom := π.toHom.comp K.subtype
  continuous_orbit' v := (π.continuous_orbit v).comp continuous_subtype_val

variable (π : BanachRep K' E) (K : Subgroup K')

def kSpan (v : E) : Submodule ℂ E := Submodule.span ℂ (range fun k : K => π k v)

theorem mem_kSpan_self (v : E) : v ∈ π.kSpan K v :=
  Submodule.subset_span ⟨1, by simp⟩

theorem map_mem_kSpan_of_mem {v w : E} (hw : w ∈ π.kSpan K v) (k : K) : π k w ∈ π.kSpan K v := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k', rfl⟩ := hx
    rw [← map_mul_apply]
    exact Submodule.subset_span ⟨k * k', by simp⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end BanachRep

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E) (K : Subgroup G)

end IsExpLieAlgebra

end GroundTheory.Automorphic
