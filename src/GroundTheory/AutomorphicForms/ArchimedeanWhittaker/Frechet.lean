import Mathlib
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ContinuousMultilinearOfFiniteDimensional

namespace GroundTheory.Automorphic

open NormedSpace Set Filter Topology Asymptotics
open scoped ContDiff

namespace IsExpLieAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)

noncomputable def wordSeminorm (Y : Σ k, Fin k → 𝔤) : Seminorm ℂ (h.smoothVectors π) :=
  Seminorm.of (fun v => ‖h.wordOp π Y.2 (v : E)‖)
    (fun v w => by
      simp only [Submodule.coe_add]
      rw [h.wordOp_add π v.2 w.2]
      exact norm_add_le _ _)
    (fun c v => by
      simp only [Submodule.coe_smul]
      rw [h.wordOp_smul π v.2, norm_smul])

def SmoothFrechet : Type _ := h.smoothVectors π

noncomputable instance : AddCommGroup (h.SmoothFrechet π) :=
  inferInstanceAs (AddCommGroup (h.smoothVectors π))

noncomputable instance : Module ℂ (h.SmoothFrechet π) :=
  inferInstanceAs (Module ℂ (h.smoothVectors π))

noncomputable def smoothSeminormFamily : SeminormFamily ℂ (h.SmoothFrechet π) (Σ k, Fin k → 𝔤) :=
  fun Y => h.wordSeminorm π Y

noncomputable instance : TopologicalSpace (h.SmoothFrechet π) :=
  (h.smoothSeminormFamily π).moduleFilterBasis.topology

theorem withSeminorms_smoothFrechet : WithSeminorms (h.smoothSeminormFamily π) := ⟨rfl⟩

instance : IsTopologicalAddGroup (h.SmoothFrechet π) :=
  (h.withSeminorms_smoothFrechet π).topologicalAddGroup

instance : ContinuousSMul ℂ (h.SmoothFrechet π) :=
  (h.withSeminorms_smoothFrechet π).continuousSMul

def IsSmoothContinuous (l : h.smoothVectors π →ₗ[ℂ] ℂ) : Prop :=
  ∃ (s : Finset (Σ k, Fin k → 𝔤)) (C : ℝ), ∀ v, ‖l v‖ ≤ C * ∑ Y ∈ s, ‖h.wordOp π Y.2 (v : E)‖


end IsExpLieAlgebra

end GroundTheory.Automorphic

namespace GroundTheory.Automorphic

open NormedSpace Set Filter Topology Asymptotics
open scoped ContDiff

namespace IsExpLieAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)

variable {h π}

theorem IsSmoothContinuous.hasDerivAt {l : h.smoothVectors π →ₗ[ℂ] ℂ}
    (hl : h.IsSmoothContinuous π l) {u : ℝ → h.smoothVectors π} {d : h.smoothVectors π}
    (hu : ∀ Y : (Σ k, Fin k → 𝔤),
      HasDerivAt (fun t => h.wordOp π Y.2 (u t : E)) (h.wordOp π Y.2 (d : E)) 0) :
    HasDerivAt (fun t => l (u t)) (l d) 0 := by
  obtain ⟨s, C, hC⟩ := hl
  rw [hasDerivAt_iff_isLittleO]
  have hY : ∀ Y ∈ s, (fun t : ℝ => ‖h.wordOp π Y.2 (u t : E) - h.wordOp π Y.2 (u 0 : E) -
      (t - 0) • h.wordOp π Y.2 (d : E)‖) =o[𝓝 0] fun t => t - 0 :=
    fun Y _ => (hasDerivAt_iff_isLittleO.1 (hu Y)).norm_left
  have hS := IsLittleO.sum hY
  refine IsBigO.trans_isLittleO (IsBigO.of_bound |C| (Eventually.of_forall fun t => ?_)) hS
  have e : l (u t) - l (u 0) - (t - 0) • l d = l (u t - u 0 - ((t : ℂ) • d)) := by
    rw [map_sub, map_sub, map_smul, smul_eq_mul, Complex.real_smul, sub_zero]
  have e2 : ∀ Y : (Σ k, Fin k → 𝔤), h.wordOp π Y.2 ((u t - u 0 - ((t : ℂ) • d) : h.smoothVectors π) : E) =
      h.wordOp π Y.2 (u t : E) - h.wordOp π Y.2 (u 0 : E) - (t - 0) • h.wordOp π Y.2 (d : E) := by
    intro Y
    simp only [Submodule.coe_sub, Submodule.coe_smul]
    rw [h.wordOp_sub π ((h.smoothVectors π).sub_mem (u t).2 (u 0).2)
      ((h.smoothVectors π).smul_mem _ d.2), h.wordOp_sub π (u t).2 (u 0).2,
      h.wordOp_smul π d.2, sub_zero, Complex.coe_smul]
  rw [e]
  refine (hC _).trans ?_
  simp_rw [e2]
  rw [Finset.sum_apply, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
  exact mul_le_mul_of_nonneg_right (le_abs_self C) (Finset.sum_nonneg fun _ _ => norm_nonneg _)

variable (h π) in

def smoothMap {v : E} (hv : h.IsSmoothVector π v) (g : G) : h.smoothVectors π :=
  ⟨π g v, h.isSmoothVector_map π hv g⟩

@[simp] theorem coe_smoothMap {v : E} (hv : h.IsSmoothVector π v) (g : G) :
    (h.smoothMap π hv g : E) = π g v := rfl

theorem IsSmoothContinuous.hasDerivAt_map_expG (hπ : ∀ g, ‖π g‖ ≤ 1)
    {l : h.smoothVectors π →ₗ[ℂ] ℂ} (hl : h.IsSmoothContinuous π l) {v : E}
    (hv : h.IsSmoothVector π v) (g : G) (X : 𝔤) :
    HasDerivAt (fun t : ℝ => l (h.smoothMap π hv (g * h.expG (t • X))))
      (l (h.smoothMap π (h.isSmoothVector_derivOp π hv X) g)) 0 := by
  refine hl.hasDerivAt fun Y => ?_
  simp only [coe_smoothMap, BanachRep.map_mul_apply]
  exact h.hasDerivAt_wordOp_map_expG π hπ hv X g Y.2

theorem IsSmoothContinuous.continuous_map (hπ : ∀ g, ‖π g‖ ≤ 1)
    {l : h.smoothVectors π →ₗ[ℂ] ℂ} (hl : h.IsSmoothContinuous π l) {v : E}
    (hv : h.IsSmoothVector π v) : Continuous fun g : G => l (h.smoothMap π hv g) := by
  obtain ⟨s, C, hC⟩ := hl
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hY : ∀ Y ∈ s, Tendsto (fun g : G => ‖h.wordOp π Y.2 (π g v) - h.wordOp π Y.2 (π g₀ v)‖)
      (𝓝 g₀) (𝓝 0) := fun Y _ => tendsto_iff_norm_sub_tendsto_zero.1
        ((h.continuous_wordOp_map π hπ hv Y.2).tendsto g₀)
  have hS := tendsto_finsetSum s hY
  simp only [Finset.sum_const_zero] at hS
  refine squeeze_zero (fun _ => norm_nonneg _) (fun g => ?_) (by simpa using hS.const_mul |C|)
  rw [← map_sub]
  refine (hC _).trans ?_
  have e : ∀ Y : (Σ k, Fin k → 𝔤),
      h.wordOp π Y.2 ((h.smoothMap π hv g - h.smoothMap π hv g₀ : h.smoothVectors π) : E) =
        h.wordOp π Y.2 (π g v) - h.wordOp π Y.2 (π g₀ v) := fun Y => by
    simp only [Submodule.coe_sub, coe_smoothMap]
    exact h.wordOp_sub π (h.isSmoothVector_map π hv g) (h.isSmoothVector_map π hv g₀) Y.2
  simp_rw [e]
  exact mul_le_mul_of_nonneg_right (le_abs_self C) (Finset.sum_nonneg fun _ _ => norm_nonneg _)


end IsExpLieAlgebra

end GroundTheory.Automorphic
