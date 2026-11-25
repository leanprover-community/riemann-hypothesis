module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ExistsExpEqOfMemKset
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Taylor
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem actM_mem_of_isKStableSub_inK {S : Submodule ℂ D} (hS : IsKStableSub ε E S)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) {x : D} (hx : x ∈ S) :
    actM E Z x ∈ S := by
  have hZ0 : ∀ a b, ε a ≠ ε b → Z a b = 0 := by
    intro a b hab
    have h := congrFun (congrFun hZ.2 a) b
    simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    have hne : (if ε b = true then (1 : ℂ) else -1) - (if ε a = true then 1 else -1) ≠ 0 := by
      cases ha : ε a <;> cases hb : ε b <;> simp_all <;> norm_num
    have h2 : Z a b * ((if ε b = true then (1 : ℂ) else -1) - (if ε a = true then 1 else -1)) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp h2).resolve_right hne
  simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
  by_cases hab : ε a = ε b
  · exact S.smul_mem _ (hS a b hab x hx)
  · rw [hZ0 a b hab, zero_smul]
    exact S.zero_mem

theorem actM_pow_mem_of_isKStableSub_inK {S : Submodule ℂ D} (hS : IsKStableSub ε E S)
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) {x : D} (hx : x ∈ S) (m : ℕ) :
    ((actM E Z) ^ m) x ∈ S :=
  Module.End.pow_apply_mem_of_forall_mem m
    (fun _ hy => actM_mem_of_isKStableSub_inK hS hZ hy) x hx

theorem exists_norm_actM_pow_le_of_isKStableSub {S : Submodule ℂ D} (hS : IsKStableSub ε E S)
    (hSf : FiniteDimensional ℂ S) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ S, ∀ m : ℕ, ‖((actM E Z) ^ m) x‖ ≤ C ^ m * ‖x‖ := by
  haveI : FiniteDimensional ℂ S := hSf
  let g : S →ₗ[ℂ] S := (actM E Z).restrict fun x hx => actM_mem_of_isKStableSub_inK hS hZ hx
  let gL := Module.End.toContinuousLinearMap S g
  refine ⟨‖gL‖, norm_nonneg _, fun x hx m => ?_⟩
  rcases m with _ | m
  · simp
  · have hpow : (gL ^ (m + 1)) ⟨x, hx⟩ =
        ⟨((actM E Z) ^ (m + 1)) x, actM_pow_mem_of_isKStableSub_inK hS hZ hx _⟩ := by
      dsimp only [gL, g]
      rw [← map_pow, Module.End.pow_restrict]
      rfl
    have key := ((gL ^ (m + 1)).le_opNorm ⟨x, hx⟩).trans
      (mul_le_mul_of_nonneg_right (norm_pow_le' gL m.succ_pos) (norm_nonneg _))
    simpa [hpow] using key

theorem kStable_of_isKStableSub (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (S : Submodule ℂ D)
    (hS : FiniteDimensional ℂ S) (hk : IsKStableSub ε E S) :
    ∀ k ∈ Kset ε, ∀ v ∈ S, ∃ w ∈ S, (w : H) = σ k v := by
  intro g hg v hv
  obtain ⟨Z, hZ, rfl⟩ := exists_exp_eq_of_mem_Kset hg
  obtain ⟨C, hC0, hC⟩ := exists_norm_actM_pow_le_of_isKStableSub hk hS hZ
  have hs : Summable fun m : ℕ => (C ^ m * ‖v‖) * |(1 : ℝ) - 0| ^ m / (m.factorial : ℝ) := by
    simp only [sub_zero, abs_one, one_pow, mul_one]
    exact ((Real.summable_pow_div_factorial C).mul_right ‖v‖).congr fun m => by ring
  have h := hasSum_orbit_of_bound hσ hD hZ.1 v (fun m => C ^ m * ‖v‖) (fun m => hC v hv m) 0 1 hs
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, hσ.1.1,
    ContinuousLinearMap.one_apply, Complex.ofReal_one, one_smul] at h
  haveI : FiniteDimensional ℂ S := hS
  have hT : IsClosed ((S.map D.subtype : Submodule ℂ H) : Set H) :=
    Submodule.closed_of_finiteDimensional _
  have hmem : σ (NormedSpace.exp Z) (v : H) ∈ S.map D.subtype := by
    refine hT.mem_of_tendsto h.tendsto_sum_nat (Filter.Eventually.of_forall fun N => ?_)
    exact Submodule.sum_mem _ fun m _ =>
      Submodule.smul_mem _ _ ⟨_, actM_pow_mem_of_isKStableSub_inK hk hZ hv m, rfl⟩
  obtain ⟨w, hwS, hw⟩ := hmem
  exact ⟨w, hwS, hw⟩

end ReciprocityTheory.ChartRestriction.DS
