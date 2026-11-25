module
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ClosureK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ExistsExpEqOfMemKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.PolarJmConjTranspose
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.RorthFunctionalEqZero
@[expose] public section
noncomputable section
open Finset Matrix
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem rigid_orth {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin n → Bool} {lam : Fin n → ℝ} (hgap : StdGap ε lam)
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (j' : V →ₗ[ℂ] H) (hj : ∀ k ∈ Kset ε, ∀ v w : V, ((w : D) : H) = σ k ((v : D) : H) → j' w = σ k (j' v))
    (horth : ∀ v v' : V, inner ℂ (j' v') ((v : D) : H) = 0) :
    ∀ g ∈ UJset ε, ∀ v v' : V, inner ℂ (j' v') (σ g ((v : D) : H)) = 0 := by
  intro g hg v v'
  apply rigid_orth_closure hgap hσ hD hV hc hVK j' hj horth v'
  obtain ⟨k, hk, Y, hY, rfl⟩ := polar_UJ hg
  have hkJ : kᴴ * Jm ε * k = Jm ε := closure_inUJ_of_mem_Kset hk
  change (k * NormedSpace.exp Y)ᴴ * Jm ε * (k * NormedSpace.exp Y) = Jm ε at hg
  rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc _ k _, Matrix.mul_assoc _ kᴴ _,
    Matrix.mul_assoc _ (kᴴ * Jm ε) _, hkJ] at hg
  rw [hσ.1.2 k hkJ (NormedSpace.exp Y) hg, ContinuousLinearMap.comp_apply]
  obtain ⟨Z, hZ, hZk⟩ := exists_exp_eq_of_mem_Kset hk
  refine closure_mapsTo_of_genSub (σ k) (fun w hw => ?_)
    (exp_apply_mem_topologicalClosure hσ hD hV.1 hV.2.1 hc hY (Submodule.mem_sInf.mpr fun T hT => hT.1 v.2))
  simpa only [hZk] using exp_inK_apply_mem_closure hσ hD hV.1 hV.2.1 hZ hw
end ReciprocityTheory.ChartRestriction.DS
