import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Filter Topology

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X]









theorem pushA_locInj {τ : (Fin e → ℂ) → (Fin e → ℂ)} {z : Fin e → ℂ} (hτ : AnalyticAt ℂ τ z)
    (hd : LinearMap.det (fderiv ℂ τ z : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) :
    ∃ W : Set (Fin e → ℂ), IsOpen W ∧ z ∈ W ∧ Set.InjOn τ W := by
  let L : (Fin e → ℂ) ≃L[ℂ] (Fin e → ℂ) :=
    (LinearMap.equivOfDetNeZero (fderiv ℂ τ z : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) hd).toContinuousLinearEquiv
  have hL : (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) = fderiv ℂ τ z := by
    ext v : 1
    simp [L]
  have hs : HasStrictFDerivAt τ (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) z := hL ▸ hτ.hasStrictFDerivAt
  refine ⟨(hs.toOpenPartialHomeomorph τ).source, (hs.toOpenPartialHomeomorph τ).open_source,
    hs.mem_toOpenPartialHomeomorph_source, ?_⟩
  have := (hs.toOpenPartialHomeomorph τ).injOn
  simpa using this







end

end ReciprocityTheory.AnForm.M
