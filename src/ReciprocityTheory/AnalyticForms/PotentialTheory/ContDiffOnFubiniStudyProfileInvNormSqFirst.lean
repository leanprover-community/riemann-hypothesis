module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

namespace ReciprocityTheory.AnForm.M

open MeasureTheory OnePoint Filter Topology

noncomputable section

@[simp] theorem rea_apply (w : Fin 1 → ℂ) : p1Re w = (w 0).re := rfl
@[simp] theorem ima_apply (w : Fin 1 → ℂ) : p1Im w = (w 0).im := rfl

theorem projLine_continuous_of_smooth {e : ℕ} {X : Type*} [TopologicalSpace X]
    (A : FinHolAtlas e X) {f : X → ℝ} (hf : A.Smooth f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨j, hj⟩ := A.cover x
  have hf' : A.SmoothOn Set.univ f := hf
  have hc : ContinuousOn (f ∘ (A.chart j).symm) (A.chart j).target := by
    have h0 := (hf' j).continuousOn
    simpa using h0
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) :=
    hc.continuousAt ((A.chart j).open_target.mem_nhds ((A.chart j).map_source hj))
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ (A.chart j)) x :=
    h1.comp ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

end

end ReciprocityTheory.AnForm.M
