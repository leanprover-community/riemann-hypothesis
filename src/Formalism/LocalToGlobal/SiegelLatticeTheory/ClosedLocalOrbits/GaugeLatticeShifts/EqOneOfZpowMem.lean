import Mathlib

noncomputable section

open MeasureTheory Topology Filter
open scoped ENNReal NNReal Pointwise

namespace Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

local notation "Δ" => Measure.modularCharacterFun (G := G)

theorem map_right (g : G) : (Measure.haar : Measure G).map (· * g) = Δ g • (Measure.haar : Measure G) :=
  Measure.map_right_mul_eq_modularCharacterFun_smul _ g

theorem haar_preimage (g : G) {A : Set G} (hA : MeasurableSet A) :
    (Measure.haar : Measure G) ((· * g) ⁻¹' A) = (Δ g : ℝ≥0∞) * (Measure.haar : Measure G) A := by
  have h : ((Measure.haar : Measure G).map (· * g)) A = (Δ g • (Measure.haar : Measure G)) A := by rw [map_right]
  rw [Measure.map_apply (measurable_mul_const g) hA] at h
  rw [h, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

theorem exists_compact_pos : ∃ C : Set G, IsCompact C ∧ 0 < (Measure.haar : Measure G) C ∧
    (Measure.haar : Measure G) C ≠ ⊤ := by
  obtain ⟨C, hC, h1⟩ := exists_compact_mem_nhds (1 : G)
  refine ⟨C, hC, ?_, hC.measure_lt_top.ne⟩
  exact Measure.measure_pos_of_nonempty_interior _ ⟨1, mem_interior_iff_mem_nhds.2 h1⟩


theorem eventually_lt (ε : ℝ) (hε : 0 < ε) : ∀ᶠ h in 𝓝 (1 : G), (Δ h : ℝ) < 1 + ε := by
  obtain ⟨C, hC, hpos, hfin⟩ := exists_compact_pos (G := G)
  have hlt : (Measure.haar : Measure G) C < ENNReal.ofReal (1 + ε) * (Measure.haar : Measure G) C := by
    have h1 : (1 : ℝ≥0∞) < ENNReal.ofReal (1 + ε) := by
      rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    have := ENNReal.mul_lt_mul_right hpos.ne' hfin h1
    simpa [mul_comm] using this
  obtain ⟨U, hCU, hU, hUlt⟩ := Set.exists_isOpen_lt_of_lt C _ hlt
  obtain ⟨V, hV, hCV⟩ := compact_open_separated_mul_right hC hU hCU
  have hV' : ∀ᶠ h in 𝓝 (1 : G), h⁻¹ ∈ V := by
    have ht : Tendsto (fun h : G => h⁻¹) (𝓝 1) (𝓝 1) := by simpa using continuous_inv.tendsto (1 : G)
    exact ht hV
  filter_upwards [hV'] with h hh
  have hsub : (· * h) ⁻¹' C ⊆ U := by
    intro x hx
    apply hCV
    exact ⟨x * h, hx, h⁻¹, hh, by group⟩
  have h2 : (Δ h : ℝ≥0∞) * (Measure.haar : Measure G) C < ENNReal.ofReal (1 + ε) * (Measure.haar : Measure G) C := by
    rw [← haar_preimage h hC.isClosed.measurableSet]
    exact lt_of_le_of_lt (measure_mono hsub) hUlt
  have h3 : (Δ h : ℝ≥0∞) < ENNReal.ofReal (1 + ε) :=
    not_le.1 fun hle => lt_irrefl _ (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle zero_le) h2)
  rw [← ENNReal.ofReal_coe_nnreal] at h3
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).1 h3



end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular
