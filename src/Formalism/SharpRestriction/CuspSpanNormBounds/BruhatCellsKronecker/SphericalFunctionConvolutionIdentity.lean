import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.FlagUnipotentLattices.HalfDeltaL1Bound

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open MeasureTheory
open scoped InnerProductSpace ComplexOrder ENNReal

section Abs


variable {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]


theorem rep_mul_apply' (σ : G →* (H →L[ℂ] H)) (g h : G) (x : H) : σ (g * h) x = σ g (σ h x) := by
  rw [map_mul, ContinuousLinearMap.mul_apply]



variable [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G)


theorem inv_invariant_of_bi_invariant [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [μ.IsOpenPosMeasure] [SigmaFinite μ]
    (f : G → ℝ) (hf : Continuous f) (hi : Integrable f μ) (h1 : 0 < f 1) : μ.IsInvInvariant := by
  have hUo : IsOpen {h : G | f 1 / 2 < f h} := isOpen_lt continuous_const hf
  have h1U : (1 : G) ∈ {h : G | f 1 / 2 < f h} := by
    show f 1 / 2 < f 1
    linarith
  have hUfin : μ {h : G | f 1 / 2 < f h} < ⊤ := by
    refine lt_of_le_of_lt (measure_mono fun h hh => ?_) (hi.measure_norm_ge_lt_top (half_pos h1))
    have hh' : f 1 / 2 < f h := hh
    show f 1 / 2 ≤ ‖f h‖
    rw [Real.norm_eq_abs]
    exact hh'.le.trans (le_abs_self _)
  have hso : IsOpen ({h : G | f 1 / 2 < f h} ∩ {h : G | f 1 / 2 < f h}⁻¹) := hUo.inter hUo.inv
  have hs1 : (1 : G) ∈ {h : G | f 1 / 2 < f h} ∩ {h : G | f 1 / 2 < f h}⁻¹ :=
    ⟨h1U, by rw [Set.mem_inv, inv_one]; exact h1U⟩
  have hsinv : ({h : G | f 1 / 2 < f h} ∩ {h : G | f 1 / 2 < f h}⁻¹)⁻¹ =
      {h : G | f 1 / 2 < f h} ∩ {h : G | f 1 / 2 < f h}⁻¹ := by
    rw [Set.inter_inv, inv_inv, Set.inter_comm]
  have hs0 : μ ({h : G | f 1 / 2 < f h} ∩ {h : G | f 1 / 2 < f h}⁻¹) ≠ 0 :=
    hso.measure_ne_zero μ ⟨1, hs1⟩
  have hstop : μ ({h : G | f 1 / 2 < f h} ∩ {h : G | f 1 / 2 < f h}⁻¹) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono Set.inter_subset_left) hUfin).ne
  have key := measure_eq_div_smul μ.inv μ hs0 hstop
  rw [Measure.inv_apply, hsinv, ENNReal.div_self hs0 hstop, one_smul] at key
  exact ⟨key⟩

def SchurOrthogonalityRelation (σ : G →* (H →L[ℂ] H)) (d : ℝ) : Prop :=
  ∀ x y : H, Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧
      ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d





open Formalism.MainNotions.PlaceDegreeData (phA IsOpIntA)






variable {Hp : Type} [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp]








end Abs






end Formalism.MainNotions.BridgeLemma

end
