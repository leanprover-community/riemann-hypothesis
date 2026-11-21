import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactGelfandAverage.AvgStep

noncomputable section

namespace PI.UnitaryGroupMassFormula.GelfCpt

open MeasureTheory Matrix

theorem integrable_of_cont {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] {F : X → ℂ} (hF : Continuous F) :
    Integrable F ν :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem haar_rightInv (μ : Measure G) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  constructor
  intro g
  have e := Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) μ) μ
  have hu : Measure.map (· * g) μ Set.univ = μ Set.univ := by
    rw [Measure.map_apply (measurable_mul_const g) MeasurableSet.univ, Set.preimage_univ]
  have h0 : μ Set.univ ≠ 0 := (Measure.measure_univ_pos.mpr (NeZero.ne μ)).ne'
  have ht : μ Set.univ ≠ ⊤ := measure_ne_top μ Set.univ
  have h1 : ((Measure.haarScalarFactor (Measure.map (· * g) μ) μ : NNReal) : ENNReal) * μ Set.univ =
      1 * μ Set.univ := by
    rw [one_mul]
    conv_rhs => rw [← hu, e]
    simp
  have hc : ((Measure.haarScalarFactor (Measure.map (· * g) μ) μ : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_left_inj h0 ht).1 h1
  rw [e, ENNReal.coe_eq_one.mp hc, one_smul]

theorem integral_conj (μ : Measure G) [μ.IsHaarMeasure] (F : G → ℂ) (h : G) :
    ∫ g, F (h * g * h⁻¹) ∂μ = ∫ g, F g ∂μ := by
  have := haar_rightInv μ
  have e1 := integral_mul_left_eq_self (μ := μ) (fun y => F (y * h⁻¹)) h
  have e2 := integral_mul_right_eq_self (μ := μ) F h⁻¹
  exact e1.trans e2



end


end PI.UnitaryGroupMassFormula.GelfCpt
