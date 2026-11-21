import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactGelfandAverage.AvgStep

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.GelfCpt

open MeasureTheory Matrix


end PI.UnitaryGroupMassFormula.GelfCpt
end
end

section
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
end
end

section
noncomputable section

namespace PI.UnitaryGroupMassFormula.GelfCpt

open MeasureTheory Matrix

theorem integrable_of_continuous_cpt {X : Type} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    {F : X → ℂ} (hF : Continuous F) : Integrable F ν :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem mul_entry {N : ℕ} (μ : Measure G) [μ.IsHaarMeasure] (R : G → Matrix (Fin N) (Fin N) ℂ)
    (hR : ∀ i j, Continuous fun g => R g i j) (hRm : ∀ x y, R (x * y) = R x * R y)
    (f₁ f₂ : G → ℂ) (h₁ : Continuous f₁) (h₂ : Continuous f₂) (i j : Fin N) :
    ∑ k, (∫ x, f₁ x * R x i k ∂μ) * (∫ y, f₂ y * R y k j ∂μ) =
      ∫ z, (∫ x, f₁ x * f₂ (x⁻¹ * z) ∂μ) * R z i j ∂μ := by
  calc ∑ k, (∫ x, f₁ x * R x i k ∂μ) * (∫ y, f₂ y * R y k j ∂μ)
      = ∑ k, ∫ x, f₁ x * R x i k * (∫ y, f₂ y * R y k j ∂μ) ∂μ := by
        congr 1; funext k; rw [integral_mul_const]
    _ = ∫ x, ∑ k, f₁ x * R x i k * (∫ y, f₂ y * R y k j ∂μ) ∂μ := by
        rw [integral_finsetSum]
        intro k _
        exact integrable_of_continuous_cpt μ ((h₁.mul (hR i k)).mul continuous_const)
    _ = ∫ x, ∫ y, f₁ x * f₂ y * R (x * y) i j ∂μ ∂μ := by
        congr 1; funext x
        have e : ∀ y, f₁ x * f₂ y * R (x * y) i j = ∑ k, f₁ x * R x i k * (f₂ y * R y k j) := by
          intro y; rw [hRm, Matrix.mul_apply, Finset.mul_sum]; congr 1; funext k; ring
        simp_rw [e]
        rw [integral_finsetSum]
        · congr 1; funext k; rw [integral_const_mul]
        · intro k _
          exact integrable_of_continuous_cpt μ (continuous_const.mul (h₂.mul (hR k j)))
    _ = ∫ x, ∫ z, f₁ x * f₂ (x⁻¹ * z) * R z i j ∂μ ∂μ := by
        congr 1; funext x
        rw [← integral_mul_left_eq_self (fun z => f₁ x * f₂ (x⁻¹ * z) * R z i j) x]
        simp only [inv_mul_cancel_left]
    _ = ∫ z, ∫ x, f₁ x * f₂ (x⁻¹ * z) * R z i j ∂μ ∂μ := by
        rw [integral_integral_swap]
        exact integrable_of_continuous_cpt (μ.prod μ)
          (F := Function.uncurry fun x z => f₁ x * f₂ (x⁻¹ * z) * R z i j)
          (((h₁.comp continuous_fst).mul
            (h₂.comp (continuous_fst.inv.mul continuous_snd))).mul ((hR i j).comp continuous_snd))
    _ = ∫ z, (∫ x, f₁ x * f₂ (x⁻¹ * z) ∂μ) * R z i j ∂μ := by
        congr 1; funext z; rw [integral_mul_const]

end

theorem mulStep : MulStep := by
  intro G _ _ _ _ _ _ _ _ μ _ N ρ hc f₁ f₂ h₁ h₂
  ext i j
  simp only [intMat, Matrix.of_apply, Matrix.mul_apply]
  exact mul_entry μ (fun g => ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ))
    (fun i j => hc.matrix_elem i j) (fun x y => by simp only [map_mul, Units.val_mul])
    f₁ f₂ h₁ h₂ i j

end PI.UnitaryGroupMassFormula.GelfCpt
end
end

section
namespace PI.UnitaryGroupMassFormula.GelfCpt


end PI.UnitaryGroupMassFormula.GelfCpt
end
