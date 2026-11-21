import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramIsHermitianL2EqDoubleSum

section
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_isHermitian_l2_eq_double_sum : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (gram μ v).IsHermitian ∧ ∀ c : ι → ℂ, (∀ σ, Integrable (cmb v c σ) (μ σ)) ∧ 0 ≤ l2 μ v c ∧ (l2 μ v c : ℂ) = ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * gram μ v i j := by
  first | exact @GlobalTheory.HSAmp.gram_isHermitian_and_l2_eq_quadratic_form | exact GlobalTheory.HSAmp.gram_isHermitian_and_l2_eq_quadratic_form | (intros; apply GlobalTheory.HSAmp.gram_isHermitian_and_l2_eq_quadratic_form <;> assumption)
end

section
section
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp

theorem gram_posDef : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι]
    (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (∀ c : ι → ℂ, l2 μ v c = 0 → c = 0) →
    (gram μ v).PosDef := by
  intro S Y _ ι _ _ μ v hF hinj
  obtain ⟨hH, hl⟩ := GlobalTheory.T.gram_isHermitian_l2_eq_double_sum S Y ι μ v hF
  refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hH, fun x hx => ?_⟩
  obtain ⟨-, h0, heq⟩ := hl (fun i => (starRingEnd ℂ) (x i))
  have hform : star x ⬝ᵥ (gram μ v *ᵥ x) = ((l2 μ v (fun i => (starRingEnd ℂ) (x i)) : ℝ) : ℂ) := by
    rw [heq]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def, Complex.conj_conj]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hform]
  have hne : l2 μ v (fun i => (starRingEnd ℂ) (x i)) ≠ 0 := by
    intro h
    apply hx
    funext i
    have := congrFun (hinj _ h) i
    simpa using this
  exact_mod_cast lt_of_le_of_ne h0 (Ne.symm hne)

end GlobalTheory.HSAmp
end

open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_posDef_of_l2_definite : ∀ (S : Type) (Y : S → Type) [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι] [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ), IsFam μ v → (∀ c : ι → ℂ, l2 μ v c = 0 → c = 0) → (gram μ v).PosDef := by
  atlas_forward_decl GlobalTheory.HSAmp.gram_posDef
end
