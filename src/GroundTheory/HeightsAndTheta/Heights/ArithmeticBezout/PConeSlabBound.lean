module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeSlab
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarietySlabMeasure
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormDimLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

open scoped ENNReal NNReal

noncomputable section

theorem ConeSlabBound.proof (hV : VarietySlabMeasure.Statement) : ConeSlabBound.Statement := by
  intro n e h W f u hW hf hu
  have hWp : W.IsPrime := hW.isPrime
  have hdim := ChowFormDimLe.proof ℂ n (e + 1) W f hW hf

  let E := WithLp.linearEquiv 2 ℂ (Fin n → ℂ)
  let F : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (E.symm.toLinearMap ∘ₗ h.matᵀ.mulVecLin ∘ₗ E.toLinearMap)
  let L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (E.symm.toLinearMap ∘ₗ (h.matᵀ)⁻¹.mulVecLin ∘ₗ E.toLinearMap)
  have hF : ∀ y i, F y i = h.pointOf y i := fun _ _ => rfl
  have hdet : IsUnit (h.matᵀ).det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  have hLF : ∀ y, L (F y) = y := by
    intro y
    ext i
    change ((h.matᵀ)⁻¹ *ᵥ (h.matᵀ *ᵥ fun j => y j)) i = y i
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  obtain ⟨C, α, hC, hα, hb⟩ := hV n (e + 1) W u hWp hdim hu ‖F‖
  set s : ℝ := ((2 * (e + 1) : ℕ) : ℝ) with hs
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  let K : ℝ≥0 := ‖L‖₊
  refine ⟨(K : ℝ) ^ s * C, α, hα, fun ε hε hε1 => ?_⟩

  have hsub : coneBall h W ∩ {y | ‖∑ j, u j * h.pointOf y j‖ ≤ ε * ‖y‖} ⊆
      L '' {z | z ∈ zeroSetEuc W ∧ ‖z‖ ≤ ‖F‖ ∧ ‖∑ j, u j * z j‖ ≤ ε} := by
    rintro y ⟨⟨hy1, hyW⟩, hyu⟩
    refine ⟨F y, ⟨fun q hq => ?_, ?_, ?_⟩, hLF y⟩
    · have : (fun i => F y i) = h.pointOf y := funext (hF y)
      rw [this]
      exact hyW q hq
    · calc ‖F y‖ ≤ ‖F‖ * ‖y‖ := F.le_opNorm y
        _ ≤ ‖F‖ * 1 := mul_le_mul_of_nonneg_left hy1.le (norm_nonneg _)
        _ = ‖F‖ := mul_one _
    · simp only [hF]
      calc ‖∑ j, u j * h.pointOf y j‖ ≤ ε * ‖y‖ := hyu
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hy1.le hε.le
        _ = ε := mul_one _
  calc μH[s] (coneBall h W ∩ {y | ‖∑ j, u j * h.pointOf y j‖ ≤ ε * ‖y‖})
      ≤ μH[s] (L '' {z | z ∈ zeroSetEuc W ∧ ‖z‖ ≤ ‖F‖ ∧ ‖∑ j, u j * z j‖ ≤ ε}) := measure_mono hsub
    _ ≤ (K : ℝ≥0∞) ^ s * μH[s] {z | z ∈ zeroSetEuc W ∧ ‖z‖ ≤ ‖F‖ ∧ ‖∑ j, u j * z j‖ ≤ ε} :=
        L.lipschitz.hausdorffMeasure_image_le hs0 _
    _ ≤ (K : ℝ≥0∞) ^ s * ENNReal.ofReal (C * ε ^ α) := by
        gcongr
        exact hb ε hε hε1
    _ = ENNReal.ofReal ((K : ℝ) ^ s * C * ε ^ α) := by
        rw [mul_assoc, ENNReal.ofReal_mul (Real.rpow_nonneg K.coe_nonneg _),
          ← ENNReal.ofReal_rpow_of_nonneg K.coe_nonneg hs0, ENNReal.ofReal_coe_nnreal]

end

end GroundTheory.Heights₂.Heights
