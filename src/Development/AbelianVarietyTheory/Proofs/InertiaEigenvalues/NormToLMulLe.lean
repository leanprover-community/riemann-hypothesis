module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
import GroundTheory.GlobalFields.KummerTheory.LocalIndex

@[expose] public section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section

namespace GlobalTheory.MSpanDecay.ColConvGrowth

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem norm_toL_mul_le (M P : Matrix (Fin a) (Fin a) (Cinf E)) :
    ‖toL (M * P)‖ ≤ (a : ℝ) * ‖toL M‖ * ‖toL P‖ := by
  have hM : ∀ i k, ‖M i k‖ ≤ ‖toL M‖ := fun i k =>
    (norm_le_pi_norm (toL M i) k).trans (norm_le_pi_norm (toL M) i)
  have hP : ∀ i k, ‖P i k‖ ≤ ‖toL P‖ := fun i k =>
    (norm_le_pi_norm (toL P i) k).trans (norm_le_pi_norm (toL P) i)
  refine pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun i =>
    pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun j => ?_
  change ‖(M * P) i j‖ ≤ _
  rw [Matrix.mul_apply]
  calc ‖∑ k, M i k * P k j‖ ≤ ∑ k, ‖M i k * P k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin a, ‖toL M‖ * ‖toL P‖ := Finset.sum_le_sum fun k _ =>
        (norm_mul_le _ _).trans (mul_le_mul (hM i k) (hP k j) (norm_nonneg _) (norm_nonneg _))
    _ = (a : ℝ) * ‖toL M‖ * ‖toL P‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

theorem height_mul_le (y u : GL (Fin a) (Cinf E)) :
    height (y * u) ≤ ((a : ℝ) + 1) * height y * height u := by
  have h1 := norm_toL_mul_le y.val u.val
  have h2 := norm_toL_mul_le (u⁻¹).val (y⁻¹).val
  have e1 : (y * u).val = y.val * u.val := rfl
  have e2 : ((y * u)⁻¹).val = (u⁻¹).val * (y⁻¹).val := by rw [_root_.mul_inv_rev]; rfl
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have n3 := norm_nonneg (toL u.val)
  have n4 := norm_nonneg (toL (u⁻¹).val)
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  unfold height
  rw [e1, e2]
  nlinarith [mul_nonneg n1 n3, mul_nonneg n2 n4, mul_nonneg n1 n4, mul_nonneg n2 n3,
    mul_nonneg ha (mul_nonneg n1 n3), mul_nonneg ha (mul_nonneg n2 n4), mul_nonneg ha n1, mul_nonneg ha n2,
    mul_nonneg ha n3, mul_nonneg ha n4, mul_nonneg ha (mul_nonneg n1 n4), mul_nonneg ha (mul_nonneg n2 n3)]

end GlobalTheory.MSpanDecay.ColConvGrowth

namespace GlobalTheory.MSpanDecay

end GlobalTheory.MSpanDecay
