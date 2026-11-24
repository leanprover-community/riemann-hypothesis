module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableToGLEntry
public import Development.AbelianVarietyTheory.Definitions.Divisors.MirSet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside

@[expose] public section

open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff

noncomputable section

namespace GlobalTheory.JSW

theorem colGL_val_apply {a : ℕ} (r : ℕ) (x : Fin a → ℂ) (i j : Fin a) :
    ((colGL r x : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j =
      (1 : Matrix (Fin a) (Fin a) ℂ) i j + (if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) := rfl

theorem colGL_inv_val_apply {a : ℕ} (r : ℕ) (x : Fin a → ℂ) (i j : Fin a) :
    (((colGL r x)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j =
      (1 : Matrix (Fin a) (Fin a) ℂ) i j - (if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) := rfl

theorem norm_one_apply_le' {a : ℕ} (i j : Fin a) : ‖(1 : Matrix (Fin a) (Fin a) ℂ) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem norm_ite_apply_le {a : ℕ} (p : Prop) [Decidable p] (x : Fin a → ℂ) (i : Fin a) :
    ‖(if p then x i else 0)‖ ≤ ‖x‖ := by
  split_ifs
  · exact norm_le_pi_norm x i
  · simp

theorem htGL_colGL_le {a : ℕ} (r : ℕ) (x : Fin a → ℂ) :
    htGL (colGL r x) ≤ 1 + 2 * (a : ℝ) ^ 2 * (1 + ‖x‖) := by
  unfold htGL
  have h1 : ∀ i j : Fin a, ‖((colGL r x : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j‖ ≤ 1 + ‖x‖ := by
    intro i j
    rw [colGL_val_apply]
    exact (norm_add_le _ _).trans (add_le_add (norm_one_apply_le' i j) (norm_ite_apply_le _ x i))
  have h2 : ∀ i j : Fin a, ‖(((colGL r x)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j‖ ≤ 1 + ‖x‖ := by
    intro i j
    rw [colGL_inv_val_apply]
    exact (norm_sub_le _ _).trans (add_le_add (norm_one_apply_le' i j) (norm_ite_apply_le _ x i))
  have s1 : ∑ i, ∑ j, ‖((colGL r x : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j‖ ≤ (a : ℝ) ^ 2 * (1 + ‖x‖) := by
    calc _ ≤ ∑ _i : Fin a, ∑ _j : Fin a, (1 + ‖x‖) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have s2 : ∑ i, ∑ j, ‖(((colGL r x)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j‖ ≤ (a : ℝ) ^ 2 * (1 + ‖x‖) := by
    calc _ ≤ ∑ _i : Fin a, ∑ _j : Fin a, (1 + ‖x‖) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h2 i j
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  linarith

theorem norm_inr_le_one' (Z V : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ‖ContinuousLinearMap.inr ℝ Z V‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simp [Prod.norm_def]

theorem norm_inl_le_one' (Z V : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ‖ContinuousLinearMap.inl ℝ Z V‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simp [Prod.norm_def]

end GlobalTheory.JSW
