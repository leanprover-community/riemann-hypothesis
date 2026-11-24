module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Data.Matrix.Mul
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.EntryNormProductBound

theorem sum_norm_entries_mul_le {n : ℕ} {α : Type} [NormedRing α]
    (a b : Matrix (Fin n) (Fin n) α) :
    ∑ i : Fin n, ∑ j : Fin n, ‖(a * b) i j‖ ≤
      (∑ i : Fin n, ∑ j : Fin n, ‖a i j‖) * ∑ i : Fin n, ∑ j : Fin n, ‖b i j‖ := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ∑ j : Fin n, ‖(a * b) i j‖
      ≤ ∑ j : Fin n, ∑ k : Fin n, ‖a i k‖ * ‖b k j‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.mul_apply]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_mul_le _ _)
    _ = ∑ k : Fin n, ‖a i k‖ * ∑ j : Fin n, ‖b k j‖ := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ k : Fin n, ‖a i k‖ * ∑ l : Fin n, ∑ j : Fin n, ‖b l j‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun l => ∑ j : Fin n, ‖b l j‖)
          (fun l _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ k)
    _ = (∑ k : Fin n, ‖a i k‖) * ∑ l : Fin n, ∑ j : Fin n, ‖b l j‖ :=
        (Finset.sum_mul _ _ _).symm

end GlobalTheory.EntryNormProductBound
