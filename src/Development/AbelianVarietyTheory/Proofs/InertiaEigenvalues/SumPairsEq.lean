module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.WeightSumSplit

theorem sum_above {N : ℕ} (i : Fin N) (c : ℤ) :
    (∑ j : Fin N, if i < j then c else 0) = ((N : ℤ) - 1 - (i : ℕ)) * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_lt_eq_Ioi,
    Fin.card_Ioi, nsmul_eq_mul]
  have hi := i.isLt
  congr 1
  omega

theorem sum_below {N : ℕ} (j : Fin N) (c : ℤ) :
    (∑ i : Fin N, if i < j then c else 0) = ((j : ℕ) : ℤ) * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Finset.filter_gt_eq_Iio,
    Fin.card_Iio, nsmul_eq_mul]

theorem sum_pairs_eq (N : ℕ) (a : Fin N → ℤ) :
    (∑ i : Fin N, ∑ j : Fin N, if i < j then a i - a j else 0)
      = ∑ i : Fin N, ((N : ℤ) - 1 - 2 * ((i : ℕ) : ℤ)) * a i := by
  have h1 : ∀ i j : Fin N, (if i < j then a i - a j else 0) =
      (if i < j then a i else 0) - (if i < j then a j else 0) := by
    intro i j
    split_ifs <;> simp
  simp_rw [h1, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun i j : Fin N => if i < j then a j else 0)]
  simp_rw [sum_above, sum_below, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem wtS_eq : ∀ (N : ℕ) (a : Fin N → ℤ),
    GlobalTheory.CellDec.wtS N a = ∑ i : Fin N, ((↑N : ℤ) - (1 : ℤ) - (2 : ℤ) * (↑(↑i : ℕ) : ℤ)) * a i := by
  intro N a
  unfold GlobalTheory.CellDec.wtS
  exact sum_pairs_eq N a

end GlobalTheory.WeightSumSplit
