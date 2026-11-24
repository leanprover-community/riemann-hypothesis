module

public import Formalism.RealPlaceAnalysis.StatementB
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset

noncomputable section

namespace Formalism.REAL

theorem generatorPowCovariance_holds : EpowCov := by
  intro A _ n E hE k
  induction k with
  | zero =>
    intro a b c d
    simp only [epow, @eq_comm _ b c, @eq_comm _ a d]
    have hl : E c d * (if a = b then (1 : A) else 0) - (if a = b then (1 : A) else 0) * E c d = 0 := by
      split_ifs <;> simp
    rw [hl]
    by_cases h2 : d = a <;> by_cases h3 : c = b <;> simp [h2, h3]
  | succ k ih =>
    intro a b c d
    simp only [epow]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    have step : ∀ e, E c d * (epow E k a e * E e b) - epow E k a e * E e b * E c d =
        ((if d = a then epow E k c e else 0) - (if e = c then epow E k a d else 0)) * E e b +
        epow E k a e * ((if d = e then E c b else 0) - (if b = c then E e d else 0)) := by
      intro e
      rw [← ih a e c d, ← hE c d e b]
      noncomm_ring
    simp only [step]
    by_cases hda : d = a <;> by_cases hbc : b = c <;>
      simp [hda, hbc, Finset.sum_add_distrib, Finset.sum_sub_distrib, sub_mul, mul_sub, ite_mul, mul_ite] <;> abel

theorem generatorTraceCentral_holds : EtrCentral := by
  intro A _ n E hE k c d
  have hc := generatorPowCovariance_holds A n E hE k
  unfold etr
  rw [Finset.sum_mul, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  have h1 : ∀ a, epow E k a a * E c d - E c d * epow E k a a =
      -((if d = a then epow E k c a else 0) - (if a = c then epow E k a d else 0)) := by
    intro a
    rw [← hc a a c d]
    abel
  simp only [h1, Finset.sum_neg_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, sub_self, neg_zero]

end Formalism.REAL
