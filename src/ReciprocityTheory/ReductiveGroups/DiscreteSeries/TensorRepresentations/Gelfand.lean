module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
public import Lemmata.MiscLemmasP.Imports
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

def ePow (E : Fin n → Fin n → Module.End ℂ M) : ℕ → Fin n → Fin n → Module.End ℂ M :=
  Bl.ThirdBlockLemmaA.goal1 E

def gelfand (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) : Module.End ℂ M :=
  ∑ a, ePow E k a a

theorem commutator_mul_right (X Y Z : Module.End ℂ M) :
    X * (Y * Z) - Y * Z * X = (X * Y - Y * X) * Z + Y * (X * Z - Z * X) := by
  noncomm_ring

theorem ePow_comm {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (k : ℕ) (a b c d : Fin n) :
    E a b * ePow E k c d - ePow E k c d * E a b =
      (if b = c then ePow E k a d else 0) - (if d = a then ePow E k c b else 0) := by
  have hz : ∀ c d, ePow E 0 c d = if c = d then 1 else 0 := fun c d => rfl
  have hs : ∀ k c d, ePow E (k + 1) c d = ∑ e, E c e * ePow E k e d := by
    intro k c d
    unfold ePow Bl.ThirdBlockLemmaA.goal1
    simp [pow_succ', Matrix.mul_apply]
  induction k generalizing c d with
  | zero =>
    simp only [hz]
    split_ifs <;> subst_vars <;> simp_all
  | succ k ih =>
    rw [hs, hs, hs, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp_rw [commutator_mul_right, hE a b c, ih]
    by_cases hbc : b = c <;> by_cases hda : d = a <;>
      simp [hbc, hda, sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib, ite_mul, mul_ite,
        Finset.sum_ite_eq, Finset.sum_ite_eq'] <;> abel

theorem gelfand_comm {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (k : ℕ) (a b : Fin n) :
    E a b * gelfand E k = gelfand E k * E a b := by
  have h : E a b * gelfand E k - gelfand E k * E a b = 0 := by
    unfold gelfand
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    simp_rw [ePow_comm hE]
    simp [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']
  exact sub_eq_zero.mp h

end ReciprocityTheory.ChartRestriction.DS
