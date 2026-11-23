module

public import Formalism.PeriodIntegrals.ClassNumImQ
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticDifference.QuadraticDifferenceForm
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.ClassNumImQInt

open NumberField Polynomial

theorem adjoin_top {K : Type} [Field K] [NumberField K] (b : K)
    (h : IntermediateField.adjoin ℚ {b} = ⊤) : Algebra.adjoin ℚ {b} = ⊤ := by
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (Algebra.IsAlgebraic.isAlgebraic b), h]
  exact IntermediateField.top_toSubalgebra

theorem half_integral {K : Type} [Field K] [NumberField K] (d : ℕ) (b : K) (hd : d % 4 = 3)
    (hb : b ^ 2 = -(d : K)) : IsIntegral ℤ ((1 + b) / 2) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 4 * k := ⟨(d + 1) / 4, by omega⟩
  have hk' : (d : K) + 1 = 4 * (k : K) := by exact_mod_cast hk
  refine ⟨X ^ 2 - X + C (k : ℤ), by monicity!, ?_⟩
  simp only [eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_natCast, map_natCast]
  linear_combination (1 / 4 : K) * hb - (1 / 4 : K) * hk'

theorem intBasis : PI.ClassNumImQ.IntBasis := by
  intro d K _ _ b ⟨hp, hd, _, hb, htop⟩
  have hsq : Squarefree d := hp.prime.squarefree
  have htop' := adjoin_top b htop
  refine ⟨half_integral d b hd hb, ?_⟩
  intro z
  obtain ⟨x, y, hxy⟩ := PI.QD.quadratic_difference_form K d b hb htop' (z : K)
  have hint : IsIntegral ℤ ((x : K) + (y : K) * b) := by rw [← hxy]; exact z.isIntegral_coe
  obtain ⟨h2x, hN⟩ := PI.QD.quadratic_intCoeffs K d b x y hsq hd hb hint
  obtain ⟨a, v, hx, hy⟩ := PI.QD.quadraticDifferenceArith d x y hsq hd h2x hN
  refine ⟨a, v, ?_⟩
  rw [hxy, hx, hy]
  push_cast
  ring

end PI.UnitaryGroupMassFormula.ClassNumImQInt
