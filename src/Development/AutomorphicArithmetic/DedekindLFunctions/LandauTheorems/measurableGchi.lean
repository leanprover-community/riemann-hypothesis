module

public import Development.AutomorphicArithmetic.DedekindLFunctions.CharFamily
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Function.Floor
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

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem measurable_Gchi_floor (g : ℕ → ℝ → ℂ) (hg : ∀ k, Measurable (g k)) :
    Measurable (fun y : ℝ => g ⌊y⌋₊ y) := by
  have h : Measurable fun p : ℝ × ℕ => g p.2 p.1 :=
    measurable_from_prod_countable_left fun k => hg k
  exact h.comp (measurable_id.prodMk Nat.measurable_floor)

theorem measurable_Gchi_ramp (f : ℕ → ℂ) : Measurable (ramp f) := by
  unfold ramp
  refine measurable_Gchi_floor
    (fun k y => ∑ n ∈ Finset.range (k + 1),
      (ArithmeticFunction.vonMangoldt n : ℂ) * f n * ((max (y / n - 1) 0 : ℝ) : ℂ)) ?_
  intro k
  refine Finset.measurable_sum _ fun n _ => ?_
  fun_prop

theorem measurable_Gchi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Measurable (Gchi χ) := by
  unfold Gchi
  split_ifs
  · exact ((measurable_Gchi_ramp _).sub (by fun_prop)).add (by fun_prop)
  · exact (measurable_Gchi_ramp _).add (by fun_prop)

end Deduction

end
