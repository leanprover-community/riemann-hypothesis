module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.ThFacts
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial
namespace UpperTheory.V.Z.Sym.Wt
private theorem hq_kap (τ : ℂ) (j : ℕ) : hq (2 + τ) (2 + τ) (2 * j + 1) = (2 + τ) ^ (j + 1) * hq τ 1 j ∧ hq (2 + τ) (2 + τ) (2 * (j+1) + 1) = (2 + τ) ^ (j + 2) * hq τ 1 (j+1) := by
  have e : ∀ i, hq (2 + τ) (2 + τ) (i + 2) = (2 + τ) * hq (2 + τ) (2 + τ) (i + 1) - (2 + τ) * hq (2 + τ) (2 + τ) i :=
    fun i => hq.eq_3 _ _ i
  have f : ∀ i, hq τ 1 (i + 2) = τ * hq τ 1 (i + 1) - 1 * hq τ 1 i := fun i => hq.eq_3 _ _ i
  induction j with
  | zero =>
    have e2 : hq (2 + τ) (2 + τ) 2 = (2 + τ) * hq (2 + τ) (2 + τ) 1 - (2 + τ) * hq (2 + τ) (2 + τ) 0 := e 0
    have e3 : hq (2 + τ) (2 + τ) 3 = (2 + τ) * hq (2 + τ) (2 + τ) 2 - (2 + τ) * hq (2 + τ) (2 + τ) 1 := e 1
    refine ⟨?_, ?_⟩
    · show hq (2 + τ) (2 + τ) 1 = (2 + τ) ^ 1 * hq τ 1 0
      rw [hq.eq_2, hq.eq_1]
      ring
    · show hq (2 + τ) (2 + τ) 3 = (2 + τ) ^ 2 * hq τ 1 1
      rw [e3, e2, hq.eq_2, hq.eq_1, hq.eq_2]
      ring
  | succ j ih =>
    refine ⟨ih.2, ?_⟩
    have e5 : hq (2 + τ) (2 + τ) (2 * j + 5) =
        (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 4) - (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 3) := e (2 * j + 3)
    have e4 : hq (2 + τ) (2 + τ) (2 * j + 4) =
        (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 3) - (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 2) := e (2 * j + 2)
    have e3 : hq (2 + τ) (2 + τ) (2 * j + 3) =
        (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 2) - (2 + τ) * hq (2 + τ) (2 + τ) (2 * j + 1) := e (2 * j + 1)
    have f2 : hq τ 1 (j + 2) = τ * hq τ 1 (j + 1) - 1 * hq τ 1 j := f j
    have i0 : hq (2 + τ) (2 + τ) (2 * j + 1) = (2 + τ) ^ (j + 1) * hq τ 1 j := ih.1
    have i1 : hq (2 + τ) (2 + τ) (2 * j + 3) = (2 + τ) ^ (j + 2) * hq τ 1 (j + 1) := ih.2
    show hq (2 + τ) (2 + τ) (2 * j + 5) = (2 + τ) ^ (j + 3) * hq τ 1 (j + 2)
    rw [f2]
    linear_combination e5 + (2 + τ) * e4 + (2 + τ) * e3 + ((2 + τ) ^ 2 - 2 * (2 + τ)) * i1 - (2 + τ) ^ 2 * i0
theorem hqKappa : HqKappa := fun j τ => (hq_kap τ j).1
end UpperTheory.V.Z.Sym.Wt
