module

public import Formalism.BranchSandwichDivisors.StatementR
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

open Finset

namespace Formalism.BranchingDeterminantCap

theorem interlaceIdentities : InterlaceIdent := by
  intro n lam sg h
  have hsum : ∑ i, lam i = lam 0 + ∑ i : Fin n, lam i.succ := Fin.sum_univ_succ lam
  have hsum' : ∑ i, lam i = ∑ i : Fin n, lam i.castSucc + lam (Fin.last n) := Fin.sum_univ_castSucc lam
  have hd0 : d0 lam sg = ∑ i, sg i - ∑ i : Fin n, lam i.succ := by
    rw [d0, Finset.sum_sub_distrib]
  have hnn : ∀ i, 0 ≤ sg i - lam i.succ := fun i => by linarith [(h i).2]
  have h3 : 0 ≤ d0 lam sg := Finset.sum_nonneg fun i _ => hnn i
  have hle : ∀ i, sg i - lam i.succ ≤ d0 lam sg := fun i =>
    Finset.single_le_sum (f := fun i => sg i - lam i.succ) (fun j _ => hnn j) (Finset.mem_univ i)
  have h5 : ∀ i, sg i ∈ rset lam sg i := by
    intro i
    rw [rset, Finset.mem_Icc]
    have := (h i).1
    have := (h i).2
    have := hle i
    omega
  refine ⟨by linarith, ?_, h3, ?_, h5, ?_⟩
  · rw [Finset.sum_sub_distrib]; linarith
  · refine Finset.sum_nonneg fun i _ => ?_
    have := (h i).1
    have := (h i).2
    omega
  · intro i
    have hmem := h5 i
    rw [Finset.card_erase_of_mem hmem]
    rw [rset, Finset.mem_Icc] at hmem
    rw [rset, Int.card_Icc]
    have hc : 0 ≤ min (lam i.castSucc) (lam i.succ + d0 lam sg) + 1 - lam i.succ := by omega
    have ht : ((min (lam i.castSucc) (lam i.succ + d0 lam sg) + 1 - lam i.succ).toNat : ℤ) =
        min (lam i.castSucc) (lam i.succ + d0 lam sg) + 1 - lam i.succ := Int.toNat_of_nonneg hc
    have h1 : 1 ≤ (min (lam i.castSucc) (lam i.succ + d0 lam sg) + 1 - lam i.succ).toNat := by omega
    rw [Nat.cast_sub h1, ht]
    push_cast
    omega

end Formalism.BranchingDeterminantCap
