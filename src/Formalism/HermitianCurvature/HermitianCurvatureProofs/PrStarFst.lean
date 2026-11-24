module

public import Formalism.HermitianCurvature.StatementQ
public import Mathlib.CategoryTheory.Category.Basic
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd

section Act

variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : Type} [Fintype S] [DecidableEq S]

theorem pr_add_fst (p q : Q.Pr V) : (p + q).1 = p.1 + q.1 := rfl
theorem pr_mul_fst (p q : Q.Pr V) : (p * q).1 = p.1 * q.1 := rfl
theorem pr_zero_fst : (0 : Q.Pr V).1 = 0 := rfl
theorem pr_one_fst : (1 : Q.Pr V).1 = 1 := rfl

theorem pr_sum_fst {ι : Type*} (s : Finset ι) (f : ι → Q.Pr V) : (∑ i ∈ s, f i).1 = ∑ i ∈ s, (f i).1 := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, pr_zero_fst]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, pr_add_fst, ih]

def actP (M : SlopeTestRemainingChoices S (Q.Pr V)) (X : Ix S → V) : Ix S → V := fun a => ∑ b, (M a b).1 (X b)

theorem polyAction_mul (M N : SlopeTestRemainingChoices S (Q.Pr V)) (X : Ix S → V) : actP (M * N) X = actP M (actP N X) := by
  funext a
  unfold actP

  simp only [Matrix.mul_apply, pr_sum_fst, pr_mul_fst, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
  exact Finset.sum_comm

theorem polyAction_one₂ (X : Ix S → V) : actP (1 : SlopeTestRemainingChoices S (Q.Pr V)) X = X := by
  funext a
  unfold actP
  rw [Finset.sum_eq_single a]
  · rw [Matrix.one_apply_eq, pr_one_fst]
    rfl
  · intro b _ hb
    rw [Matrix.one_apply_ne (Ne.symm hb), pr_zero_fst]
    rfl
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem blockMulVec_add (M : SlopeTestRemainingChoices S (Q.Pr V)) (X Y : Ix S → V) : actP M (X + Y) = actP M X + actP M Y := by
  funext a
  simp only [actP, Pi.add_apply, map_add (f := _), Finset.sum_add_distrib]

theorem actP_smul (M : SlopeTestRemainingChoices S (Q.Pr V)) (c : ℂ) (X : Ix S → V) : actP M (c • X) = c • actP M X := by
  funext a
  simp only [actP, Pi.smul_apply, map_smul, Finset.smul_sum]

end Act

end Formalism.FourierDecayAlt.P.PBF
