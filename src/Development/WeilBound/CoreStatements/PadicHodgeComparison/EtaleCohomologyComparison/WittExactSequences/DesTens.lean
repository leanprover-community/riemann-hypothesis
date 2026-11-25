module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.CechDifferentialOneInclusion
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.PowersGood
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ResKill
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ToPfFull
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

universe w v u v' u' v'' u''

namespace CrystallineSemistableComparison.D

variable (l : ℕ) [Fact l.Prime]

theorem rt_pow (k N : ℕ) : rt l (k + N) ^ (l ^ N) = rt l k := by
  induction N with
  | zero => rw [pow_zero, pow_one, add_zero]
  | succ N ih => rw [pow_succ', pow_mul, ← add_assoc, (isRt_rt l).1 (k + N), ih]

theorem rt_ideal (N : ℕ) : Ideal.span (Set.range (rt l)) ≤
    Ideal.span ((fun a => a ^ N) '' (Ideal.span (Set.range (rt l)) : Set (Ob l))) := by
  rw [Ideal.span_le]
  rintro _ ⟨k, rfl⟩
  have hN : N ≤ l ^ N := (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le
  rw [← rt_pow l k N, ← Nat.sub_add_cancel hN, pow_add]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨rt l (k + N), Ideal.subset_span ⟨k + N, rfl⟩, rfl⟩)

theorem des_tens (h : ObFacts l) (N : Type) [AddCommGroup N] [Module (Ob l) N] (M : ℕ) (hN : ∀ x : N, pFlat l ^ M • x = 0) (k : ℕ) :
    Des (toPf l ⋙ tensF l (Ob l) N) (rt l k) := by
  have := (toPf_full l).1
  have := (toPf_full l).2
  have hdes : DesJ (testι l ⋙ toPf l) (tensF l (Ob l) N) (rt l k) := fun A =>
    CrystallineSemistableComparison.P.induct (testι l ⋙ toPf l) (tensF l (Ob l) N) _ (rt_ideal l) (fun A => powers_good l h N M hN A) A _
      (Ideal.subset_span ⟨k, rfl⟩)
  exact des_ff (testι l) (toPf l) _ _ hdes

end CrystallineSemistableComparison.D
