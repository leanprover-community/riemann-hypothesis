module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup

@[expose] public section

open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S.ThB

namespace GlobalTheory

theorem hcParam_sub_integral : ∀ (n : ℕ) (lam lam' : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → Formalism.QuantumDeterminants.IsHCParam lam' → ∃ ν : Fin n → ℤ, lam' = (fun a => lam a + (ν a : ℝ)) ∧ ((BranchingSupport.n1 ν : ℕ) : ℝ) = l1 lam' lam ∧ ∀ s, |lam' s - lam s| ≤ l1 lam' lam := by
  intro n lam lam' h h'
  choose m hm using h.2
  choose m' hm' using h'.2
  have key : ∀ a, lam' a - lam a = ((m' a - m a : ℤ) : ℝ) := by
    intro a
    push_cast
    linarith [hm a, hm' a]
  refine ⟨fun a => m' a - m a, ?_, ?_, ?_⟩
  · funext a
    linarith [key a]
  · unfold BranchingSupport.n1 l1
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [key a, Nat.cast_natAbs, Int.cast_abs]
  · intro s
    unfold l1
    exact Finset.single_le_sum (f := fun a => |lam' a - lam a|) (fun a _ => abs_nonneg _) (Finset.mem_univ s)

end GlobalTheory
