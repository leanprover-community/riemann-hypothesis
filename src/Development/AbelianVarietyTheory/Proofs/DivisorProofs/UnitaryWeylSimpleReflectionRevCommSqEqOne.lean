module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne

@[expose] public section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

namespace GlobalTheory

theorem simpleU_rev_and_sq : ∀ (n : ℕ) (k : Fin (n / 2)), (∀ i, simpleU k i.rev = (simpleU k i).rev) ∧ simpleU k * simpleU k = 1 := by
  intro n k
  have hk := k.isLt
  have hn : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  unfold simpleU partnerU
  split_ifs with h
  · refine ⟨fun i => ?_, ?_⟩
    · have hi := i.isLt
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
      split_ifs at * <;> simp only [Fin.ext_iff, Fin.val_rev, lo, Fin.coe_castLE] at * <;> omega
    · have hnd : [lo k, lo (⟨k.val + 1, h⟩ : Fin (n / 2)), (lo k).rev,
          (lo (⟨k.val + 1, h⟩ : Fin (n / 2))).rev].Nodup := by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
          and_true, Fin.ext_iff, Fin.val_rev, lo, Fin.coe_castLE, not_false_eq_true]
        omega
      have hc := (Equiv.Perm.disjoint_swap_swap hnd).commute
      rw [hc.symm.mul_mul_mul_comm, Equiv.swap_mul_self, Equiv.swap_mul_self, mul_one]
  · refine ⟨fun i => ?_, Equiv.swap_mul_self _ _⟩
    simp only [Equiv.swap_apply_def]
    split_ifs <;> simp_all [Fin.ext_iff, Fin.val_rev, lo] <;> omega

end GlobalTheory
