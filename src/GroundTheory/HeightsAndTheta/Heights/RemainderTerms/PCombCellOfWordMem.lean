module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

theorem Comb.pcnt_lt_pcnt_of_eq {m n : ℕ} (w : Fin n → Fin m) (t : Fin n) :
    pcnt w t (w t) < pcnt w n (w t) := by
  classical
  unfold pcnt
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨t, ?_, ?_⟩
    · simp
    · simp
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact ⟨lt_trans hs.1 t.2, hs.2⟩

theorem CombCellOfWordMem.proof : CombCellOfWordMem.Statement := by
  intro m lam w hw t
  classical
  have hc : ∀ i, pcnt w (youngCells lam).card i = lam i := by
    have := hw
    simp only [latticeWords, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this.2
  have hlt : pcnt w t (w t) < lam (w t) := by
    have := Comb.pcnt_lt_pcnt_of_eq w t
    rwa [hc] at this
  have hle : lam (w t) ≤ ∑ i, lam i :=
    Finset.single_le_sum (f := lam) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  simp only [youngCells, cellOfWord, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
    Finset.mem_range, true_and]
  exact ⟨lt_of_lt_of_le hlt hle, hlt⟩

end GroundTheory.Heights₂.Heights.RestTerms
