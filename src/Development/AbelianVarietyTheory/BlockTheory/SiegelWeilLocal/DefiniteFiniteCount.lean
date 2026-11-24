module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open NumberField MeasureTheory

namespace GlobalTheory.IndefiniteRowSideFullHecke.DefiniteFiniteCount

open Formalism.MainNotions.S GlobalTheory.Count

def DefiniteHyp (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p : ℕ) : Prop :=
  IsDSData B d ∧ SigIs B p 0 ∧ 1 ≤ p ∧ 1 ≤ B.g ∧ B.g₀.Prime ∧ 4 * B.I.n < B.g₀ ∧
    (Ideal.primesOver (Ideal.span {(B.g₀ : ℤ)}) (𝓞 B.I.E)).ncard = Module.finrank ℚ B.I.E

theorem DefiniteHyp.rank_eq {B : RowsAut} {d : InfinitePlace B.I.F → ℝ} {p : ℕ}
    (h : DefiniteHyp B d p) : B.I.n = p := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace B.I.F) := inferInstance
  obtain ⟨hp, hq⟩ := h.2.1 v
  unfold AutInst.pAt at hp
  unfold AutInst.qAt at hq
  have hall : ∀ a, B.I.ε v a = true := by
    intro a
    by_contra ha
    have hm : a ∈ (Finset.univ.filter fun a => B.I.ε v a = false) := by
      simpa using ha
    rw [Finset.card_eq_zero.mp hq] at hm
    simp at hm
  rw [← hp, Finset.filter_true_of_mem fun a _ => hall a]
  simp

end GlobalTheory.IndefiniteRowSideFullHecke.DefiniteFiniteCount
