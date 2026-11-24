module

public import Formalism.LocalRingCardinality.DataKerI
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

@[expose] public section

open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory

theorem youngDiagram_card_eq_sum_rowLen_range (μ : YoungDiagram) (n : ℕ) (h : μ.colLen 0 ≤ n) :
    μ.card = ∑ r ∈ Finset.range n, μ.rowLen r := by
  have hmap : ∀ c ∈ μ.cells, c.1 ∈ Finset.range n := by
    intro c hc
    rw [Finset.mem_range]
    have h1 : (c.1, c.2) ∈ μ := hc
    have h2 : (c.1, 0) ∈ μ := μ.up_left_mem le_rfl (Nat.zero_le _) h1
    exact lt_of_lt_of_le (YoungDiagram.mem_iff_lt_colLen.1 h2) h
  unfold YoungDiagram.card
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (fun c hc => hmap c hc)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [YoungDiagram.rowLen_eq_card]
  rfl

theorem nuD_card_eq_sum_nuRow : ∀ (D : D7), NuRowOK D → ∀ (u : D.what₂.Word), ∀ j < D.R.m, ∀ (z : Bool × HH D), (((nuD D u j z).card : ℕ) : ℝ) = ∑ r ∈ Finset.range (D.R.N j), DV.nuRow D u (j + 1) (tauPl D z) r := by
  intro D hD u j hj z
  rw [youngDiagram_card_eq_sum_rowLen_range _ _ (nuD_rows D u j z), Nat.cast_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [hD u j hj z r, if_pos (Finset.mem_range.1 hr)]

end GlobalTheory
