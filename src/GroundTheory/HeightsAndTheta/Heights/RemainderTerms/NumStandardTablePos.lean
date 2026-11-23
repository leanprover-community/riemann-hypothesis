module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsTop
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

theorem numStandardTable_pos {m : ℕ} (lam : Fin m → ℕ) : 0 < numStandardTable lam := by
  classical
  let t : Finset (Fin m ×ₗ ℕ) := (youngCells lam).map (toLex : Fin m × ℕ ≃ _).toEmbedding
  have ht : t.card = (youngCells lam).card := Finset.card_map _
  let e : Fin (youngCells lam).card ≃o t := t.orderIsoOfFin ht
  let g : youngCells lam ≃ t :=
    Equiv.subtypeEquiv toLex fun p => by simp [t]
  let T : youngCells lam ≃ Fin (youngCells lam).card := g.trans e.symm.toEquiv
  have hT : ∀ p q : youngCells lam, p.1.1 ≤ q.1.1 → p.1.2 ≤ q.1.2 → T p ≤ T q := by
    intro p q h1 h2
    apply e.symm.monotone
    show toLex p.1 ≤ toLex q.1
    exact Prod.Lex.toLex_mono ⟨h1, h2⟩
  have : Nonempty {T : youngCells lam ≃ Fin (youngCells lam).card //
      ∀ p q : youngCells lam, p.1.1 ≤ q.1.1 → p.1.2 ≤ q.1.2 → T p ≤ T q} := ⟨⟨T, hT⟩⟩
  exact Nat.card_pos

theorem RectangleTablePos.intersectionNumber_baseChange : RectangleTablePos.Statement :=
  fun r a => numStandardTable_pos (rectangle r a)

end GroundTheory.Heights₂.Heights.RestTerms
