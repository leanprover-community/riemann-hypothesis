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

open Finset Comb

theorem CombTableauOfWord.proof (h1 : CombCellOfWordMem.Statement)
    (h2 : CombCellOfWordInj.Statement) (h3 : CombCellOfWordMono.Statement) :
    CombTableauOfWord.Statement := by
  intro m lam _hlam w hw
  have hL : IsLattice w := by
    simp only [latticeWords, mem_filter] at hw
    exact hw.2.1
  let f : Fin (youngCells lam).card → youngCells lam := fun t => ⟨cellOfWord w t, h1 m lam w hw t⟩
  have hinj : Function.Injective f := by
    intro s t hst
    exact h2 m _ w (congrArg Subtype.val hst)
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by simp⟩
  let T : youngCells lam ≃ Fin (youngCells lam).card := (Equiv.ofBijective f hbij).symm
  have hT : ∀ p : youngCells lam, cellOfWord w (T p) = p.1 := by
    intro p
    have : f (T p) = p := (Equiv.ofBijective f hbij).apply_symm_apply p
    exact congrArg Subtype.val this
  refine ⟨T, ?_, ?_⟩
  · intro p q hpq1 hpq2
    apply h3 m _ w hL
    · rw [hT p, hT q]; exact hpq1
    · rw [hT p, hT q]; exact hpq2
  · funext t
    show (T.symm t).1.1 = w t
    rfl

end GroundTheory.Heights₂.Heights.RestTerms
