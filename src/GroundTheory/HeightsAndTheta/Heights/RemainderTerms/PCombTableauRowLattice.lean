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

theorem CombTableauRowLattice.proof : CombTableauRowLattice.Statement := by
  classical
  intro m lam hlam T hT t i j hij
  have hmem : ∀ p : youngCells lam, p.1.1 = j → (i, p.1.2) ∈ youngCells lam := by
    intro p hp
    have hp' := p.2
    simp only [youngCells, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_range] at hp' ⊢
    have h1 : p.1.2 < lam i := by
      rw [hp] at hp'
      exact lt_of_lt_of_le hp'.2 (hlam hij)
    refine ⟨lt_of_lt_of_le h1 ?_, h1⟩
    exact Finset.single_le_sum (fun k _ => Nat.zero_le (lam k)) (Finset.mem_univ i)
  let f : youngCells lam → youngCells lam := fun p =>
    if h : p.1.1 = j then ⟨(i, p.1.2), hmem p h⟩ else p
  have hf : ∀ p : youngCells lam, ∀ h : p.1.1 = j, f p = ⟨(i, p.1.2), hmem p h⟩ := by
    intro p h
    simp only [f, dif_pos h]
  apply Finset.card_le_card_of_injOn f
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
    rw [hf p hp.1]
    refine ⟨rfl, lt_of_le_of_lt ?_ hp.2⟩
    have := hT ⟨(i, p.1.2), hmem p hp.1⟩ p (by simpa [hp.1] using hij) le_rfl
    exact_mod_cast this
  · intro p hp q hq hpq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
    rw [hf p hp.1, hf q hq.1] at hpq
    have h2 : p.1.2 = q.1.2 := by
      have := congrArg (fun x : youngCells lam => x.1.2) hpq
      simpa using this
    apply Subtype.ext
    exact Prod.ext (hp.1.trans hq.1.symm) h2

end GroundTheory.Heights₂.Heights.RestTerms
