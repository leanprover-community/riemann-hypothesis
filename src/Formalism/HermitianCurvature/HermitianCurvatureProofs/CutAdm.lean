module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMP2
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP

open Formalism.FourierDecayAlt

theorem admissible_in_truncation_holds : AdmInCut := by
  intro E _ _ _ Wp Wq _ _ _ _ S hG v a ha x hx
  obtain ⟨w, rfl⟩ := ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have h1 := w.2.1.1 v j hj
  have hnode := (hG v).2.2.2.2.2
  have hcut : ∀ Y ∈ (S.G.place (S.pl v)).cutI S.l, Y ∈ Set.Icc (S.cutLo v) (S.cutHi v) := by
    intro Y hY
    simp only [Sz.Cfg.cutI, Set.mem_setOf_eq] at hY
    simp only [C.HidaSetting.cutLo, C.HidaSetting.cutHi, Set.mem_Icc]
    constructor <;> linarith [hY.1, hY.2]
  by_cases hp : ((w.1 v)[j]'hj).1
  · rw [if_pos hp] at h1
    have hy : (∃ b, ((w.1 v)[j]'hj).2 ∈ S.grid v b) ∨ ((w.1 v)[j]'hj).2 ∈ S.grid1 v := by
      rcases Finset.mem_union.1 h1 with h | h
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr h
    exact hcut _ (hnode _ hy).1
  · rw [if_neg hp] at h1
    have hy : (∃ b, ((w.1 v)[j]'hj).2 - 1 ∈ S.grid v b) ∨ ((w.1 v)[j]'hj).2 - 1 ∈ S.grid1 v := by
      rcases Finset.mem_union.1 h1 with h | h
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr h
    have := hcut _ (hnode _ hy).2.1
    simpa using this

end Formalism.FourierDecayAlt.P.CutMP
