module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FlipTwoThree
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

theorem UpperTheory.V.Pr.globProp :
    UpperTheory.V.Pr.GlobProp := by
  intro X _ _ M hM
  classical
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)
  have key : ∀ Y, M.CompI Y → Y ⊆ M.Good := by
    by_contra hne
    push_neg at hne
    obtain ⟨Yb, hYb, hYbn⟩ := hne
    set G : Set X := ⋃ Y ∈ {Y | M.CompI Y ∧ Y ⊆ M.Good}, Y with hG
    set B : Set X := ⋃ Y ∈ {Y | M.CompI Y ∧ ¬ Y ⊆ M.Good}, Y with hB
    have hGc : IsClosed G :=
      (hfin.subset (t := {Y | M.CompI Y ∧ Y ⊆ M.Good}) (fun Y hY => hY.1.1)).isClosed_biUnion
        (fun Y hY => isClosed_of_mem_irreducibleComponents Y hY.1.1)
    have hBc : IsClosed B :=
      (hfin.subset (t := {Y | M.CompI Y ∧ ¬ Y ⊆ M.Good}) (fun Y hY => hY.1.1)).isClosed_biUnion
        (fun Y hY => isClosed_of_mem_irreducibleComponents Y hY.1.1)
    have hcov : M.Core ⊆ G ∪ B := by
      intro x hx
      have h1 : x ∈ closure (M.Cl \ M.EE) := hM.dense hx
      have h2 : M.Cl \ M.EE ⊆ G ∪ B := by
        intro y hy
        obtain ⟨Y, hY, hyY⟩ := hM.off y hy
        by_cases hg : Y ⊆ M.Good
        · exact Or.inl (Set.mem_biUnion (show Y ∈ {Y | M.CompI Y ∧ Y ⊆ M.Good} from ⟨hY, hg⟩) hyY)
        · exact Or.inr (Set.mem_biUnion (show Y ∈ {Y | M.CompI Y ∧ ¬ Y ⊆ M.Good} from ⟨hY, hg⟩) hyY)
      exact (hGc.union hBc).closure_subset_iff.mpr h2 h1
    obtain ⟨Ys, hYs, hYsg⟩ := hM.seed
    have hG' : (M.Core ∩ G).Nonempty := by
      obtain ⟨x, hxY, hxC⟩ := hM.meets Ys hYs
      exact ⟨x, hxC, Set.mem_biUnion (show Ys ∈ {Y | M.CompI Y ∧ Y ⊆ M.Good} from ⟨hYs, hYsg⟩) hxY⟩
    have hB' : (M.Core ∩ B).Nonempty := by
      obtain ⟨x, hxY, hxC⟩ := hM.meets Yb hYb
      exact ⟨x, hxC, Set.mem_biUnion (show Yb ∈ {Y | M.CompI Y ∧ ¬ Y ⊆ M.Good} from ⟨hYb, hYbn⟩) hxY⟩
    obtain ⟨x, hxC, hxG, hxB⟩ := isPreconnected_closed_iff.mp hM.conn G B hGc hBc hcov hG' hB'
    obtain ⟨z, hzGB, hzCl⟩ := hM.jac (G ∩ B) (hGc.inter hBc) ⟨x, ⟨hxG, hxB⟩, hxC⟩
    rw [hG, hB] at hzGB
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hzGB
    obtain ⟨⟨Y, ⟨hY, hYg⟩, hzY⟩, ⟨Y', ⟨hY', hY'n⟩, hzY'⟩⟩ := hzGB
    exact hY'n (hM.loc z hzCl Y Y' hY hY' hzY hzY' hYg)
  intro x hx
  exact key (irreducibleComponent x)
    ⟨irreducibleComponent_mem_irreducibleComponents x, ⟨x, mem_irreducibleComponent, hx⟩⟩
    mem_irreducibleComponent
