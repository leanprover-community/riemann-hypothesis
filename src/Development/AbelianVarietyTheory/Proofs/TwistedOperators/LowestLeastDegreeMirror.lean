module

public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegWBlattnerLeOfBlattnerConeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockInUnitarySStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitaryStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

namespace GlobalTheory.LeastDegree

theorem lamA_ne_zero {t : ℕ} {al be ga de : List ℚ} (h : HypA t al be ga de)
    (a : Ix (al.length + be.length) (ga.length + de.length)) : lamA al be ga de a ≠ 0 := by
  obtain ⟨ht, -, -, -, -, -, -, -, -, -, habs⟩ := h
  have key : ∀ e ∈ al ++ be ++ ga ++ de, e ≠ 0 := by
    intro e he h0
    have hle := habs e he
    rw [h0, abs_zero] at hle
    have ht' : (1 : ℚ) ≤ t := by exact_mod_cast ht
    linarith
  rcases a with ⟨i, hi⟩ | ⟨j, hj⟩
  · have hi' : i < (al ++ be).length := by simpa using hi
    have hm : (al ++ be)[i] ∈ al ++ be := List.getElem_mem hi'
    simp only [lamA, ofBlocks, List.getD_eq_getElem _ _ hi']
    apply key
    simp only [List.mem_append] at hm ⊢
    tauto
  · have hj' : j < (ga ++ de).length := by simpa using hj
    have hm : (ga ++ de)[j] ∈ ga ++ de := List.getElem_mem hj'
    simp only [lamA, ofBlocks, List.getD_eq_getElem _ _ hj']
    apply key
    simp only [List.mem_append] at hm ⊢
    tauto

theorem coneTypes_ds (X : ProvA) (hX : DiscreteSeriesBlattner X) {p q : ℕ} {lam : Ix p q → ℚ}
    (h : IsParam lam) : ConeTypes (X.ds p q lam).HK lam := by
  intro μ v hv
  exact (hX p q lam h).2.2 μ v hv

theorem lowest_least_degree : ∀ X : ProvA, DiscreteSeriesBlattner X → ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → (∀ μ v, IsHW (X.ds _ _ (lamA al be ga de)).HK.act μ v → degW (cPair (al.length + de.length + t) (ga.length + be.length)) (blattner (lamA al be ga de)) ≤ degW (cPair (al.length + de.length + t) (ga.length + be.length)) μ) ∧ (∀ μ v, IsHW (X.ds _ _ (lamA' t al be ga de)).HK.act μ v → degW (cPair (al.length + be.length) (ga.length + de.length)) (blattner (lamA' t al be ga de)) ≤ degW (cPair (al.length + be.length) (ga.length + de.length)) μ) := by
  intro X hX t al be ga de hA
  obtain ⟨-, hP, hP', hs, hs'⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hA
  refine ⟨?_, ?_⟩
  · refine GlobalTheory.T.degW_blattner_le_of_blattnerCone _ _ _ _ _ 0 (coneTypes_ds X hX hP) ?_
    intro a
    refine ⟨(hs a).1, fun hle => (hs a).2 ?_⟩
    exact lt_of_le_of_ne hle (lamA_ne_zero hA a)
  · exact GlobalTheory.T.degW_blattner_le_of_blattnerCone _ _ _ _ _ ((t : ℚ) / 2) (coneTypes_ds X hX hP') hs'

theorem lowest_least_degree_mirror : ∀ X : ProvA, DiscreteSeriesBlattner X → ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → (∀ μ v, IsHW (X.ds _ _ (lamA al be ga de)).HK.act μ v → degW (cPair (al.length + de.length) (ga.length + be.length + t)) (blattner (lamA al be ga de)) ≤ degW (cPair (al.length + de.length) (ga.length + be.length + t)) μ) ∧ (∀ μ v, IsHW (X.ds _ _ (lamM' t al be ga de)).HK.act μ v → degW (cPair (al.length + be.length) (ga.length + de.length)) (blattner (lamM' t al be ga de)) ≤ degW (cPair (al.length + be.length) (ga.length + de.length)) μ) := by
  intro X hX t al be ga de hA
  obtain ⟨-, hP, -, -, -⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hA
  obtain ⟨-, hM, hs, hs'⟩ := GlobalTheory.T.lowestKTypes_jointShape_block_in_unitaryS t al be ga de hA
  refine ⟨?_, ?_⟩
  · refine GlobalTheory.T.degW_blattner_le_of_blattnerCone _ _ _ _ _ 0 (coneTypes_ds X hX hP) ?_
    intro a
    refine ⟨(hs a).1, fun hle => (hs a).2 ?_⟩
    exact lt_of_le_of_ne hle (lamA_ne_zero hA a)
  · exact GlobalTheory.T.degW_blattner_le_of_blattnerCone _ _ _ _ _ ((t : ℚ) / 2) (coneTypes_ds X hX hM) hs'

end GlobalTheory.LeastDegree
