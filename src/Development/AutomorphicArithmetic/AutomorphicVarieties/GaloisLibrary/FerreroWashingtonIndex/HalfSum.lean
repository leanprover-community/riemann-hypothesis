module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle

@[expose] public section

open UpperTheory.V.FW

theorem UpperTheory.V.FW.halfSum :
    ∀ (α k : Type) [AddCommMonoid k] (σ : α → α) (H H' : Finset α) (g : α → k), (∀ x, σ (σ x) = x) → (∀ x, g (σ x) = g x) → (∀ x ∈ H, σ x ∉ H) → (∀ x ∈ H', σ x ∉ H') → (∀ x ∈ H, x ∈ H' ∨ σ x ∈ H') → (∀ x ∈ H', x ∈ H ∨ σ x ∈ H) → ∑ x ∈ H, g x = ∑ x ∈ H', g x := by
  classical
  intro α k _ σ H H' g hσ hg hH hH' hHH' hH'H
  refine Finset.sum_bij' (fun x _ => if x ∈ H' then x else σ x) (fun y _ => if y ∈ H then y else σ y)
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    by_cases h : x ∈ H'
    · simp [h]
    · simp only [h, if_false]
      exact (hHH' x hx).resolve_left h
  · intro y hy
    by_cases h : y ∈ H
    · simp [h]
    · simp only [h, if_false]
      exact (hH'H y hy).resolve_left h
  · intro x hx
    by_cases h : x ∈ H'
    · simp [h, hx]
    · simp [h, hH x hx, hσ]
  · intro y hy
    by_cases h : y ∈ H
    · simp [h, hy]
    · simp [h, hH' y hy, hσ]
  · intro x hx
    by_cases h : x ∈ H'
    · simp [h]
    · simp [h, hg]
