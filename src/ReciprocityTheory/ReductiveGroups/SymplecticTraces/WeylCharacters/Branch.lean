module

public import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.AltBranchStatement
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.TR.Weyl

theorem gtChar_zero {K : Type*} [Field K] : ∀ (n : ℕ) (t : Fin n → K), gtChar n 0 t = 1
  | 0, _ => rfl
  | n + 1, t => by
    rw [gtChar]
    have h : interl (0 : Fin (n + 1) → ℤ) = {0} := by
      ext mu
      simp only [interl, Fintype.mem_piFinset, Pi.zero_apply, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · intro h; funext i; have := h i; simp only [Pi.zero_apply]; omega
      · rintro rfl i; simp
    rw [h, Finset.sum_singleton, gtChar_zero n]
    simp [wsum]

end ReciprocityTheory.ChartRestriction.TR.Weyl
