module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Choose.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Lean.Elab.MutualDef
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Defs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSuppAA

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

set_option linter.unusedSectionVars false

namespace ProjectiveBundleNumbers

theorem sum_choose_succ (n : ℕ) (U : ℕ → ℤ) :
    ∑ k ∈ Finset.range (n + 2), ((n + 1).choose k : ℤ) * U k =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * U k +
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * U (k + 1) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun k => (n.choose k : ℤ) * U k)]
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib,
    Nat.choose_zero_right]
  rw [Finset.sum_range_succ (fun k => (n.choose (k + 1) : ℤ) * U (k + 1)),
    Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
  ring

section ProjBundle

variable {K : Type*} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {F : Type*} [Field F] {Ω : Type*} [Field Ω] [Algebra F Ω]
variable {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

end ProjBundle

section Rename

variable {F : Type} [Field F] {S : Type} [Fintype S] [DecidableEq S] {κ ι' : S → Type}
  [∀ s, Fintype (κ s)] [∀ s, Fintype (ι' s)]

end Rename

end ProjectiveBundleNumbers

end

end GroundTheory.Heights₂.Heights.NumbersDVR
