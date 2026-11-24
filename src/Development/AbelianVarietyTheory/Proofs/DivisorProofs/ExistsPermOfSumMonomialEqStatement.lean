module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermOfSumMonomialEq
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Mathlib.Geometry.Manifold.StructureGroupoid
import Mathlib.NumberTheory.ModularForms.SlashActions

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

theorem _root_.GlobalTheory.T.exists_perm_of_sum_monomial_eq' : ∀ (ι S : Type) [Fintype ι] [Fintype S] (x y : ι → S → ℂ), (∀ μ : S → ℕ, ∑ i, ∏ s, x i s ^ μ s = ∑ i, ∏ s, y i s ^ μ s) → ∃ ρ : Equiv.Perm ι, ∀ i, x i = y (ρ i) := by
  first | exact @GlobalTheory.QFam.exists_perm_of_sum_monomial_eq | exact GlobalTheory.QFam.exists_perm_of_sum_monomial_eq | (intros; apply GlobalTheory.QFam.exists_perm_of_sum_monomial_eq <;> assumption)
