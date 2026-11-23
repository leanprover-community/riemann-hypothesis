module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
public import Mathlib.NumberTheory.ModularForms.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerPeriodCocycleMemCocyclesAndEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.eichlerPeriodCocycle_mem_cocycles_and_eq : ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 2 ≤ k → ∀ f : ModularForm Γ (k : ℤ), per Γ (k - 2) ⇑f ∈ Z1 Γ (k - 2) ∧ ∀ (γ : Γ) (τ : ℍ), per Γ (k - 2) ⇑f γ = slP (k - 2) (mat γ) (eichler (k - 2) ⇑f ((γ : SL(2, ℤ)) • τ)) - eichler (k - 2) ⇑f τ := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.PerCoc.per_mem_Z1_and_eq_slP_eichler_sub | exact GlobalTheory.HeckeFamilyMatrices.PerCoc.per_mem_Z1_and_eq_slP_eichler_sub | (intros; apply GlobalTheory.HeckeFamilyMatrices.PerCoc.per_mem_Z1_and_eq_slP_eichler_sub <;> assumption)
