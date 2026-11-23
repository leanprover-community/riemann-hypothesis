module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankEichlerShimuraCocyclesLeGamma1
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.finrank_z1_le_of_le_gamma1_of_finiteIndex : ∀ (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (w : ℕ), 5 ≤ N → Γ ≤ CongruenceSubgroup.Gamma1 N → Γ.FiniteIndex → FiniteDimensional ℂ (Z1 Γ w) ∧ 12 * Module.finrank ℂ (Z1 Γ w) ≤ (w + 1) * (12 + Γ.index) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.finrank_eichlerShimuraCocycles_le_Gamma1 | exact GlobalTheory.HeckeFamilyMatrices.finrank_eichlerShimuraCocycles_le_Gamma1 | (intros; apply GlobalTheory.HeckeFamilyMatrices.finrank_eichlerShimuraCocycles_le_Gamma1 <;> assumption)
