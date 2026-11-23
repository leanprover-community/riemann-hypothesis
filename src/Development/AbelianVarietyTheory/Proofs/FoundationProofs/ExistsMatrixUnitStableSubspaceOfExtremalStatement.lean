module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMatrixUnitStableSubspaceOfExtremal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData

@[expose] public section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_matrixUnit_stable_subspace_of_extremal : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (S : Ix p q → Ix p q → Prop), Equivalence S → ∀ (r : Ix p q → ℕ), Function.Injective r → ∀ (μ : Ix p q → ℚ) (v : V), v ∈ wtSub act μ → (∀ a b, S a b → r a < r b → act (Eab a b) v = 0) → ∃ U : Submodule ℂ V, v ∈ U ∧ (∀ a b, S a b → ∀ x ∈ U, act (Eab a b) x ∈ U) ∧ (∀ U' : Submodule ℂ V, v ∈ U' → (∀ a b, S a b → r a < r b → ∀ x ∈ U', act (Eab b a) x ∈ U') → U ≤ U') ∧ (∀ x ∈ U, x ∈ wtSub act μ → ∃ c : ℂ, x = c • v) ∧ ∀ (ν : Ix p q → ℚ), ∀ x ∈ U, x ≠ 0 → x ∈ wtSub act ν → ν = μ ∨ ∑ a, (r a : ℚ) * μ a < ∑ a, (r a : ℚ) * ν a := by
  first | exact @GlobalTheory.ExtremalGen.exists_generated | exact GlobalTheory.ExtremalGen.exists_generated | (intros; apply GlobalTheory.ExtremalGen.exists_generated <;> assumption)
