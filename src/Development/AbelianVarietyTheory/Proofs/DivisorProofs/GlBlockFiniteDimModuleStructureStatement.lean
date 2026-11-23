module

public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.glBlock_finiteDim_module_structure : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsKLieAct act → ∀ W : Submodule ℂ V, FiniteDimensional ℂ W → KStable act W → (∀ v ∈ W, v ∈ ⨆ μ : Ix p q → ℚ, wtSub act μ) → (∀ U : Submodule ℂ V, U ≤ W → KStable act U → ∃ U' : Submodule ℂ V, KStable act U' ∧ U ⊓ U' = ⊥ ∧ U ⊔ U' = W) ∧ (W ≠ ⊥ → ∃ μ v, v ∈ W ∧ IsHW act μ v) ∧ (∀ v ∈ W, v ∈ ⨆ μ : Ix p q → ℚ, Submodule.span ℂ {w | w ∈ W ∧ OfType act μ w}) ∧ (∀ μ v, v ∈ W → IsHW act μ v → (∀ a b, posC a b → ∃ k : ℕ, μ a - μ b = k) ∧ OfType act μ v ∧ ∀ U : Submodule ℂ V, KStable act U → U ≤ sInf {N | v ∈ N ∧ KStable act N} → U = ⊥ ∨ v ∈ U) := by
  first | exact @GlobalTheory.BlockReps.finite_module_structure | exact GlobalTheory.BlockReps.finite_module_structure | (intros; apply GlobalTheory.BlockReps.finite_module_structure <;> assumption)
