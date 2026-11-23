module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IrreducibleOfWeightLine
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

theorem _root_.GlobalTheory.T.eq_bot_or_eq_of_weight_line_generates : ∀ (p q : ℕ) (M : GKMod p q) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : M.V →ₗ[ℂ] H), Function.Injective E → (∀ Z x y, inner ℂ (E (M.act Z x)) (E y) = inner ℂ (E x) (E (M.act (adjZ Z) y))) → ∀ (S : Ix p q → Ix p q → Prop), Equivalence S → ∀ (μ : Ix p q → ℚ) (v : M.V) (U : Submodule ℂ M.V), v ∈ wtSub M.act μ → (∀ U' : Submodule ℂ M.V, v ∈ U' → (∀ a b, S a b → ∀ x ∈ U', M.act (Eab a b) x ∈ U') → U ≤ U') → (∀ x ∈ U, x ∈ wtSub M.act μ → ∃ c : ℂ, x = c • v) → ∀ N : Submodule ℂ M.V, N ≤ U → (∀ a b, S a b → ∀ x ∈ N, M.act (Eab a b) x ∈ N) → N = ⊥ ∨ N = U := by
  first | exact @GlobalTheory.FockIrr.irreducible_of_weight_line | exact GlobalTheory.FockIrr.irreducible_of_weight_line | (intros; apply GlobalTheory.FockIrr.irreducible_of_weight_line <;> assumption)
