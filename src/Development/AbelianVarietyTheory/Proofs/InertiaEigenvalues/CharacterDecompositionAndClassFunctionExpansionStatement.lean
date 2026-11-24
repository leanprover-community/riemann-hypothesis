module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterDecompositionAndClassFunctionExpansion
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.character_decomposition_and_classFunction_expansion : ∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ), (IsChar χ → ∃ L : List (G → ℂ), (∀ ρ ∈ L, IsIrr ρ) ∧ χ = L.sum) ∧ (IsClass χ → χ = ∑ᶠ ρ ∈ {ρ : G → ℂ | IsIrr ρ}, ip χ ρ • ρ) ∧ (IsChar χ → IsClass χ) ∧ (IsChar χ → ip χ χ = 1 → IsIrr χ) ∧ (∀ L : List (G → ℂ), (∀ ρ ∈ L, IsChar ρ) → IsChar L.sum) := by
  first | exact @GlobalTheory.charDec | exact GlobalTheory.charDec | (intros; apply GlobalTheory.charDec <;> assumption)
