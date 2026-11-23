module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotypicTraceEqOfOneDoubleCoset
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass

@[expose] public section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem _root_.GlobalTheory.T.isotypic_trace_eq_of_one_double_coset : ∀ (G : Type) [Group G] [Fintype G] (H H₁ H₂ : Subgroup G) (l₁ : H₁ →* ℂˣ) (l₂ : H₂ →* ℂˣ), H₁ ≤ H → H₂ ≤ H → Nat.card H₁ = Nat.card H₂ → (∀ (a : H₁) (b : H₂), (a : G) = b → l₁ a = l₂ b) → (∀ h ∈ H, h ∉ H₁ → ∃ a a' : H₁, (a' : G) = h⁻¹ * a * h ∧ l₁ a' ≠ l₁ a) → (∀ h ∈ H, h ∉ H₂ → ∃ b b' : H₂, (b' : G) = h⁻¹ * b * h ∧ l₂ b' ≠ l₂ b) → ∀ φ : G → ℂ, IsClass φ → (Nat.card H₁ : ℂ)⁻¹ * ∑ a : H₁, ((l₁ a)⁻¹ : ℂˣ) * φ a = (Nat.card H₂ : ℂ)⁻¹ * ∑ b : H₂, ((l₂ b)⁻¹ : ℂˣ) * φ b := by
  first | exact @GlobalTheory.GLm.OneDoubleCoset.isotypic_trace_eq | exact GlobalTheory.GLm.OneDoubleCoset.isotypic_trace_eq | (intros; apply GlobalTheory.GLm.OneDoubleCoset.isotypic_trace_eq <;> assumption)
