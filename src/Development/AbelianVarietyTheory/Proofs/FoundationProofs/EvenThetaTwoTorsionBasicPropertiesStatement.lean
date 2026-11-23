module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaTwoTorsionBasicProperties
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.th0_zero_even_sq_zeros_and_periodicity : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → Differentiable ℂ (GL3Theta.th0 Λ t₀) ∧ GL3Theta.th0 Λ t₀ 0 = 1 ∧ (∀ z, GL3Theta.th0 Λ t₀ (-z) = GL3Theta.th0 Λ t₀ z) ∧ (∀ z, GL3Theta.th0 Λ t₀ z ^ 2 = sqTh Λ t₀ z) ∧ (∀ z, GL3Theta.th0 Λ t₀ z = 0 ↔ z + t₀ ∈ Λ) ∧ ∀ ω ∈ Λ, ω / 2 + t₀ ∉ Λ → ∀ z, U1 Λ ω (GL3Theta.th0 Λ t₀) z = GL3Theta.th0 Λ t₀ z := by
  first | exact @GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties | exact GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties | (intros; apply GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties <;> assumption)
