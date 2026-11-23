module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
public import Mathlib.Analysis.Complex.Norm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralLinearPositiveNormBound
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

open GlobalTheory.IdxInt
open scoped Pointwise Classical

theorem _root_.GlobalTheory.T.indexMeasureIntegral_linear_positive_norm_bound : ∀ {W : Type} [AddCommGroup W] (A : AddSubgroup W), (∀ φ ψ : W → ℂ, Nice A φ → Nice A ψ → Nice A (φ + ψ) ∧ cint A (φ + ψ) = cint A φ + cint A ψ ∧ ((∀ w, ‖φ w‖ ≤ (ψ w).re) → ‖cint A φ‖ ≤ (cint A ψ).re)) ∧ (∀ (c : ℂ) (φ : W → ℂ), Nice A φ → Nice A (fun w => c * φ w) ∧ cint A (fun w => c * φ w) = c * cint A φ) ∧ (∀ P : W → Prop, 0 ≤ (cint A (ind P)).re ∧ (cint A (ind P)).im = 0) ∧ ∀ (ι : Type) (s : Finset ι) (φ : ι → W → ℂ), (∀ i ∈ s, Nice A (φ i)) → Nice A (fun w => ∑ i ∈ s, φ i w) ∧ cint A (fun w => ∑ i ∈ s, φ i w) = ∑ i ∈ s, cint A (φ i) := by
  first | exact @GlobalTheory.IdxInt.Lin.main | exact GlobalTheory.IdxInt.Lin.main | (intros; apply GlobalTheory.IdxInt.Lin.main <;> assumption)
