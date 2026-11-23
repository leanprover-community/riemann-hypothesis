module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsReversedTriangularFrameChange
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

open Matrix

theorem _root_.GlobalTheory.T.exists_reversed_triangular_frame_change : ∀ (Φ : Type) [Field Φ] (R : Subring Φ) (r : ℕ) (u T U Rm Rm' : Matrix (Fin r) (Fin r) Φ), IsUnit u.det → IsUnit T.det → U.BlockTriangular id → (∀ l, U l l ≠ 0) → (∀ a b, Rm a b ∈ R) → (∀ a b, Rm' a b ∈ R) → Rm * Rm' = 1 → (Matrix.of fun a b => uᵀ⁻¹ a (Fin.rev b)) * U = Tᵀ⁻¹ * Rm → ∃ U₂ R₂ R₂' : Matrix (Fin r) (Fin r) Φ, U₂.BlockTriangular id ∧ (∀ l, U₂ l l = (U l.rev l.rev)⁻¹) ∧ (∀ a b, R₂ a b ∈ R) ∧ (∀ a b, R₂' a b ∈ R) ∧ R₂ * R₂' = 1 ∧ u * U₂ = T * R₂ := by
  first | exact @GlobalTheory.CompanionTheory.AdaptedFrame.reversed_dual_frame | exact GlobalTheory.CompanionTheory.AdaptedFrame.reversed_dual_frame | (intros; apply GlobalTheory.CompanionTheory.AdaptedFrame.reversed_dual_frame <;> assumption)
