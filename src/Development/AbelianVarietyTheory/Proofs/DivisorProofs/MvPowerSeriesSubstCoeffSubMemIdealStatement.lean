module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesSubstCoeffSubMemIdeal
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

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

theorem _root_.GlobalTheory.T.mvPowerSeries_subst_coeff_sub_mem_ideal : ∀ {B Q σ τ : Type} [CommRing B] [CommRing Q] [Algebra B Q] [Fintype σ] (N : Ideal B) (u ℓ : σ → MvPowerSeries τ B), (∀ s, constantCoeff (u s) = 0) → (∀ s (β : τ →₀ ℕ), β.degree ≤ 1 → coeff β (u s) = coeff β (ℓ s)) → ∀ (m : ℕ) (c : MvPowerSeries σ Q), (∀ α : σ →₀ ℕ, α.degree < m → ∃ b ∈ N, coeff α c = algebraMap B Q b) → ∀ (w : τ →₀ ℕ), w.degree = m → ∃ r ∈ N, coeff w (subst (up Q u) c) - coeff w (subst (up Q ℓ) c) = algebraMap B Q r := by
  first | exact @GlobalTheory.SubstMod.subst_coeff_sub_mem | exact GlobalTheory.SubstMod.subst_coeff_sub_mem | (intros; apply GlobalTheory.SubstMod.subst_coeff_sub_mem <;> assumption)
