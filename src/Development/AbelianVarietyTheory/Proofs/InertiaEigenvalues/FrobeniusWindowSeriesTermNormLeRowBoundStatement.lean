module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusWindowSeriesTermNormLeRowBound
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

open GlobalTheory.PMonE

theorem _root_.GlobalTheory.T.frobeniusWindowSeriesTerm_norm_le_rowBound : ∀ (F : Type) [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] (k : ℕ) (ϖ : F), ‖ϖ‖ = (p : ℝ)⁻¹ → ∀ lam π : Fin (k + 1) → F, (∀ j, lam j ≠ 0) → Antitone (fun j => ‖lam j‖) → (∀ i j, ‖lam i‖ < p * ‖lam j‖) → (∀ j, π j ≠ 0 ∧ ‖π j‖ < 1) → (∀ j : Fin k, ‖lam j.succ‖ * ‖π j.succ‖ ^ p ^ (j : ℕ) = ‖lam j.castSucc‖ * ‖π j.castSucc‖ ^ p ^ (j : ℕ)) → (‖lam 0‖ / p) ^ p * ‖π 0‖ = (‖lam (Fin.last k)‖ * ‖π (Fin.last k)‖ ^ p ^ k) ^ p → ∀ (r j : Fin (k + 1)) (n : ℤ), ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ ∧ (0 < n → ‖term p ϖ lam π r j n‖ < ‖lam r * π r ^ p ^ (r : ℕ)‖) ∧ (2 < |n| → ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ / p) := by
  first | exact @GlobalTheory.PMonE.WinBounds.term_le_bound | exact GlobalTheory.PMonE.WinBounds.term_le_bound | (intros; apply GlobalTheory.PMonE.WinBounds.term_le_bound <;> assumption)
