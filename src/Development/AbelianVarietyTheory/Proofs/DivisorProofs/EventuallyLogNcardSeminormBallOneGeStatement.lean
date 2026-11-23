module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLogNcardSeminormBallOneGe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open Filter Topology GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.eventually_log_ncard_seminormBall_one_ge : ∀ (G : Type) [AddCommGroup G] (Λ : ℕ → AddSubgroup G) (B : ℕ → ℝ → Set G) (d : ℕ), 0 < d → (∀ m, IsBallFam (Λ m) (B m)) → (∀ m R, (B m R).Finite) → ∀ α β t₀ : ℝ, (∀ t, t₀ ≤ t → Tendsto (fun m : ℕ => Real.log ((B m (Real.exp (t * m))).ncard : ℝ) / (m : ℝ) ^ d) atTop (𝓝 (α + β * t))) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (α - ε) * (m : ℝ) ^ d ≤ Real.log ((B m 1).ncard : ℝ) := by
  first | exact @GlobalTheory.VolBr.log_ncard_ball_one_eventually_ge | exact GlobalTheory.VolBr.log_ncard_ball_one_eventually_ge | (intros; apply GlobalTheory.VolBr.log_ncard_ball_one_eventually_ge <;> assumption)
