module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeNumericalBoundsCollect
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

open Real

theorem _root_.GlobalTheory.T.covolume_numerical_bounds_collect : ∀ (CG CB f r Lb S N0 sz c₁ q ℓ lb dd : ℝ), 0 ≤ CG → 0 ≤ CB → 1 ≤ f → 1 ≤ r → 1 ≤ Lb → 0 ≤ S → 0 ≤ q → q ≤ r → 0 ≤ ℓ → ℓ ≤ 3 * Lb → |c₁| ≤ 9 * r * Lb → 0 ≤ N0 → N0 ≤ S + f * (4 * (f * r + 1) + 1) → 0 ≤ sz → sz ≤ (1 + r) * S + r * f * (4 * (f * r + 1) + 1) → lb ≤ CB * (f * r * Lb) ^ 2 → dd ≤ 391 / 2 * (f * r * Lb) ^ 2 → (f * r + 1) * (2 * (f * r) * Real.log (2 * Real.pi)) + ((|c₁| + q * ℓ) * N0 + lb + dd + 1) + CG * (f * r * Lb) ^ 2 * sz ≤ (11 * CG + CB + 500) * ((f * r * Lb) ^ 3 * S + (f * r * Lb) ^ 5) := by
  first | exact @GlobalTheory.covol_numerical_collect | exact GlobalTheory.covol_numerical_collect | (intros; apply GlobalTheory.covol_numerical_collect <;> assumption)
