module

public import Formalism.LandauZeroFreeBounds.NoZeroComplexOf
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.EulerFactorLogDerivBound
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ZetaLogDerivLandauBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem trivial_log_deriv_bound : TrivLogDeriv := by
  obtain ⟨K, hK0, hK⟩ := zeta_neg_log_deriv_re_bound
  refine ⟨K + 1, fun q _ σ t hσ hσ2 => ?_⟩
  have hs : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  have h1 := re_negLogDeriv_le q ((σ : ℂ) + t * I) hs
  have h2 := hK σ t hσ hσ2
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq
  have hT : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hlog : Real.log ((q : ℝ) * (|t| + 2)) = Real.log q + Real.log (|t| + 2) :=
    Real.log_mul (by linarith : (0 : ℝ) < q).ne' (by linarith [abs_nonneg t] : (0 : ℝ) < |t| + 2).ne'
  rw [hlog]
  nlinarith [mul_nonneg hK0 hlq]

end Formalism.ZeroFreeDirichlet
