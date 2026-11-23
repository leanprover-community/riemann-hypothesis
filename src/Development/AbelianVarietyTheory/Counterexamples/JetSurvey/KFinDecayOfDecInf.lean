module

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.BesselNonvanishingReduction

@[expose] public section

open Formalism.FourierDecayAlt.ThreeDimData

namespace GlobalTheory.GapSizeCheck

theorem decay_range (k r : ℕ) (h : ℝ) (h120 : 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 ≤ h) :
    120 * ((2 * r + k + 1 : ℕ) : ℝ) * (((r : ℝ) + 1) * Real.sqrt ((r : ℝ) + 1)) ≤ h := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hs : Real.sqrt ((r : ℝ) + 1) ≤ (r : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hn
  have hn1 : (r : ℝ) + 1 ≤ n := by rw [hn]; push_cast; linarith
  have : ((r : ℝ) + 1) * Real.sqrt ((r : ℝ) + 1) ≤ n * n :=
    mul_le_mul hn1 (hs.trans hn1) (Real.sqrt_nonneg _) (by linarith)
  nlinarith



end GlobalTheory.GapSizeCheck
