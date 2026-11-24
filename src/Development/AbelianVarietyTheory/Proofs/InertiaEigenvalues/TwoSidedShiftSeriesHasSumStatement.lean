module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoSidedShiftSeriesHasSum
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial

theorem _root_.GlobalTheory.T.twoSided_shift_series_hasSum : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] [IsAdicComplete (Ideal.span {(l : A)}) A] (φ : A →+* A) (h : ℕ) (c : ℤ → A), (∀ n : ℤ, (l : A) ^ n.natAbs ∣ c n) → (∀ n : ℤ, φ^[h] (c n) = (l : A) * c (n + 1)) → ∃ w : A, φ^[h] w = (l : A) * w ∧ ∀ Θ : A →+* ℂ_[l], (∀ a, ‖Θ a‖ ≤ 1) → HasSum (fun n : ℤ => Θ (c n)) (Θ w) := by
  first | exact @GlobalTheory.twoSided_shift_series | exact GlobalTheory.twoSided_shift_series | (intros; apply GlobalTheory.twoSided_shift_series <;> assumption)
