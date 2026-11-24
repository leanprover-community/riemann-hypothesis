module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogThetaWeightSizeLe
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

open Real

theorem _root_.GlobalTheory.T.log_le_twenty_mul_of_bounds : ∀ (f r Lb S sz : ℝ), 1 ≤ f → 1 ≤ r → 1 ≤ Lb → Real.log (f * r) ≤ Lb → (∃ N : ℕ, S = N) → Real.log S ≤ 10 * Lb → 0 ≤ sz → sz ≤ (1 + r) * S + r * f * (4 * (f * r + 1) + 1) → Real.log sz ≤ 20 * Lb := by
  first | exact @GlobalTheory.log_theta_weight_size_le | exact GlobalTheory.log_theta_weight_size_le | (intros; apply GlobalTheory.log_theta_weight_size_le <;> assumption)
