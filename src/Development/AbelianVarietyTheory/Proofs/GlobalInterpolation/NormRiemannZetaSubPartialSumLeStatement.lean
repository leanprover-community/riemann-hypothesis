module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormRiemannZetaSubPartialSumLe
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

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.norm_riemannZeta_sub_partial_sum_le : ∀ s : ℂ, 0 < s.re → s ≠ 1 → ∀ M : ℕ, 1 ≤ M → ‖riemannZeta s - ∑ n ∈ Finset.Icc 1 M, (n : ℂ) ^ (-s) - (M : ℂ) ^ (1 - s) / (s - 1)‖ ≤ ‖s‖ / s.re * (M : ℝ) ^ (-s.re) := by
  first | exact @GlobalTheory.ZetaPartialSum.norm_zeta_sub_sum_le | exact GlobalTheory.ZetaPartialSum.norm_zeta_sub_sum_le | (intros; apply GlobalTheory.ZetaPartialSum.norm_zeta_sub_sum_le <;> assumption)
