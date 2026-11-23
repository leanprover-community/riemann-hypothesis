module

public import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormCoeffIntegralPowerSeriesLeProdZeros
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

open GlobalTheory.ConvSer

theorem _root_.GlobalTheory.T.norm_coeff_integral_powerSeries_le_prod_zeros : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (h : PowerSeries K) (S : Finset K), Intg h → (∀ x ∈ S, ‖x‖ < 1 ∧ ev1 h x = 0) → (∀ r : ℝ, 0 < r → r ≤ 1 → (∀ x ∈ S, r ≤ ‖x‖) → ∀ k, ‖PowerSeries.coeff k h‖ * r ^ k ≤ ∏ x ∈ S, ‖x‖) ∧ (‖PowerSeries.coeff S.card h‖ = 1 → (∀ k < S.card, ‖PowerSeries.coeff k h‖ < 1) → ∏ x ∈ S, ‖x‖ = ‖PowerSeries.coeff 0 h‖) := by
  first | exact @GlobalTheory.ConvSer.norm_coeff_le_prod_zeros | exact GlobalTheory.ConvSer.norm_coeff_le_prod_zeros | (intros; apply GlobalTheory.ConvSer.norm_coeff_le_prod_zeros <;> assumption)
