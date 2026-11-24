module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LeTwoMulOfForallScale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCurvatureDualMetricPointwiseBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram

@[expose] public section

open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

theorem _root_.GlobalTheory.T.hodgeCurvature_dual_metric_pointwise_bound : ∀ (g a : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (Bs : Fin a → Matrix (Fin g) (Fin g) ℝ) (Dm : Matrix (Fin g) (Fin g) ℂ) (s : Fin a → ℂ) (t : Fin a → ℝ) (c K : ℝ), 0 < c → 0 ≤ K → Y.IsSymm → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ i, (Bs i).PosSemidef) → (∀ i, 0 < t i) → (∀ i x, t i * (x ⬝ᵥ Bs i *ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ j k, ‖Dm j k‖ ≤ K) → (Y.map Complex.ofReal).PosDef ∧ ∀ v, ‖form (Y.map Complex.ofReal)⁻¹ ((Dm + ∑ i, s i • (Bs i).map Complex.ofReal) *ᵥ v) ((Dm + ∑ i, s i • (Bs i).map Complex.ofReal) *ᵥ v)‖ ≤ (g * K / c + ∑ i, ‖s i‖ / t i) ^ 2 * gnorm (Y.map Complex.ofReal) v ^ 2 := by
  first | exact @GlobalTheory.HodgeCurvPoint.dual_bound | exact GlobalTheory.HodgeCurvPoint.dual_bound | (intros; apply GlobalTheory.HodgeCurvPoint.dual_bound <;> assumption)
