module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroOnSubsetApplyCoe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedEstimateRhsLeManifold
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

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.twistedEstimate_rhs_le_manifold : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ) (U : Set Y) (z : Y → V n) (β h : ι → Y → ℂ), IsOpen U → (∀ (a : Y → ℂ) (w : Y → ℝ), Measurable a → Measurable w → (∀ y ∈ U, 0 ≤ w y) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) β y * ‖a y‖ ^ 2 * w y) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖a x‖ ^ 2 * (w x * Real.exp (-GlobalTheory.OTY.TwEst.wt A E β z x))) ∂vol n (fun y : U => z y)) → (∀ y ∈ U, h (A.pick y) y = β (A.pick y) y * GlobalTheory.OTY.TwEst.quot A h β y) → Measurable (GlobalTheory.OTY.TwEst.ext0 U (fun y : U => GlobalTheory.OTY.TwEst.quot A h β y)) → Measurable (psi A L s) → ∀ δ T : ℝ, ∫⁻ x in {x : U | -T - 1 ≤ δ * psi A L s x ∧ δ * psi A L s x ≤ -T + 1}, ENNReal.ofReal (‖GlobalTheory.OTY.TwEst.quot A h β x‖ ^ 2 * Real.exp (-(GlobalTheory.OTY.TwEst.wt A E β z x + psi A L s x))) ∂vol n (fun y : U => z y) ≤ ∫⁻ y in {y | -T - 1 ≤ δ * psi A L s y ∧ δ * psi A L s y ≤ -T + 1}, ENNReal.ofReal (A.nsq (A.kap + E) h y * Real.exp (-psi A L s y)) ∂A.mu := by
  first | exact @GlobalTheory.OTY.TwEst.rhs_le_manifold | exact GlobalTheory.OTY.TwEst.rhs_le_manifold | (intros; apply GlobalTheory.OTY.TwEst.rhs_le_manifold <;> assumption)
