module

public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormCutoffLogWeightLowerBound
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.CoeffMatrixZeroCorrectedLineGramPoly
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainTranslate

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

theorem _root_.GlobalTheory.T.leviForm_cutoffLogWeight_lower_bound : ∀ (χ : ℝ → ℝ) (A : ℝ), ContDiff ℝ ∞ χ → (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) → (∀ t, t ≤ 1 / 4 → χ t = 1) → (∀ t, 1 ≤ t → χ t = 0) → (∀ t, |deriv χ t| ≤ A) → (∀ t, |deriv (deriv χ) t| ≤ A) → ∀ (n : ℕ) (ρ δ : ℝ), 0 < ρ → 0 < δ → δ ≤ 1 → ∀ (z : V n) (ξ : Fin n → ℂ), -((13 * A + 20) / ρ ^ 2 * ∑ j, ‖ξ j‖ ^ 2) ≤ (leviV n (fun w => ((χ (‖w‖ ^ 2 / ρ ^ 2) * Real.log ((‖w‖ ^ 2 / ρ ^ 2 + δ) / 2) : ℝ) : ℂ)) z ξ).re := by
  first | exact @GlobalTheory.PeakWeightLevi.levi_cutLog_lower | exact GlobalTheory.PeakWeightLevi.levi_cutLog_lower | (intros; apply GlobalTheory.PeakWeightLevi.levi_cutLog_lower <;> assumption)
