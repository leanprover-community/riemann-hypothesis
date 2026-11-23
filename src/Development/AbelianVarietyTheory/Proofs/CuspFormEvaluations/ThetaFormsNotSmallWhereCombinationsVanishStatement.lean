module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaFormsNotSmallWhereCombinationsVanish
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

theorem _root_.GlobalTheory.T.theta_forms_not_small_where_combinations_vanish : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (K : Type) [Field K] (σ : K →+* ℂ) (t : Fin (nd X + 1) × Fin Xa.N → ℂ), (∀ Q : MvPolynomial (Fin (nd X + 1) × Fin Xa.N) K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0) → RelIn σ X Xa → let sf : Fin (nd X + 1) → Frame X.Ψ r → ℂ := fun i x => ∑ j, t (i, j) * Xa.w j x; ∃ ε c0 : ℝ, 0 < ε ∧ 0 < c0 ∧ ∀ x ∈ X.dom, ∑ i : Fin (nd X), ‖sf i.succ x‖ ^ 2 < ε * ‖sf 0 x‖ ^ 2 → c0 ≤ ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := by
  first | exact @GlobalTheory.Shares.Low.forms_not_small | exact GlobalTheory.Shares.Low.forms_not_small | (intros; apply GlobalTheory.Shares.Low.forms_not_small <;> assumption)
