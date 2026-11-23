module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlurisubharmonicDecreasingLimitExtension
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OnbPerp

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
open scoped ContDiff

theorem _root_.GlobalTheory.T.plurisubharmonic_decreasing_limit_extension : ∀ {n : ℕ} {U : Set (V n)}, IsOpen U → ∀ (e : V n → ℝ), ContDiffOn ℝ ∞ e U → (∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (e w : ℂ)) y ξ).re) → (∀ a : ℝ, IsCompact {y | y ∈ U ∧ e y ≤ a}) → ∀ (φ : ℕ → V n → ℝ), (∀ k, ContDiffOn ℝ ∞ (φ k) U) → (∀ k, ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (φ k w : ℂ)) y ξ).re) → (∀ k, ∀ y ∈ U, φ (k + 1) y ≤ φ k y) → ∀ (F0 : V n → ℂ), ContDiffOn ℝ ∞ F0 U → ∀ (h : V n → ℝ≥0∞), Measurable h → (∀ k, ∀ y ∈ U, ∀ ξ : Fin n → ℂ, ENNReal.ofReal (‖∑ j, wdb n j F0 y * (starRingEnd ℂ) (ξ j)‖ ^ 2) ≤ h y * ENNReal.ofReal (leviV n (fun w => (φ k w : ℂ)) y ξ).re) → ∀ A : ℝ≥0∞, (∀ k, ∫⁻ y in U, h y * ENNReal.ofReal (Real.exp (-φ k y)) ≤ A) → ∃ F : V n → ℂ, DifferentiableOn ℂ F U ∧ ∫⁻ y in U, ENNReal.ofReal (‖F0 y - F y‖ ^ 2) * ⨆ k, ENNReal.ofReal (Real.exp (-φ k y)) ≤ A := by
  first | exact @GlobalTheory.HormanderLimit.hormander_limit | exact GlobalTheory.HormanderLimit.hormander_limit | (intros; apply GlobalTheory.HormanderLimit.hormander_limit <;> assumption)
