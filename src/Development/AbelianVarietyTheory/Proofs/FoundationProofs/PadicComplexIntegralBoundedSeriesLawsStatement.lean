module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicComplexIntegralBoundedSeriesLaws
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.padicComplex_integral_bounded_series_laws : ∀ (p : ℕ) [Fact p.Prime], (∀ f g : PowerSeries ℂ_[p], IntSer f → IntSer g → IntSer (f + g) ∧ IntSer (f - g) ∧ IntSer (f * g)) ∧ (∀ f g : PowerSeries ℂ_[p], BddSer f → BddSer g → BddSer (f + g) ∧ BddSer (f - g) ∧ BddSer (f * g)) ∧ (∀ c : ℂ_[p], BddSer (PowerSeries.C c) ∧ (‖c‖ ≤ 1 → IntSer (PowerSeries.C c))) ∧ IntSer (PowerSeries.X : PowerSeries ℂ_[p]) ∧ (∀ f : PowerSeries ℂ_[p], IntSer f → ‖PowerSeries.constantCoeff f‖ = 1 → IntSer f⁻¹) ∧ (∀ (f h : PowerSeries ℂ_[p]) (B : ℝ), (∀ n, ‖PowerSeries.coeff n f‖ ≤ B) → IntSer h → PowerSeries.constantCoeff h = 0 → ∀ n, ‖PowerSeries.coeff n (PowerSeries.subst h f : PowerSeries ℂ_[p])‖ ≤ B) ∧ ∀ (f g : PowerSeries ℂ_[p]) (A B : ℝ), (∀ n, ‖PowerSeries.coeff n f‖ ≤ A) → (∀ n, ‖PowerSeries.coeff n g‖ ≤ B) → ∀ n, ‖PowerSeries.coeff n (f * g)‖ ≤ A * B := by
  first | exact @GlobalTheory.EvenTheta.SerRing.series_ring_laws | exact GlobalTheory.EvenTheta.SerRing.series_ring_laws | (intros; apply GlobalTheory.EvenTheta.SerRing.series_ring_laws <;> assumption)
