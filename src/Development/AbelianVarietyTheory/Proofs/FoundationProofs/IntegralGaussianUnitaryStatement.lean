module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPosHermFormV
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralGaussianUnitary
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

open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

theorem _root_.GlobalTheory.T.integral_cexp_herm_gaussian_eq_div_det : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ a : V ≃ₗ[ℂ] V, (∀ z w, H (a z) (a w) = H z w) → LinearMap.det (1 - (a : V →ₗ[ℂ] V)) ≠ 0 → ∃ κ : ℝ, κ ≠ 0 ∧ ∀ y v : V, Integrable (fun z => cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v)) μ ∧ ∫ z, cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v) ∂μ = κ / LinearMap.det (1 - (a : V →ₗ[ℂ] V)) * cexp (π * H y v) := by
  first | exact @GlobalTheory.UnitaryTheta.integral_gaussian_unitary | exact GlobalTheory.UnitaryTheta.integral_gaussian_unitary | (intros; apply GlobalTheory.UnitaryTheta.integral_gaussian_unitary <;> assumption)
