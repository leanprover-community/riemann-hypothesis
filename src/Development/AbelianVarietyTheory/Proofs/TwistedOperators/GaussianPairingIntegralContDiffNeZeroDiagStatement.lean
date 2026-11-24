module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianPairingIntegralContDiffNeZeroDiag
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

open MeasureTheory

theorem _root_.GlobalTheory.T.gaussianPairingIntegral_contDiff_ne_zero_diag : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ),
    (∀ x y, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => M t x y) →
    (∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2)) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => ∫ x, Complex.exp (M p.1 x x) * starRingEnd ℂ (Complex.exp (M p.2 x x)) ∂μ) ∧
    ∀ u, ∫ x, Complex.exp (M u x x) * starRingEnd ℂ (Complex.exp (M u x x)) ∂μ ≠ 0 := by
  first | exact @GlobalTheory.GaussPairing.gauss_pairing_smooth_ne_zero | exact GlobalTheory.GaussPairing.gauss_pairing_smooth_ne_zero | (intros; apply GlobalTheory.GaussPairing.gauss_pairing_smooth_ne_zero <;> assumption)
