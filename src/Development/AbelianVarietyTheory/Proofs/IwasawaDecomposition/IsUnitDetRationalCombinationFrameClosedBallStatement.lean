module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombMatAddMul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitDetRationalCombinationFrameClosedBall
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.isUnit_det_rational_combination_frame_closed_ball : ∀ (n a g r₀ r : ℕ) (ha : a ≤ n) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (c : Matrix (Fin r₀) (Fin r) ℤ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (gm dl : Matrix (Fin r₀) (Fin g) ℚ) (rk D : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < D → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → (∀ s ∈ logDom n a, ∀ i, ζ (logExp a s) i = ∑ j, c i j • lam s j) → c.map (Int.cast : ℤ → ℚ) = gm * (α * c.map (Int.cast : ℤ → ℚ)) + dl * φ → (∀ m (j : Fin g), j.val < rk → dl m j = 0) → (∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det) → (∀ i j, DifferentiableOn ℂ (fun z => τ₀ z i j) (Metric.ball 0 1)) → (∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → B k j l = 0) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 → GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s = τ₀ (logExp a s) + ∑ k, (s (Fin.castLE ha k) / (2 * Real.pi * Complex.I)) • (B k).map (Int.cast : ℤ → ℂ)) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ z) α).det := by
  first | exact @GlobalTheory.PeriodFrame.isUnit_det_combMat_on_ball | exact GlobalTheory.PeriodFrame.isUnit_det_combMat_on_ball | (intros; apply GlobalTheory.PeriodFrame.isUnit_det_combMat_on_ball <;> assumption)
