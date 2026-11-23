module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightsIntegralPullbackFormula
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ConsCompSuccAboveZero
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjSpace

@[expose] public section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

theorem _root_.GlobalTheory.T.lintegral_indicator_mul_locDens_pullback_lt_top : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {q : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {T : Type}
    [TopologicalSpace T] (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F),
    (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F)) →
    ∀ {B C : LB X} (φ : GlobalTheory.Weight q σ B) (_ : φ.IsCInf) (ψ : GlobalTheory.Weight q σ C) (_ : ψ.IsCInf)
      (g : GlobalTheory.CxPts q σ → ℝ) (S Z : Set (GlobalTheory.CxPts q σ)) {N : ℕ} (W : Fin N → X.Opens) (b : Fin N → C.ι)
      (a d : ∀ l, Γ(X, W l)),
    (∀ y : GlobalTheory.CxPts q σ, ∃ l, y ∈ ptsIn q σ (W l)) → (∀ l, W l ≤ C.U (b l)) →
    (∀ l, ∀ y ∈ ptsIn q σ (W l), y ∈ S → y ∉ Z →
      g y = Real.log ‖ev q σ (W l) (a l) y‖ - Real.log ‖ev q σ (W l) (d l) y‖ - ψ.φ (b l) y / 2) →
    IsOpen S → ContinuousOn g S → MeasurableSet Z →
    ∀ (j : Fin A.n) (K : Set (Fin D → ℂ)), K ⊆ (A.chart j).target → IsCompact K →
      ∫⁻ u in K \ (F ∘ (A.chart j).symm) ⁻¹' Z, S.indicator (fun y => ‖g y‖ₑ) (F ((A.chart j).symm u)) *
        ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u| < ⊤ := by
  exact @GlobalTheory.CompanionTheory.MixZ.lintegral_logNorm_locDens_lt_top
