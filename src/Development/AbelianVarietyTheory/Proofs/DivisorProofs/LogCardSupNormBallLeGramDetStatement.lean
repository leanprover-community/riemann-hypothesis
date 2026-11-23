module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardSupNormBallLeGramDet
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.abs_log_card_ballIn_sub_gramVolume_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p) (ω : ∀ σ, VolDens p σ D) (a b : ℤ) (r : ℕ) (f : Fin r → X.functionField), (∀ i, f i ∈ P.H a b) → LinearIndependent ℤ f → ∀ (M Vv ρ R : ℝ), 1 ≤ M → 1 ≤ Vv → (∑ᶠ σ, ((ω σ).meas Set.univ).toReal) ≤ Vv → 0 ≤ ρ → 0 < R → (∀ (c : Fin r → ℂ) σ y, cmb (vals P a b f) c σ y ≤ M * l2 (fun σ => (ω σ).meas) (vals P a b f) c) → AddSubgroup.closure (Set.range f) ≤ AddSubgroup.closure (ballIn P (AddSubgroup.closure (Set.range f)) a b ρ) → 2 * r * ρ * (M * Vv) ≤ R → |Real.log ((ballIn P (AddSubgroup.closure (Set.range f)) a b R).ncard : ℝ) - (r * Real.log R - Real.log (gram (fun σ => (ω σ).meas) (vals P a b f)).det.re / 2 + Real.log (volume {x : Fin r → ℝ | ∑ i, x i ^ 2 ≤ 1}).toReal)| ≤ 2 * r * Real.log (2 * (M * Vv)) := by
  first | exact @GlobalTheory.BallGram.count_ball_gram | exact GlobalTheory.BallGram.count_ball_gram | (intros; apply GlobalTheory.BallGram.count_ball_gram <;> assumption)
