module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaSumShift
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.theta_sum_shift_eq_single_mul_fSum : ∀ (O : Type) [CommRing O] [StarRing O] (A : AnArc O), ∀ (k : ℕ) [NeZero k] (la : A.La), (∀ α, (k : ℤ) ∣ A.be la.y α) → ∃ cz : A.V → ℂ, (∀ z, cz z ≠ 0) ∧ ∀ α, ∀ th ∈ A.Theta k α, ∃ th' ∈ A.Theta k (α + la.y), (th ≠ 0 → th' ≠ 0) ∧ ∀ z, (∀ F, IsFShift A k α th la z F ↔ F = HahnSeries.single (A.be la.y α / k) (cz z) * A.FSum k (α + la.y) th' z) ∧ ∀ w : ℂ, A.Sum k α th w (z + (k : ℂ)⁻¹ • A.Pw w la) = cz z * eTwoPi (w * ((A.be la.y α / k : ℤ) : ℂ)) * A.Sum k (α + la.y) th' w z := by
  first | exact @GlobalTheory.ArcPts.theta_sum_shift | exact GlobalTheory.ArcPts.theta_sum_shift | (intros; apply GlobalTheory.ArcPts.theta_sum_shift <;> assumption)
