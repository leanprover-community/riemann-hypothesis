module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsWeierstrassCoordinatesOnLine
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve
open scoped CategoryTheory.Obj UpperHalfPlane
theorem _root_.GlobalTheory.T.exists_weierstrass_coordinates_on_line : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R) (f : R →+* ℂ) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ scheme W) (v : epsR ℂ ⟶ A) (h : IsUnimodularSol (W.map ((algebraMap ℂ (DualNumber ℂ)).comp f)) ![DualNumber.eps, -1, 0]), IsPullback φ A.hom (toSpec W) (spMap f) → eSec A ≫ φ = spMap f ≫ zero W → v.left ≫ φ = ptHom W ((algebraMap ℂ (DualNumber ℂ)).comp f) ![DualNumber.eps, -1, 0] h → ∀ (L₁ : LB A.left) (g : ℕ) (u : HolUnif A L₁ g) (w : Fin g → ℂ), u.IsDiff w v → w ≠ 0 ∧ ∃ x y t : ℂ → ℂ, DifferentiableOn ℂ x {z | z • w ∈ u.Λ}ᶜ ∧ DifferentiableOn ℂ y {z | z • w ∈ u.Λ}ᶜ ∧ (∀ l : ℂ, l • w ∈ u.Λ → ∀ z, x (z + l) = x z ∧ y (z + l) = y z) ∧ (∀ z : ℂ, z • w ∉ u.Λ → (W.map f).toAffine.Equation (x z) (y z)) ∧ AnalyticAt ℂ t 0 ∧ t 0 = 0 ∧ deriv t 0 = 1 ∧ (∀ᶠ z in nhdsWithin 0 {0}ᶜ, t z * y z = -x z) ∧ Filter.Tendsto (fun z => ‖y z‖) (nhdsWithin 0 {0}ᶜ) Filter.atTop := by
  first | exact @GlobalTheory.UnifCoord.exists_coord_on_line | exact GlobalTheory.UnifCoord.exists_coord_on_line | (intros; apply GlobalTheory.UnifCoord.exists_coord_on_line <;> assumption)
