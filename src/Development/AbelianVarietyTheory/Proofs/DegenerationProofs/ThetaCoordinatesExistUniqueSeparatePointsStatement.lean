module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.thetaCoordinates_exist_unique_separate_points : Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (s : Sp K ⟶ S) (m : ℕ), Odd m → (m : K) ≠ 0 → ∀ (Ix : Type) (x : Ix → (Over.mk s ⟶ P.A)), (∀ i, x i ^ m ^ 2 = 1) → (∀ z, ∃ v : Ix → K, IsCoordPt P m x z fun i => fnOf (v i)) ∧ (∀ z (v v' : Ix → K), (IsCoordPt P m x z fun i => fnOf (v i)) → ((IsCoordPt P m x z fun i => fnOf (v' i)) ↔ ∃ c : Kˣ, v' = (c : K) • v)) ∧ (∀ v : Ix → K, (IsThetaPt P m x fun i => fnOf (v i)) ↔ IsCoordPt P m x 1 fun i => fnOf (v i)) ∧ (3 ≤ m → (∀ y : Over.mk s ⟶ P.A, y ^ m ^ 2 = 1 → ∃ i, x i = y) → ∀ z z' (v : Ix → K), (IsCoordPt P m x z fun i => fnOf (v i)) → (IsCoordPt P m x z' fun i => fnOf (v i)) → z = z' ∧ v ≠ 0) := by
  first | exact @GlobalTheory.CoordSep.coord_exists_unique_separate | exact GlobalTheory.CoordSep.coord_exists_unique_separate | (intros; apply GlobalTheory.CoordSep.coord_exists_unique_separate <;> assumption)
