module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapTangentCoordinates
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
import Mathlib.Tactic.NormNum.Prime
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

theorem _root_.GlobalTheory.T.abelian_map_tangent_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (A : Type) [CommRing A] (i : Sp A ⟶ X) (N : ℕ) (v : Fin N → (epsAt i ⟶ t.G)) (R : Type) [CommRing R] (t' : SAB H (Sp R)) (θ : A →+* R) (m : SABMap t' t (spMap θ ≫ i)) (g : ℕ) (M : LieModel t'.G (𝟙 (Sp R)) (Fin g → R)), (∀ k, IsTanAt t.G i (v k)) → ∃ x : Fin N → Fin g → R, ∀ k, (M.pt (x k)).left ≫ m.φ = spMap (dualMap θ) ≫ (v k).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PeriodCoord.exists_coords | exact GlobalTheory.CompanionTheory.Ar.PeriodCoord.exists_coords | (intros; apply GlobalTheory.CompanionTheory.Ar.PeriodCoord.exists_coords <;> assumption)
