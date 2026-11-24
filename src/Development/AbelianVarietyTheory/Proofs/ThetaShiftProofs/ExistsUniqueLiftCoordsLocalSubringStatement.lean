module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueLiftCoordsLocalSubring
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
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.existsUnique_lift_coords_localSubring : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsSeparated G.hom] (L : LB G.left) (U : S.Opens) (N n : ℕ) (b : Fin n → LB.Sec (Out.powOver G L U N)) (R K : Type) [CommRing R] [IsLocalRing R] [CommRing K] [IsLocalRing K] (f : R →+* K) (y : Sp R ⟶ S) (x : Sp K ⟶ (G.hom ⁻¹ᵁ U).toScheme) (cf : Fin n → R) (j : L.ι) (u : Kˣ), L.IsLB → IsAffineOpen U → AmpleSpan.EmbedsBy (G.hom ∣_ U) b → Function.Injective f → ⊤ ≤ y ⁻¹ᵁ U → x ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = spMap f ≫ y → ⊤ ≤ (x ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j → (∀ i, valR x ((Out.powOver G L U N).U (fun _ => j)) ((b i).f (fun _ => j)) = f (cf i) * u) → (∃ i, IsUnit (cf i)) → ∃! x' : Sp R ⟶ (G.hom ⁻¹ᵁ U).toScheme, x' ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom = y ∧ spMap f ≫ x' = x ∧ ∀ j', ⊤ ≤ (x' ≫ (G.hom ⁻¹ᵁ U).ι) ⁻¹ᵁ L.U j' → ∃ u' : Rˣ, ∀ i, valR x' ((Out.powOver G L U N).U (fun _ => j')) ((b i).f (fun _ => j')) = cf i * u' := by
  first | exact @GlobalTheory.LiftPoint.existsUnique_lift | exact GlobalTheory.LiftPoint.existsUnique_lift | (intros; apply GlobalTheory.LiftPoint.existsUnique_lift <;> assumption)
