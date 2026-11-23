module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DualNumberPointsGlue
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

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar


theorem _root_.GlobalTheory.T.dual_number_points_glue : ∀ (X : Scheme.{0}) (R : Type) [CommRing R] (J : Type) [Finite J] (f : J → R), Ideal.span (Set.range f) = ⊤ →
  (∀ a b : Sp R ⟶ X, (∀ i, spMap (algebraMap R (Localization.Away (f i))) ≫ a = spMap (algebraMap R (Localization.Away (f i))) ≫ b) → a = b) ∧
  (∀ a b : Sp (DualNumber R) ⟶ X,
    (∀ i, spMap (dualMap (algebraMap R (Localization.Away (f i)))) ≫ a = spMap (dualMap (algebraMap R (Localization.Away (f i)))) ≫ b) → a = b) ∧
  ∀ w : ∀ i, Sp (DualNumber (Localization.Away (f i))) ⟶ X,
    (∀ i j (a : Localization.Away (f i) →+* Localization.Away (f i * f j)) (b : Localization.Away (f j) →+* Localization.Away (f i * f j)),
      a.comp (algebraMap R _) = algebraMap R _ → b.comp (algebraMap R _) = algebraMap R _ →
      spMap (dualMap a) ≫ w i = spMap (dualMap b) ≫ w j) →
    ∃ v : Sp (DualNumber R) ⟶ X, ∀ i, spMap (dualMap (algebraMap R (Localization.Away (f i)))) ≫ v = w i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieFinGlue.dual_glue | exact GlobalTheory.CompanionTheory.Ar.LieFinGlue.dual_glue | (intros; apply GlobalTheory.CompanionTheory.Ar.LieFinGlue.dual_glue <;> assumption)
