module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

def LieChart {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] (x : Sp R ⟶ S) (f : R) : Prop :=
  ∃ (P : Type) (_ : AddCommGroup P) (_ : Module R P) (_ : Module (Localization.Away f) P)
    (_ : IsScalarTower R (Localization.Away f) P) (_ : Module.Finite (Localization.Away f) P)
    (_ : Module.Projective (Localization.Away f) P)
    (m : ∀ (C : Type) [CommRing C] [Algebra R C], IsUnit (algebraMap R C f) →
      LieModel G (spMap (algebraMap R C) ≫ x) (P →ₗ[R] C)),
    ∀ (C C' : Type) [CommRing C] [CommRing C'] [Algebra R C] [Algebra R C']
      (hC : IsUnit (algebraMap R C f)) (hC' : IsUnit (algebraMap R C' f)) (c : C →ₐ[R] C') (w : P →ₗ[R] C),
      ((m C' hC').pt (c.toLinearMap ∘ₗ w)).left = spMap (dualMap c.toRingHom) ≫ ((m C hC).pt w).left

end GlobalTheory.CompanionTheory.Ar
