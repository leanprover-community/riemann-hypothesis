module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleExtensionGenericFibre
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem lb_extends_over_dvr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (H : Over (Sp R)) [Smooth H.hom] [QuasiCompact H.hom] [IsSeparated H.hom] [GeometricallyIntegral H.hom] (L : LB ((Over.pullback (jK R)).obj H).left), L.IsLB → ∃ L' : LB H.left, L'.IsLB ∧ LBIso L (L'.pull (pullback.fst H.hom (jK R))) := by
  intro R _ _ _ H _ _ _ _ L hL
  obtain ⟨M, hM, hML⟩ := GlobalTheory.LBExtDVR.exists_lineBundle_extension_genericFibre R (FractionRing R)
    H.left ((Over.pullback (jK R)).obj H).left H.hom (pullback.snd H.hom (jK R))
    (pullback.fst H.hom (jK R)) inferInstance inferInstance (IsPullback.of_hasPullback H.hom (jK R)) L hL
  exact ⟨M, hM, LBIso.symm hML⟩

end GlobalTheory.Mum
