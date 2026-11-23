module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.RigidPullbackIdentification
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.UniformizationBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullDegEquivApply

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifPullCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification (CarriesAt PullIdent)
open GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBaseChange (CarriesFam GrpPull RigPull UnifPull GenericInPsiLocus UnifBaseChange)
open GlobalTheory.PullDegCompare
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

section Bundle

end Bundle

section Main

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']

omit [IsDomain R] [IsDomain R'] in
theorem isGrpPullback_of_bc (bc : G' ≅ (Over.pullback (specOf φ)).obj G) (hbc : IsMonHom bc.hom) :
    IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
  ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl


variable [IsCommMonObj G] [IsCommMonObj G']

variable {I : Ideal R} {I' : Ideal R'}

variable {D : DegData R I} {D' : DegData R' I'} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {A' : PolAV (Spec (CommRingCat.of (FractionRing R')))}

end Main

end GlobalTheory.UnifPullCompare
