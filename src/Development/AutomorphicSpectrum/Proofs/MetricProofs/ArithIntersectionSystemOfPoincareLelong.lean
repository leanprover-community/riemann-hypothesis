module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeAndCoordinatesOfResolutionStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionExistsOfPoincareLelongStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatementStatement
import GroundTheory.HeightsAndTheta.Heights.Intersections.EqZeroOfEventuallyEval
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFIntZero
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFVert
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRatioAlgDep
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ArithSystem
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Contract
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ContractMixed
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ContractMixedField
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.GeoNum
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageArithClosed
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ProjContract
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

namespace GlobalTheory.CompanionTheory.Ar.Pub

open GroundTheory.Heights₂.Heights ReciprocityTheory.ChartRestriction.G.AI.I4

theorem contractMixed_closed : ContractMixedStatement :=
  have hIntZero : Inter.PFIntZero.Statement :=
    Inter.PFIntZero.proof (Inter.pointFormRank_holds.proof Inter.RatioAlgDep.proof)
  have hVert : Inter.PFVert.Statement :=
    Inter.PFVert.proof (by intros; exact geoNumStatement _)
      (by intros; exact Targets.ExistsUnique.full _ _) Targets.contractMixedField
  Targets.ContractMixed.of_found imageArith Targets.Contract.pulledBackForms_topDensity_vanish
    (Inter.ProjectivePointVertical.proof (by intros; exact geoNumStatement _)
      (by intros; exact Targets.ExistsUnique.full _ _)
      (by intros; exact Targets.ProjContract.full _ _ _ _ _))
    hIntZero hVert

theorem arithIntersectionSystem_of_poincareLelong_resK :
    GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement →
      ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement := fun hPL hRK =>
  Targets.ArithIntersectionSystem.of_found
    (GlobalTheory.T.intersection_exists_of_poincare_lelong hPL (GlobalTheory.T.resolution_exists_of_resolution_statement hRK))
    (GlobalTheory.T.degree_and_coordinates_of_resolution (GlobalTheory.T.resolution_exists_of_resolution_statement hRK)).2
    contractMixed_closed

end GlobalTheory.CompanionTheory.Ar.Pub
