module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DatumExistsPeriod
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHolomorphicChart
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalPeriodLift
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPointOfIsPeriod
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFrameFamily
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationAtPointClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUnifOfParts
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteImageOfLocallyConstantOnHolomorphicFamilie
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsHolToModulipointExpOfHolomorphicPeriodsStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModNOfDvdModulus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PointEqIffIsometryClosed
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem familyUnif_of_thetaUnif : ThetaUnifAV → Out.Laws → N1c := fun hU hL =>
  GlobalTheory.familyUnif_of_parts GlobalTheory.datum_exists_period
    (GlobalTheory.PointUnif.exists_uniformisation_at_point_closed hU hL) (GlobalTheory.Moduli.exists_point_of_isPeriod hU hL) (GlobalTheory.UnifPoint.point_eq_iff_isometry_closed hU hL)
    (GlobalTheory.exists_local_period_lift hU hL) (GlobalTheory.T.isHolTo_modulipoint_exp_of_holomorphic_periods hU hL)
    (GlobalTheory.FiniteClasses.finite_image_of_locally_constant_on_holomorphic_families GlobalTheory.SubfieldChart.exists_holomorphic_chart)
    (GlobalTheory.exists_thetaFrame_family hU hL)
    (GlobalTheory.SimMult.exists_sim_trivial_of_mult GlobalTheory.SimAlg.sim_group GlobalTheory.exists_sim_lift)

end GlobalTheory
