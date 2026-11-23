module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConjBis
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LimWU4OfLimWU3
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.TLiftK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BaseChangeDescent.BcBackOffT
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.ClosedPhiHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CongruenceOddLevel.CongFinOddOfLvLac
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineDescent.ToCoreK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineInputs.CoreAllOfRowStarCore
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.InertCharpoly.GaloisLocalGlobalOfLocalGlobalCompatibility
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.MainFin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.GaloisCompatUnlinkedSupportOfSpherical
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.PAdicSplitting.LocalGlobalCompatAtIwahoriFixedOfUnlinked
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TraceLimits.LimFinOddOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.LadicWeightEmbeddingOverPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

namespace UpperTheory.Gal.Int

open GlobalTheory.CongL

def recT : UpperTheory.GalStar.RecNotion := fun h rc => UpperTheory.Zero.LLC.IsRecT h rc

theorem coreAll_of (seed : SeedFinOdd) (cong : CongFinOdd) (up : UpperTheory.TP.TLiftK) : GlobalTheory.RoadU.CoreAll :=
  UpperTheory.Gal.Int.Inp.coreAll_of_core
    (UpperTheory.Gal.Int.Core.toCoreK up UpperTheory.Gal.ClosedPhiFromClosedTrace.congPhi_holds UpperTheory.Gal.Desc.descOffT (UpperTheory.Gal.Lim.limFinOdd_of seed cong))

theorem rest (h : GlobalTheory.RoadU.CoreAll) : UpperTheory.GalStar.Row0 recT := by
  have hspherical := UpperTheory.Gal.ToralGalois.galoisCompat_unlinkedSupport_of_spherical h
  exact UpperTheory.Gal.Int.Row.galoisLocalGlobal_of_localGlobalCompatibility h hspherical
    (UpperTheory.Gal.ToralGalois.R2.localGlobalCompatAtIwahoriFixed_of_unlinked hspherical)

theorem galoisLocalGlobal_of_geometry_lift (geo : UpperTheory.Gal.Int.Geo.GeoOne) (up : UpperTheory.TP.TLiftK) : UpperTheory.GalStar.Row0 recT :=
  rest (coreAll_of (UpperTheory.Gal.Int.Div.seedFinOdd_of_geoOne geo) (UpperTheory.Gal.Int.Cong.congFinOdd_of_ex UpperTheory.Gal.Wt.wtLacEx_holds) up)

theorem galoisLocalGlobalStrong_of_geometry_lift (geo : UpperTheory.Gal.Int.Geo.GeoOne) (up : UpperTheory.TP.TLiftK) : UpperTheory.GalStar.Row0b recT :=
  UpperTheory.GalStar.Row0.row0b recT (galoisLocalGlobal_of_geometry_lift geo up)

end UpperTheory.Gal.Int
