module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PrimeProj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.CenExHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.NsmulIntegIff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PCongOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PDatEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PFrameEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PGoodOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PInIdUnit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PLevBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PNearNbhd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PPrimeProj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PProjLev
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PSiteTriv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PStabOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.SameKTrans
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.SpanLePow
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.SatCard
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.NhdsBasisLevelSubgroup
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace UpperTheory.Gal.Int.Geo.Pl

theorem tjOK_holds : TjOK := tjOK_of sides_holds dict_holds levBasic_holds

theorem tjIdx_holds : TjIdx := tjIdx_of sides_holds dict_holds levBasic_holds

theorem memEx_holds : MemEx := memEx_of sides_holds dict_holds levBasic_holds

theorem siteTriv_holds : SiteTriv := siteTriv_of sides_holds levBasic_holds

theorem siteEx_holds : SiteEx :=
  siteEx_of sides_holds dict_holds levBasic_holds (stabOf_of nearNbhd_holds primeProj_holds dict_holds)

theorem goodOf_holds : GoodOf :=
  goodOf_of levBasic_holds tjOK_holds (projLev_of dict_holds primeProj_holds levBasic_holds inIdUnit_holds)

theorem congOf_holds : CongOf := congOf_of levBasic_holds tjOK_holds tjIdx_holds

theorem exists_unitaryGroupDatum_of_vector_exponent_spectral (h1 : VecEx) (h2 : ExpOf) (h3 : SpecTop) : PlanEx :=
  planEx_of ⟨frameEx_holds, h1, h3, h2, sides_holds, levBasic_holds, memEx_holds, siteTriv_holds, siteEx_holds, goodOf_holds,
    congOf_holds, datEx_holds, CertificateRingHomMap.rootsAlg_holds, satCard, intCof_holds⟩

end UpperTheory.Gal.Int.Geo.Pl
