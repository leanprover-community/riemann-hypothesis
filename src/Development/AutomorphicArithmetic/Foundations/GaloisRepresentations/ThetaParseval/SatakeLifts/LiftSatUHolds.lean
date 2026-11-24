module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.CompUnit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SrcApply
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.CompUnitPf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.ContraIrr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.ContraUnit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.IsUnitaryCharInv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.KeepsSB
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.LeftSmooth
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.LiftSatUPf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.ModelDict
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLift
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairSatPf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PullGoodPf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SatContra
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SatDet
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SatInvT
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SatProd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SatTwist
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SegInv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.Separates
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SrcGood
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace UpperTheory.Gal.TP.Loc

theorem liftIso_holds : LiftIso :=
  liftIso_of (pairOfLift leftSmooth keepsSB modelDict separates) srcGood contraIrr (contraUnit contraIrr)

theorem liftSat_holds : LiftSat :=
  liftSat_of liftIso_holds srcGood contraIrr (contraUnit contraIrr) (satContra (contraUnit contraIrr)) satTwist satInvT satDet
    satProd segInv

theorem pairSat_holds : PairSat :=
  pairSat liftSat_holds pullGood contraIrr (contraUnit contraIrr) (satContra (contraUnit contraIrr))

theorem liftSatU_holds : LiftSatU := liftSatU pairSat_holds compUnit

end UpperTheory.Gal.TP.Loc
