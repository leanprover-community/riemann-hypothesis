module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.HodgeTrAt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.BcCover
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.CrysStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.GoodOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.GrCrys
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.HopExS
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.IntMap
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.MatInS
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.NegVan
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.NiceBc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.PieceInS
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.SubAdm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CorrUniqHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JLocTower
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.VFinHolds
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

namespace UpperTheory.Gal.Seam

theorem hopEx_holds : HopEx := hopExS trivial

theorem locTower_holds : LocTower := G3.locTower_of G3.vBcS_holds hopEx_holds niceBc

theorem pieceIn_holds : PieceIn := pieceInS G3.vInv_holds hopEx_holds

theorem matIn_holds : MatIn := matInS G3.vFin_holds pieceIn_holds negVan

theorem crysStep_of (h : CrystallineSemistableComparison.SmoothModelCrystalline) : UpperTheory.Gal.Int.Geo.CrysStep :=
  crysStep h niceBc locTower_holds bcCover intMap goodOf matIn_holds subAdm grCrys

end UpperTheory.Gal.Seam
