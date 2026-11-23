module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsQuotTriv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LGrpHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LIdxHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LPCount
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LPSigFin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LPSigPt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LPtsHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiesAbsOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PSigmaFEt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

namespace UpperTheory.Gal.FiniteEtaleModels

theorem liesAbs_holds : LiesAbs :=
  liesAbs_of (lPts_holds lGrp_holds) (lCount_holds lSigPt_holds lSigFin_holds) lIdx_holds sigmaFEt_holds

end UpperTheory.Gal.FiniteEtaleModels
