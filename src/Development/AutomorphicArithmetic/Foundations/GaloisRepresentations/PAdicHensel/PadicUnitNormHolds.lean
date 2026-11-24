module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PAdFour
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PBlockMat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PCongrScale
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PDefSign
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PFinCls
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PFinCongr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PHenselV
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PInfCongr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PIsoEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PLocFour
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PLocRoot
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PLocUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PNormTwo
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PPadMap
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PPadicSqFin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PPadicUnitNorm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PRelOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PScale
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PSplitCongr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PSplitRep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PTrivMat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PUnitCls
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PZSqFin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PZUnitNorm
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

namespace UpperTheory.Gal.G1

theorem LocFour_holds : LocFour := pLocFour
theorem HenselV_holds : HenselV := pHenselV
theorem SplitRep_holds : SplitRep := pSplitRep
theorem BlockMat_holds : BlockMat := pBlockMat
theorem PadMap_holds : PadMap := pPadMap
theorem Scale_holds : Scale := pScale
theorem PadicUnitNorm_holds : PadicUnitNorm := pPadicUnitNorm
theorem PadicSqFin_holds : PadicSqFin := pPadicSqFin
theorem TrivMat_holds : TrivMat := pTrivMat
theorem CongrScale_holds : CongrScale := pCongrScale
theorem SplitCongr_holds : SplitCongr := pSplitCongr
theorem InfCongr_holds : InfCongr := pInfCongr
theorem DefSign_holds : DefSign := pDefSign
theorem RelOf_holds : RelOf := pRelOf
theorem LocUnit_holds : LocUnit := pLocUnit HenselV_holds
theorem LocRoot_holds : LocRoot := pLocRoot HenselV_holds
theorem ZUnitNorm_holds : ZUnitNorm := pZUnitNorm PadicUnitNorm_holds
theorem ZSqFin_holds : ZSqFin := pZSqFin PadicSqFin_holds
theorem AdFour_holds : AdFour := pAdFour LocFour_holds LocUnit_holds LocRoot_holds SplitRep_holds
theorem UnitCls_holds : UnitCls := pUnitCls Scale_holds ZUnitNorm_holds ZSqFin_holds
theorem FinCongr_holds : FinCongr := pFinCongr PadMap_holds LocRoot_holds TrivMat_holds CongrScale_holds SplitCongr_holds DefSign_holds
theorem NormTwo_holds : NormTwo := pNormTwo AdFour_holds
theorem FinCls_holds : FinCls := pFinCls UnitCls_holds FinCongr_holds InfCongr_holds DefSign_holds RelOf_holds
theorem IsoEx_holds : IsoEx := pIsoEx NormTwo_holds BlockMat_holds

end UpperTheory.Gal.G1
