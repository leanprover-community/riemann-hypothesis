module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.CharLiftPrimeOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.NormCnt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.NormLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.MatchBCX
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NormVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.Ci
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.LiftAll
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.WeakStableAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CoreDesc
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CoreLift
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.DescStep
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.LiftAll
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.LiftStep
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStrong
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.ChsConsSome
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.ChsFacts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.FdegEq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.GamOneOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.GamSumOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.LpEvalZero
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.LpPowOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.NmEq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.RkLiftOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.RkSupp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.SplitSuppOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.TwValsOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.UpThruOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.ValsExtOfAlt
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

namespace UpperTheory.Gal.GamX

open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.T

theorem gamSum_holds : GamSum :=
  gamSumOf matchBCX normCnt normVal (lpPowOf lpInj) chsFacts fdegEq (twValsOf normVal)

theorem gamOne_holds : GamOne := gamOneOf chsFacts (valsExtOf polFacts) gamSum_holds

theorem splitSupp_holds : SplitSupp :=
  splitSuppOf nmEq suppFacts Sph.weakStable
    (splitStrong (descStep (coreDesc ci Sph.gm) (liftAll (liftStep (coreLift ci Sph.gm)))))

theorem gamMixed_holds : GamMixed :=
  gamMixed_of gamOne_holds splitSupp_holds chsTr rkSupp (rkLiftOf UpperTheory.V.Z.Gam.normLoc) (upThruOf chsFacts)

theorem charSupp_holds : CharSupp := charSupp_of gamMixed_holds nmEq suppFacts

theorem charLiftPrime_holds : CharLiftPrime := charLiftPrime_of charSupp_holds

end UpperTheory.Gal.GamX
