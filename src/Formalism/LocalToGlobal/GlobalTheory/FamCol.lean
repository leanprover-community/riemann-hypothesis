module

public import Formalism.LocalToGlobal.Columns.ReferenceActionRationalLevels
public import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
public import Formalism.LocalRingCardinality.Lemmas
public import Formalism.SizeWindowBrackets.Chain2aCoreNoAnalytic
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.PChain
public import Formalism.SizeWindowBrackets.ClaimGaFree
public import Formalism.SizeWindowBrackets.QuotientSlopeBoundsWith
public import Formalism.SizeWindowBrackets.FrameTraceRatioFinEquiv
public import Formalism.SizeWindowBrackets.SlopesHypothesisFinitePlaces
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.WeightedSlopeExcessDecomposition
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.LevelOfCongruence
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.JointDModelAppliesUnitLattice
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.ExistsNsmulMem
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.GaloisMapComplexConjugation
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.AdmissibleSchurLemma
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.OneLeThresholdMulPowers
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.StronglyIrreducible
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtGram
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PolygonSlopeSum
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
public import Formalism.SizeWindowBrackets.ErrorFormsWeakWindowsFalse
public import Formalism.LogVandermondeBounds.LogRatioUpperBound
public import Formalism.SizeWindowBrackets.SlopesFromSizeAndCount

@[expose] public section

open Module NumberField IsDedekindDomain Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.FamCol

open Formalism Formalism.BasicNotions Formalism.HN Formalism.LFunctionChainParameters Formalism.L2.Col Formalism.L2.DIV

attribute [instance] RowArg.indexWFirst RowArg.indexWSecond RowArg.indexWThird RowArg.indexWFourth RowArg.firstRealIndex RowArg.secondRealIndex RowArg.firstRationalIndex RowArg.secondRationalIndex

section Fam

variable {K : Type} [Field K] [NumberField K] [StarRing K] {I : Type}

end Fam

attribute [instance] Pt.i1 Pt.i2 Pt.i3 Pt.i4

section Family

open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end Family

section Rec

end Rec

section Conc

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}

end Conc

section Dat

end Dat

section ConcNum

open Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain2

variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

end ConcNum

end Formalism.L2.GlobalTheoryTheory.FamCol

end
