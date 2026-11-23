module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermMultiplicativeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingSplitOfStatement
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.MultiplicityOneBase.ArchimedeanBaseChangeFirst
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.ArchimedeanBaseChangeFourth
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Imports
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IsCompactMaximalPairPlace
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.GeneratorPowSplitPlacesOfIdempotent
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.LeviMatchingBlocks.StabilizerDilationWeightsDualIsotropicVector
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalOperatorSums.LocOp3
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchBPf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchBadIOf2
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchTorusOfTwistedMatching
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SplitPlacePowersOfLocalOps
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

@[expose] public section

namespace PositivityTheory.Rg.BcB.F.MatchAll

open PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcN.F2.LocOpPf

theorem ctMul : MT.CtMul := GlobalTheory.T.constant_term_multiplicative

theorem hM4 : M4 := archimedean_base_change_fourth

theorem hM1 : M1 := m1

theorem matchT_of (h4 : M4) : MT.MatchT := TorusMatching.match_torus_of_twisted_matching h4

theorem matchUnitI_of (h1 : M1) : MB.MatchUnitI := MB.matchUnitIOf h1

theorem matchSplit (h3 : M3) : MT.MatchSplit := GlobalTheory.T.matching_split_of h3 ctMul

theorem matchLMId : MLM.MatchLMId := MLM.matchLMIdOf idemAlg BlockFiniteConvolution.locOk₀

theorem matchLMWordS (h3 : M3) : MLM.MatchLMWordS := MLM.matchLMWordSOf (matchSplit h3) ctMul MLM.ctStar sphComm idemAlg

theorem matchLMUnit (h1 : M1) (h3 : M3) : MLM.MatchLMUnit := MLM.matchLMUnitOf (matchUnitI_of h1) (matchSplit h3) idemAlg

theorem matchLMB2 (h2 : M2) (h3 : M3) (h4 : M4) : MLM.MatchLMB2 :=
  MLM.matchLMB3Of_pf (matchT_of h4) (MS.match_split_place_of_powers h3 (MS.split_place_powers_of_local_ops locOp3)) (MB.matchBadSOf h3 MB.lponeIdem)
    (MB.matchBadIOf2 h2 MB.lponeIdem) MB.fixIdem idemAlg

end PositivityTheory.Rg.BcB.F.MatchAll
