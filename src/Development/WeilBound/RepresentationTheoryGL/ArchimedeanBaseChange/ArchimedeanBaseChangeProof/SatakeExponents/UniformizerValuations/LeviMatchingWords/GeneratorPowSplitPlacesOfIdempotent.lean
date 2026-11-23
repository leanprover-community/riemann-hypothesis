module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermStarStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchLeviWordsOfStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingIdentityOfStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingUnitOfStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityInertStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularPowerTorusStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparablePowerTorusStatement
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

namespace PositivityTheory.Rg.BcB.F.MLM

theorem matchLMIdOf : MatchLMIdOf := GlobalTheory.T.matching_identity_of
theorem matchLMUnitOf : MatchLMUnitOf := GlobalTheory.T.matching_unit_of

theorem muInert : MuInert := GlobalTheory.T.multiplicity_inert
theorem regPowT : RegPowT := GlobalTheory.T.regular_power_torus
theorem sepPowT : SepPowT := GlobalTheory.T.separable_power_torus
theorem ctStar : CtStar := GlobalTheory.T.constant_term_star
theorem matchLMWordSOf : MatchLMWordSOf := GlobalTheory.T.match_levi_words_of

end PositivityTheory.Rg.BcB.F.MLM
