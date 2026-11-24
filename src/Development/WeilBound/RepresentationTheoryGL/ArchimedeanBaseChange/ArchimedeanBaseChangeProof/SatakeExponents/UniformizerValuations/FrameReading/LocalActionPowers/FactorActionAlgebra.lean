module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairMaximalCompactOpenCompact
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexNeZeroOfOpen
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.FmTermZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.Pfmone
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.Pfmpow
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LocalActionPowers.Psmall
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

namespace PositivityTheory.Rg.BcB.F.FA

theorem position_action_algebra : ActAlg := GlobalTheory.CompanionTheory.FactorAction.actAlg

theorem finAct_of (h1 : IntHint) (h2 : Slots) (h3 : FinConv) : FinAct := GlobalTheory.CompanionTheory.FinActS.finActOf h1 h2 h3 position_action_algebra

theorem fmOne_of (h1 : IntHint) (h2 : Slots) (h3 : FinConv) : Tail.FmOne :=
  fmOneOf_holds (fmOff_holds h3 (finAct_of h1 h2 h3)) actIdem_holds

theorem fmPow_of (h1 : IntHint) (h2 : Slots) (h3 : FinConv) (h4 : FmAlg) : Tail.FmPow :=
  fmPowOf_holds h4 (fmAtP_holds h3 (finAct_of h1 h2 h3)) convMul_holds position_action_algebra actIdem_holds

end PositivityTheory.Rg.BcB.F.FA
