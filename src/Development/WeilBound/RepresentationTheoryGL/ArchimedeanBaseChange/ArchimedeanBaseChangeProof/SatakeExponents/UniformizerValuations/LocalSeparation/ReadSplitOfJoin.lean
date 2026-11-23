module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChiDetPowSplitCentre
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFlipGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasInfCharGLRankZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HintZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisFurther
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfOfTwPart
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitAtOfValuation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatVMapMulChi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmVecTranslate
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.LeafSeparation.LeafModHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PPairSat
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PReadModOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PTreeModOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.PTreeSatOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.SaturationTransportPair
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace PositivityTheory.Rg.BcB.F.RS

theorem joinEx_holds : JoinEx := GlobalTheory.CompanionTheory.JoinDatum.joinEx

theorem joinInf_holds : JoinInf := GlobalTheory.CompanionTheory.JoinInfProof.joinInf

theorem joinSat_holds : JoinSat := GlobalTheory.CompanionTheory.JoinSatPf.joinSat

theorem treeInf_holds : TreeInf := GlobalTheory.CompanionTheory.TreeInfSum.treeInf

theorem weightJoin_holds : WeightJoin := GlobalTheory.CompanionTheory.WeightJoin.main

theorem muLoc_holds' : MuLoc := GlobalTheory.CompanionTheory.MuLocal.muLoc_holds

theorem treeMod_of (h : JoinMod) : TreeMod := treeModOf_holds leafMod_holds GlobalTheory.CompanionTheory.NodeSep.nodeMod h

theorem readMod_of (h : JoinMod) : ReadMod := readModOf_holds (treeMod_of h)

theorem readSplit_of_join (h : JoinMod) : ReadSplit :=
  readSplit_of (treeSatOf_holds (treeMod_of h)) pairSat_holds thetaSat2_holds GlobalTheory.CompanionTheory.CtS.ctSat muLoc_holds' joinSat_holds
    GlobalTheory.CompanionTheory.SatSplitAt.satSplit GlobalTheory.CompanionTheory.ConjSat.satConj

end PositivityTheory.Rg.BcB.F.RS
