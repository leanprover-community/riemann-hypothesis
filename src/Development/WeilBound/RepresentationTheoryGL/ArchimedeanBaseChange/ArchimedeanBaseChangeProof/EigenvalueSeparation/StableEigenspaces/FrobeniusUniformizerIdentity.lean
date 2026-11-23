module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterpolationLocalL2Bound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStableBdSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralCompactLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralTranslate
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulInvEqOfCentral
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSp
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.CentralEigenvalues.CenteigHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.CentralEigenvalues.IsStableEigenspaceCap
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.FiniteTypes.FintypeHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.SizeBounds.SizetHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.StableHulls.IsStableHull
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PositivityTheory.Rg.BcB.E.E3

theorem frobenius_uniformizer_identity (h : LocNonPosGlue) : PositivityTheory.Rg.BcB.E.E3 :=
  asm_holds fintype_holds (GlobalTheory.CompanionTheory.LocSlice.locSlGlue sizet_holds GlobalTheory.CompanionTheory.CentralMult.multC GlobalTheory.CompanionTheory.InterpLoc.interpolation_local_L2_bound)
    (h sizet_holds) centeig_holds (GlobalTheory.CompanionTheory.CentRe.centReGlue_holds sizet_holds GlobalTheory.CompanionTheory.CentralMult.multC) hullaut_holds
    GlobalTheory.CompanionTheory.HullExp.hullNonPos GlobalTheory.CompanionTheory.PairSpProof.pairSp

end PositivityTheory.Rg.BcB.E.E3
