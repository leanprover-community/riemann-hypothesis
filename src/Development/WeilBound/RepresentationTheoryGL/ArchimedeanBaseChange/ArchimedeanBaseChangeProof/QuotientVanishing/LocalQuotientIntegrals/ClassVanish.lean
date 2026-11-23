module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AevalTranspose
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCornerGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetOneAddOfSq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnormOfRealToRealLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwConjOfIsTest
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImgEqOfInvariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralNonnegNormaliserEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralProdSubgroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogSizeNonneg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableSdot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.T2SpaceAdelicGLCmField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.T2SpaceFiniteAdeleRingCmField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwConjCentMul
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.OnlyIsotropic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.ClassVanishOfSteps
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.IsCompactEntryBall
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.QuotVanishL
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

namespace PositivityTheory.Rg.BcB.CV

open PositivityTheory.Rg.BcB.D1 GlobalTheory.CompanionTheory

theorem classVanish : ClassVanish :=
  classVanish_of_steps QuotNorm.integral_normaliser_eq (QuotProduct.quotProd_of_normEq QuotNorm.integral_normaliser_eq) chainSum
    RatDisc.ratDisc locVanish LocP.main LocFlagPf.locFlag degBdd KerTwFin.kerFin mahler SplitInf.splitAt NonEll.nonEllFlag
    SplitTwo.splitAt2 PairParam.pairParam (TorusCh.torusChar degAdelic)
    (ChiGamGlobal.chiGam_of onlyIsotropic (PosYGlobal.posY_of degSubmod degPairing) chainSum)
    (QuotStageInt.quotStage_of QuotNorm.integral_normaliser_eq) sizeBasic

theorem unfold : Unfold := UnfoldCut.unfold_of_mahler mahler

end PositivityTheory.Rg.BcB.CV
