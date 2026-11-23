module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.SFunOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLogSizeM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFundamentalDomainRangeProdMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulLeSqAddSq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumMulSqLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumProdEqPow
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.OnlyIsotropic
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.AdmissibleLeHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ContinuousPA
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.CutCountOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelRowsColumnsSquareIntegrable
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.Mahler
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.MahlerFinal
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

namespace PositivityTheory.Rg.BcB.E1

open D1

theorem sizeCont : SizeCont := GlobalTheory.CompanionTheory.SizeCont.sizeCont szFin
theorem degRight : DegRight := GlobalTheory.CompanionTheory.DegRightProof.degRight_of mulF mulI szFin finSupp
theorem redBasic : RedBasic := redBasic_of ratProper_holds sizeCont
theorem cutBox : CutBox := cutBox_of' degBasis degAdelic degBdd
theorem redCell : RedCell := redCell_of sizeBasic degBdd degRat degRight torNorm_holds cutBox redBasic
theorem cutRed : CutRed := cutRed_of degRat cellCover_holds cutBox redBasic redCell
theorem cntPair : CntPair := cntPair_of ratProper_holds thetaBasic_holds
theorem wtCount : WtCount := wtCount_of ratProper_holds cellSum cellCover_holds redBasic redCell GlobalTheory.CompanionTheory.LatticeSum.latSum
theorem cutCount : CutCount := cutCount_of redBasic cutRed wtCount
theorem vecsEx : VecsEx := GlobalTheory.CompanionTheory.DualVectorFamily.vecsEx_of ratProper_holds kerBasic kerLin cntBasic cntPair vecEx vecNorm vecInner ptEq
theorem lBound : LBound := GlobalTheory.CompanionTheory.LBoundProof.lBound_of mahler_holds cutCount
theorem sFun_holds : SFun := sFun_of vecsEx lBound
theorem sBound_holds : F.SBound := sBound_of (sb_of sFun_holds)
theorem bridge_holds : F.Bridge := bridge_of (GlobalTheory.CompanionTheory.PairDom.prodDom ratProper_holds)
theorem opEx_holds : F.OpEx := opEx_of ratProper_holds opExA opAdj opMul
theorem kernel_operator_exists_holds : E.SmoothSeminormGrowth := kernel_operator_exists_of opEx_holds
theorem growthJ_of_ell (h : D4.EllFormula2J) : GrowthJ := growthJ_of h sBound_holds bridge_holds domEx_holds


end PositivityTheory.Rg.BcB.E1
