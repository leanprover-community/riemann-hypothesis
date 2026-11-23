module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.FrameDer
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjMemNilSet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContDiffMulRight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnOfIteratedFDerivZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlagFieldHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorsCommute
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisMore
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsWaveTranslateSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivTwoClm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionCompact
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeHomotopyStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveConeStructureStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceMulConjTranspose
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.CxDataModel
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.LOfOfKChain
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.KerComm
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.KerNId
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.SecondCountableG
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.TrZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.UnitaryMemGLs
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

namespace PositivityTheory.RgBcC

theorem lef_top (hE : WaveEx) (hS : WaveSpeed) (hK : KerEx) (hM : MultAlg) (hC : LfSt.KChain) : Lef := by
  have hKer : VC.VCKer := VC.vcKer_of
    (VC.kerComm_of GlobalTheory.CompanionTheory.WaveInv.waveN GlobalTheory.CompanionTheory.WaveField.waveA)
    (VC.kerNId_of GlobalTheory.CompanionTheory.LgBound.lgCpt GlobalTheory.CompanionTheory.ParamInt.intSmooth)
    (VC.nAvg_of GlobalTheory.CompanionTheory.ParamInt.intSmooth GlobalTheory.CompanionTheory.LgBound.lgCpt GlobalTheory.CompanionTheory.NilUnimod.nilUni)
    VC.trZero GlobalTheory.CompanionTheory.LgBound.lgCpt
  have hV : VCSt := VC.vcOf_of GlobalTheory.CompanionTheory.ParamInt.intSmooth hKer hE hS hM GlobalTheory.CompanionTheory.GelC.gelComm
    GlobalTheory.CompanionTheory.GelFlagPf.gelFlag_holds GlobalTheory.CompanionTheory.FlagHerm.flagField_holds GlobalTheory.CompanionTheory.NilUnimod.nilUni
    GlobalTheory.CompanionTheory.KerZeroPf.main
  have hCh : Chain := LfSt.chainOf'_holds hE hS GlobalTheory.CompanionTheory.GelC.gelComm GlobalTheory.CompanionTheory.KerZeroPf.main
  have hL : LSt := LfSt.lOf_of_kChain hC hE hS hK hM hCh GlobalTheory.T.positive_cone_structure GlobalTheory.T.positive_cone_homotopy
    GlobalTheory.CompanionTheory.SuppBound.suppSt
  exact lef_of cxEx_model hV hL

end PositivityTheory.RgBcC
