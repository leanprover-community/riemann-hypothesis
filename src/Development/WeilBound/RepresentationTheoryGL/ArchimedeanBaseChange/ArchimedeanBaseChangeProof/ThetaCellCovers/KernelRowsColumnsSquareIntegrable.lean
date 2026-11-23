module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BumpEx
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellSumOfCntBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CntBasicOfKerBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoeFnSumAe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColOp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColSqOfKerBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompKey
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAtOfSqBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CvAdjEqAvg
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfLeSmall
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOfCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerEqIntegralConjMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableReflect
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerClose
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerLinOfKerBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerMulOfKerBasicOfCvTest
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowsColumnsSquareIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralEnormRpowTwoNeTop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralWeightedSqLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowIntOfKerBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchurOpOfSchurL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoUnif
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecCloseOfKerBasicColSq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecInnerOfKerBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecLimOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecNormOfVecClose
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

theorem kerBasic : KerBasic := GlobalTheory.CompanionTheory.KernelBasic.kerBasic
theorem kerLin : KerLin := GlobalTheory.CompanionTheory.KerLinear.kerLin_of_kerBasic kerBasic
theorem cntBasic : CntBasic := GlobalTheory.CompanionTheory.KernelCount.cntBasic_of_kerBasic kerBasic
theorem rowInt : RowInt := GlobalTheory.CompanionTheory.KernelRows.rowInt_of_kerBasic kerBasic
theorem colSq : ColSq := GlobalTheory.CompanionTheory.KernelColumn.colSq_of_kerBasic kerBasic
theorem kernel_rows_columns_square_integrable : KernelL2RowsColumns := GlobalTheory.CompanionTheory.KerSquare.kernel_rows_columns_square_integrable kerBasic cntBasic colSq
theorem schurL : SchurL := GlobalTheory.CompanionTheory.Schur.schurL
theorem schurInt : SchurInt := GlobalTheory.CompanionTheory.SchurKernel.schurInt_of_schurL schurL
theorem schurOp : SchurOp := GlobalTheory.CompanionTheory.Schur.schurOp_of_schurL schurL
theorem cvTest : CvTest := GlobalTheory.CompanionTheory.ConvTest.cvTest
theorem kerMul : KerMul := GlobalTheory.CompanionTheory.KernelComposition.kerMul_of_kerBasic_of_cvTest kerBasic cvTest
theorem opExA : OpExA := GlobalTheory.CompanionTheory.OpEx.opExA kerBasic rowInt schurOp
theorem opAdj : OpAdj := GlobalTheory.CompanionTheory.KerAdj.opAdj_of kerBasic rowInt schurInt opExA
theorem opMul : OpMul := GlobalTheory.CompanionTheory.KernelOperators.opMul kerBasic kerLin rowInt kernel_rows_columns_square_integrable schurInt cvTest kerMul
theorem colOp : ColOp := GlobalTheory.CompanionTheory.KernelColumns.colOp kerBasic cvTest kernel_rows_columns_square_integrable kerMul
theorem cellSum : CellSum := GlobalTheory.CompanionTheory.CellSumProof.cellSum_of_cntBasic cntBasic
theorem twoUnif : TwoUnif := GlobalTheory.CompanionTheory.TwoSidedUnif.twoUnif
theorem bumpEx : BumpEx := GlobalTheory.CompanionTheory.Bump.bumpEx
theorem approxU : ApproxU := GlobalTheory.CompanionTheory.ApproxUnit.approxU cvTest twoUnif
theorem kerClose : KerClose := GlobalTheory.CompanionTheory.KernelClose.kerClose
theorem vecClose : VecClose := GlobalTheory.CompanionTheory.KernelColumns.vecClose_of_kerBasic_colSq kerBasic colSq
theorem vecNorm : VecNorm := GlobalTheory.CompanionTheory.KernelColumns.vecNorm_of_vecClose vecClose
theorem vecEx : VecEx := GlobalTheory.CompanionTheory.KerVec.vecEx cntBasic kernel_rows_columns_square_integrable twoUnif vecClose
theorem vecInner : VecInner := GlobalTheory.CompanionTheory.E1.vecInner_of_kerBasic kerBasic
theorem vecLim : VecLim := GlobalTheory.CompanionTheory.KernelColumns.vecLim_of cntBasic cvTest colOp approxU vecClose
theorem ptEq : PtEq := GlobalTheory.CompanionTheory.KerPoint.ptEq_of kerBasic cvTest opAdj colOp bumpEx approxU kerClose vecLim

end PositivityTheory.Rg.BcB.E1
