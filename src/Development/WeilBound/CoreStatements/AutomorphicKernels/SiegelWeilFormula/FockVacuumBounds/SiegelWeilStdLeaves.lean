module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FarRightC
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicEisensteinSeries.MajorantW
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DenseW
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.RdEx
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.MeromorphicOnOfWeak
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.SecK
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.Strong
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.LiftExOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.FieldOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.MainEq
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.MainLe
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.VacAll
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.ContinuousChr
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.FourierZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.WeylElementTransposeMul
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.LamSingOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSchwartzSums.HolValueAtFinsum
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.SiegelMultOf
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

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

theorem Atop.siegelWeilStd_of (hA : AbsThm) (hT : TAll) (hTC : ThetaCoef) (hLo : LocOpEx) (hLI : LocInst)
    (hGS : GSplit) (hGI : GIinv) (hGD : GIdil) (hKP : KFinPoly) (hPK : PolyKFin) (hU : Unfold)
    (hW : WhitK) (hWE : WhitEq) (hG : AbsSt.GenCore) (hLD : LDEx) (hVK : VacK) (hSt : Step) :
    SiegelWeilStd := by
  have hBL : EisBL := PositivityTheory.RgEis.Hd.eisBL
  have hSK : SecK := Khead.secK
  have hAux : AuxiliaryPrimeFunction := kfour.auxEx
  have hRD : RDEx := Krd.rdEx
  have hFM : FockMem := KFock.fockMem
  have hLE : LiftEx := KFock.liftEx hT.1
  have hLB : LamBd := kfour.lamBd
  have hLS : LamSing := KSing.lamSing_of kfour.coefEx kfour.fourierZero Krd.denseW hAux
  have hEW : EisWk := Aeis.eisWk
  have hMain := KMain.mainOf hA hT hTC hRD hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hLB hLS hU hW
  have hLt := Khead.headOf hBL hSK (Khead.eisStrong_of hBL) hMain
  have hEq := Atop.mainEq_of hA hT hTC hRD hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hLB hLS hU hEW hWE
  have hVA := Atop.vacAllOfC hG hT hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hEW
  have hLe := Atop.mainLeOf hRD hLD hVK hPK hEq hSt hVA
  exact Atop.fieldOf hBL hSK hLt hLe

end PositivityTheory.SiegelWeilFormula

end
