module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeylTheta.TWeylOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DarbouxCharts.BorelTup
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DarbouxCharts.DarbouxAnti
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.LiftExOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.WeylElementTransposeMul
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.LdExOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocOpExOfTAll
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalWeilElements.ThetaW
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalWeilElements.TtSmul
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.KFinPolyOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilStandard.SiegelWeilStdMid
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilStandard.SiegelWeilStdOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.JjMulJj
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnipotentBorelTuples.BorelTupU
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Fin

theorem tWeyl_of (hP : TW.Poisson) : TWeyl :=
  TW.tWeyl_of TBij.tBij tTheta (TW.UpToPf.upTo_of TW.Twu.uniq) hP TW.ThetaWPf.thetaW

theorem siegelWeilStd_pre (hP : TW.Poisson) (hCT : CTSplit) : SiegelWeilStd :=
  have hT := tAll_of (tWeyl_of hP)
  siegelWeilStd_mid (tWeyl_of hP)
    (KFP.kFinPoly_of hT Tunit.tUnit Tunit.tHeis kfour.auxEx KFock.fockMem (locOpEx_of_tAll hT) (locInst_of hT))
    (Ald.ldEx_of hT kfour.auxEx) hCT

end PositivityTheory.SiegelWeilFormula.Fin

end
