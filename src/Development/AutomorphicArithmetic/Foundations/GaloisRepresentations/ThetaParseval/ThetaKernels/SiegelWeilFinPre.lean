module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTwSt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldTop
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilFinCore
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilFinMid
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockFock
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourW
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpMain
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopTop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTbijMain
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTunitHeis
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTunitMain
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTwuMain
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTwvThetaW
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTwvUpTo
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



section
noncomputable section
open GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Fin
theorem tWeyl_of_k (hP : _root_.PositivityTheory.SiegelWeilFormula.TW.Poisson_k) : _root_.PositivityTheory.SiegelWeilFormula.TWeyl_k :=
  _root_.PositivityTheory.SiegelWeilFormula.TW.tWeyl_of_k _root_.PositivityTheory.SiegelWeilFormula.TBij_k.tBij _root_.PositivityTheory.SiegelWeilFormula.Fin.tTheta_k (_root_.PositivityTheory.SiegelWeilFormula.TW.UpToPf.upTo_of_k _root_.PositivityTheory.SiegelWeilFormula.TW.Twu.uniq_k) hP _root_.PositivityTheory.SiegelWeilFormula.TW.ThetaWPf.thetaW_k
theorem siegelWeilStd_pre_k (hP : _root_.PositivityTheory.SiegelWeilFormula.TW.Poisson_k) (hCT : _root_.PositivityTheory.SiegelWeilFormula.CTSplit_k) : _root_.GlobalTheory.ThK.Dbl.SiegelWeilStd_k :=
  have hT := _root_.PositivityTheory.SiegelWeilFormula.Fin.tAll_of_k (_root_.PositivityTheory.SiegelWeilFormula.Fin.tWeyl_of_k hP)
  _root_.PositivityTheory.SiegelWeilFormula.Fin.siegelWeilStd_mid_k (_root_.PositivityTheory.SiegelWeilFormula.Fin.tWeyl_of_k hP)
    (_root_.PositivityTheory.SiegelWeilFormula.KFP.kFinPoly_of_k hT _root_.PositivityTheory.SiegelWeilFormula.Tunit.tUnit_k _root_.PositivityTheory.SiegelWeilFormula.Tunit.tHeis_k _root_.PositivityTheory.SiegelWeilFormula.kfour.auxiliaryExistence_holds _root_.PositivityTheory.SiegelWeilFormula.KFock.fockMem_k (_root_.PositivityTheory.SiegelWeilFormula.locOpEx_of_tAll_k hT) (_root_.PositivityTheory.SiegelWeilFormula.Fin.locInst_of_k hT))
    (_root_.PositivityTheory.SiegelWeilFormula.Ald.ldEx_of_k hT _root_.PositivityTheory.SiegelWeilFormula.kfour.auxiliaryExistence_holds) hCT
end PositivityTheory.SiegelWeilFormula.Fin
end
end
