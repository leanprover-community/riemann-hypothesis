module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilFinCore
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayTop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKdilFull
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockFock
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinMul
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocinstInst
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopTop
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.HolLeadB
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



section
noncomputable section
open GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Fin
theorem locInst_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k := _root_.PositivityTheory.SiegelWeilFormula.KLI.locInst_of_k hT _root_.PositivityTheory.SiegelWeilFormula.kfour.auxiliaryExistence_holds _root_.PositivityTheory.SiegelWeilFormula.KFock.fockMem_k (_root_.PositivityTheory.SiegelWeilFormula.KFock.liftEx_k hT.1)
theorem siegelWeilStd_mid_k (hW : _root_.PositivityTheory.SiegelWeilFormula.TWeyl_k) (hKP : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k) (hLD : _root_.PositivityTheory.SiegelWeilFormula.LDEx_k) (hCT : _root_.PositivityTheory.SiegelWeilFormula.CTSplit_k) : _root_.GlobalTheory.ThK.Dbl.SiegelWeilStd_k :=
  have hT := _root_.PositivityTheory.SiegelWeilFormula.Fin.tAll_of_k hW
  _root_.PositivityTheory.SiegelWeilFormula.Fin.siegelWeilStd_of_k hT (_root_.PositivityTheory.SiegelWeilFormula.Fin.locInst_of_k hT)
    (_root_.PositivityTheory.SiegelWeilFormula.Kdil.gIdil_full_k hT _root_.PositivityTheory.SiegelWeilFormula.kfour.auxiliaryExistence_holds (_root_.PositivityTheory.SiegelWeilFormula.locOpEx_of_tAll_k hT) (_root_.PositivityTheory.SiegelWeilFormula.KAway.awayAct_of_tAll_k hT) (_root_.PositivityTheory.SiegelWeilFormula.Fin.locInst_of_k hT)) hKP
    (_root_.PositivityTheory.SiegelWeilFormula.KK.polyKFin_of_k hT _root_.PositivityTheory.SiegelWeilFormula.KFock.fockMem_k) hLD hCT HSt.holLeadB
end PositivityTheory.SiegelWeilFormula.Fin
end
end
