module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitCutX
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitCell
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitCoreX
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitDictAsm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitHeight
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitIwaX
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitLinX
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitMeas
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitRelEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitVac
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThGramIncMK
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitPure

@[expose] public section



section
noncomputable section
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
theorem genDictX_of_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.GenDictX_k :=
  _root_.PositivityTheory.SiegelWeilFormula.KWhit.dictAsmX_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.cellFormula_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.relEx_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.heightDict_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.measDict_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.thetaDict_k
theorem whitK_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hR : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hK : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (hW : Gen.WhitGenLt)
    (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) : _root_.PositivityTheory.SiegelWeilFormula.WhitK_k :=
  _root_.PositivityTheory.SiegelWeilFormula.KWhit.whitK_of_X_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.iwaRedC_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.pureSpan_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.linRedC_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.coreX_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.genDictX_of_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.kFinK_k hT hA hR hF hK hS hU hW hTC hLB hPK
theorem whitEq_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hR : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hK : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (hEW : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k)
    (hW : Gen.WhitGenEq) (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) : _root_.PositivityTheory.SiegelWeilFormula.WhitEq_k :=
  _root_.PositivityTheory.SiegelWeilFormula.KWhit.whitEq_of_X_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.iwaRedC_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.pureSpan_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.linRedC_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.coreX_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.genDictX_of_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.kFinK_k hT hA hR hF hK hS hU hEW hW hTC hLB hPK
theorem whitLow_of_k (hVK : _root_.PositivityTheory.SiegelWeilFormula.VacK_k)
    (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (hEW : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k) (hW : Gen.WhitGenLow)
    (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) : _root_.PositivityTheory.SiegelWeilFormula.WhitLow_k :=
  _root_.PositivityTheory.SiegelWeilFormula.KWhit.whitLow_of_X_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.iwaRedC_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.vacSpan_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.linRedC_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.coreX_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.genDictX_of_k hVK hT hA hF hS hU hEW hW hTC hLB hPK
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
