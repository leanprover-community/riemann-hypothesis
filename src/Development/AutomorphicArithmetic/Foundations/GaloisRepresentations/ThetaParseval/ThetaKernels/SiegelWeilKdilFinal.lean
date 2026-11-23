module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKdilSteps
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.AdDecompK
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocDerBig
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKdilAssembly
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKdilSplit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKdilTbBdd
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKdilTheta
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsplitSplitW
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitaryStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.Bridge
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.ProdGenMem
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
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Kdil
theorem decompW_k : _root_.PositivityTheory.SiegelWeilFormula.Kdil.DecompW_k := fun _ _ _ _ _ _ _ _ d R w g => _root_.PositivityTheory.SiegelWeilFormula.KSplitW.decompW_k d R w g
theorem gIdil_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hLE : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hAw : _root_.PositivityTheory.SiegelWeilFormula.AwayAct_k) (hS : GlobalTheory.Published.SiegelSetUnitary)
    (hLF : _root_.PositivityTheory.SiegelWeilFormula.Kdil.LocFamG_k) (hBD : BigDense) : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k :=
  _root_.PositivityTheory.SiegelWeilFormula.Kdil.gIdil_of_k hT hAux hLE (_root_.PositivityTheory.SiegelWeilFormula.Kdil.thetaPt_of_k hT) (fun _ _ P => KFock.isSw_fP P) matCount (_root_.PositivityTheory.SiegelWeilFormula.Kdil.splitDom_of_k hT hAw _root_.PositivityTheory.SiegelWeilFormula.Kdil.decompW_k)
    (_root_.PositivityTheory.SiegelWeilFormula.Kdil.thetaBdd_of_k hS) hLF hBD holMean derCont stripOK
theorem gIdil'_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hLE : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hAw : _root_.PositivityTheory.SiegelWeilFormula.AwayAct_k) (hLF : _root_.PositivityTheory.SiegelWeilFormula.Kdil.LocFamG_k) : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k :=
  _root_.PositivityTheory.SiegelWeilFormula.Kdil.gIdil_k hT hAux hLE hAw GlobalTheory.T.siegel_set_unitary hLF bigDense
end PositivityTheory.SiegelWeilFormula.Kdil
end
end
