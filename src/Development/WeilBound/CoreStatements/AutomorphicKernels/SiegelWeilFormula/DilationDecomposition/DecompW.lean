module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdDecomp
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocDerBig
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitaryStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.Assembly
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.Bridge
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.ContinuousMhUInv
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.SplitDomOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.ThetaPtOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.ProdGenMem
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitW
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

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Kdil

theorem decompW : DecompW := fun _ _ _ _ _ _ _ _ d R w g => KSplitW.decompW d R w g

theorem gIdil (hT : TAll) (hAux : AuxiliaryPrimeFunction) (hLE : LocOpEx) (hAw : AwayAct) (hS : GlobalTheory.Published.SiegelSetUnitary)
    (hLF : LocFamG) (hBD : BigDense) : GIdil :=
  gIdil_of hT hAux hLE (thetaPt_of hT) (fun _ _ P => KFock.isSw_fP P) matCount (splitDom_of hT hAw decompW)
    (thetaBdd_of hS) hLF hBD holMean derCont stripOK

theorem gIdil' (hT : TAll) (hAux : AuxiliaryPrimeFunction) (hLE : LocOpEx) (hAw : AwayAct) (hLF : LocFamG) : GIdil :=
  gIdil hT hAux hLE hAw GlobalTheory.T.siegel_set_unitary hLF bigDense

end PositivityTheory.SiegelWeilFormula.Kdil

end
