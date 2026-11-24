module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.DiracOfDiracZeroModule
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalMemUnitary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestTermLemmaReal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.N2TopReal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSqLeDominantRearrangement
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

namespace PositivityTheory.RgBcC.RealD

theorem countG_holds : CountG := GlobalTheory.CompanionTheory.RealCountG.countG

theorem dirac_inequality_k_types : DiracInequalityWithoutSplitComponent := GlobalTheory.CompanionTheory.DiracKType0.dirac_inequality_k_types

theorem adm_least_zero_holds : AdmLeast0 :=
  adm_least_zero_of_dirac GlobalTheory.CompanionTheory.MultOne.WeightSumTopTypes.n2T dirac_inequality_k_types GlobalTheory.CompanionTheory.SpinBound.lemmaHT

theorem adm_least_holds : AdmLeast := adm_least_of_zero_module adm_least_zero_holds

end PositivityTheory.RgBcC.RealD
