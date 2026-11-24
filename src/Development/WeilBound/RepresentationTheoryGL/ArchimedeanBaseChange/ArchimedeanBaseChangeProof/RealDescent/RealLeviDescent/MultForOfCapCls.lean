module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.LeviCommutantWordReduction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutantReductionRealStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPickRealStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRelationsRealStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviStabilityRealStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarActionFifthRealStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemisimpleClassificationRealStatement
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.MultForOf
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PositivityTheory.RgBcC.RealD

theorem multFor_of_capCls (hCC : CapCls) : MultFor :=
  multFor_of GlobalTheory.T.invariant_pick_real GlobalTheory.T.levi_stability_real GlobalTheory.T.levi_relations_real GlobalTheory.T.semisimple_classification_real hCC GlobalTheory.T.commutant_reduction_real GlobalTheory.T.scalar_action_fifth_real

end PositivityTheory.RgBcC.RealD
