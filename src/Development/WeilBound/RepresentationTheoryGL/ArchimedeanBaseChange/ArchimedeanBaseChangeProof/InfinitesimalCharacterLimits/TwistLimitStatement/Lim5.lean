module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitBlockTypesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitNodeEmbeddingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitTwistBoundStatement
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TensorOperatorTrees.TreeLemmas
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TwistStripLimits.LimitOfFiniteDiscrete
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

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.LimG

theorem lim5 : PositivityTheory.Rg.BcB.SpectralAccumulation.FinDisc → PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5 := fun hFD =>
  PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5.limit_of_finite_discrete hFD GlobalTheory.T.limit_block_types GlobalTheory.T.limit_twist_bound GlobalTheory.T.limit_node_embedding
    PositivityTheory.Rg.BcB.SpectralAccumulation.Trees.treeLemmas.2.2.1 PositivityTheory.Rg.BcB.SpectralAccumulation.Trees.treeLemmas.2.1
    PositivityTheory.Rg.BcB.SpectralAccumulation.Trees.treeLemmas.1

end PositivityTheory.Rg.BcB.SpectralAccumulation.LimG
