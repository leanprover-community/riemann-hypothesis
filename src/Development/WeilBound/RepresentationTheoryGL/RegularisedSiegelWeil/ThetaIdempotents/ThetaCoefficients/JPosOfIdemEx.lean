module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlternativeLocalComputationOfComponentsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactnessStatementStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundStatementStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionStatementStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositivityStatementStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionEigenfunctionMaximalCompactBis
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceRankCutOfAlternativeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundednessStatementStatement
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.JacquetPiatetskiBoundHolds
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionEigenfunctionMaximalCompact

@[expose] public section

open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

namespace GlobalTheory.CompanionTheory.Jp

theorem jPos_of_idemEx : IdemEx → JPos := by
  intro _ D n r t hrt hr ψ hψ χ hχ hres nb hnb S
  have hB2 : SplitPlaceRankCutEigenvalue := GlobalTheory.T.split_place_rank_cut_of_alternative (GlobalTheory.T.alternative_local_computation_of_components GlobalTheory.T.iwasawa_decomposition_statement GlobalTheory.T.height_bound_statement GlobalTheory.T.uniform_boundedness_statement GlobalTheory.T.compactness_statement GlobalTheory.T.positivity_statement)
  obtain ⟨v, hvS, hpsi, τ, hchi⟩ := GlobalTheory.T.jacquet_piatetski_bound_holds D r ψ hψ χ hχ hres S
  obtain ⟨C, c, hK, hd, hc, hint⟩ := hB2 D n r t hrt hr ψ hψ nb hnb v hpsi τ
  refine ⟨v, hvS, C, c, hK, hd, hc, ?_⟩
  intro νv hH hP z f _ hlaw hinv g
  exact GlobalTheory.T.section_eigenfunction_maximal_compact D n χ nb hnb v τ hchi C νv hH z (c z) (hint νv hH hP z) f hlaw hinv g

end GlobalTheory.CompanionTheory.Jp
