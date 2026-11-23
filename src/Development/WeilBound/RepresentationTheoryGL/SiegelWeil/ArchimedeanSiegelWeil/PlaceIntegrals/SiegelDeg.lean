module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralCongruenceInvariantStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralEqCoefficientNonrepresentedStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypothesesPreservedByLinearPullbackStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SingularHermitianCongruentBlockNormalFormStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerCoefficientCongruencePullbackStatement
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.SiegelWeilRankCoefficientStatement
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

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg

theorem siegelDeg : PositivityTheory.GramSchwartzFunctions.BC.SiegelDeg := by
  intro D r V ψ θ μ lam ν φ hH β hβ
  obtain ⟨a, t, γ, ha, hγ, rfl⟩ := GlobalTheory.T.singular_hermitian_congruent_block_normal_form D r β hβ
  rw [GlobalTheory.T.frame_integral_congruence_invariant D V ν r φ γ a ha, ← GlobalTheory.T.whittaker_coefficient_congruence_pullback D r V ψ μ lam φ γ a ha hH.2.2.2.1 hH.2.2.2.2.1]
  have hH' := GlobalTheory.T.hypotheses_preserved_by_linear_pullback D r V ψ θ μ lam ν φ a ha hH
  by_cases hx : ∃ x : Matrix (Fin V.rank) (Fin r) D.host.E, x.rank = r ∧ gramQ V x = γ.1
  · exact GlobalTheory.T.siegel_weil_rank_coefficient D r V ψ θ μ lam ν (pull a φ) hH' t γ hγ hx
  · exact GlobalTheory.T.frame_integral_eq_coefficient_nonrepresented D r V ψ θ μ lam ν (pull a φ) hH' t γ hγ hx

end GlobalTheory.CompanionTheory.WeilSiegel.Deg
