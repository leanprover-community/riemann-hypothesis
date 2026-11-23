module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfHermEBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoissonSummationHermitianLatticeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinCoefficientsSummableStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralContinuousStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralLocallySummableBoundStatement
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

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermPoisson

theorem poissonHerm_main : PositivityTheory.GramSchwartzFunctions.BC.PoissonHerm := by
  intro D r V ψ θ μ lam ν φ hH hJ
  obtain ⟨hm, hψ, hθ, hμ, ⟨𝓖, hlam⟩, -, hφ, -⟩ := hH
  have hc := GlobalTheory.T.theta_integral_continuous D r V ψ θ μ φ hψ hθ hμ hφ
  have hu := GlobalTheory.T.theta_integral_locally_summable_bound D r V ψ θ μ φ hm hψ hθ hμ hφ
  have hW := GlobalTheory.T.siegel_eisenstein_coefficients_summable D r V ψ θ μ lam 𝓖 φ hm hψ hθ hμ hlam hφ
  obtain ⟨-, hP⟩ := GlobalTheory.T.poisson_summation_hermitian_lattice D r ψ hψ lam 𝓖 hlam _ hc hu
  have hgW : ∀ β : HermE D r, (fun t : ratHerm D r => ∫ b, Jt ψ V μ φ b *
      ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) ((hermEquiv (D := D) (r := r)) β) = W ψ V μ lam φ β :=
    fun β => (W_eq ψ V μ lam φ β).symm
  have hS : Summable (fun t : ratHerm D r => ∫ b, Jt ψ V μ φ b *
      ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam) := by
    refine (hermEquiv (D := D) (r := r)).summable_iff.1 ?_
    exact hW.congr fun β => (hgW β).symm
  have e := hP hS
  have hsumJ : ∑' b : HermE D r, J ψ V μ φ b = ∑' c : ratHerm D r, Jt ψ V μ φ c.1 :=
    (hermEquiv (D := D) (r := r)).tsum_eq (fun c => Jt ψ V μ φ c.1)
  have hsumW : ∑' β : HermE D r, W ψ V μ lam φ β = ∑' t : ratHerm D r, ∫ b, Jt ψ V μ φ b *
      ψ (-halfTr (Matrix.trace (HMul.hMul t.1.1 b.1 : Mx D r r))) ∂lam := by
    rw [← (hermEquiv (D := D) (r := r)).tsum_eq]
    exact tsum_congr fun β => (hgW β).symm
  rw [hsumJ, e, ← hsumW]
  exact hW.hasSum

end GlobalTheory.CompanionTheory.HermPoisson
