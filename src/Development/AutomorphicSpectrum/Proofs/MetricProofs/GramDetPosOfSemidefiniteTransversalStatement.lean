module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.GramDetPosOfSemidefiniteTransversal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SymplecticUnipotentShape
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsChart
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi
import GroundTheory.HeightsAndTheta.Heights.Regularisation.StPuncturedExpOrder

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

theorem _root_.GlobalTheory.T.gram_det_pos_of_semidefinite_transversal : ∀ (g : ℕ) (Hb : Matrix (Fin g) (Fin g) ℂ) (U : Submodule ℂ (Fin g → ℂ)) (k : ℕ) (q : Fin k → Fin g → ℂ), Hb.IsHermitian → (∀ v : Fin g → ℂ, 0 ≤ (v ⬝ᵥ Hb *ᵥ star v).re ∧ ((v ⬝ᵥ Hb *ᵥ star v).re = 0 → v ∈ U)) → (∀ l : Fin k → ℂ, ∑ c, l c • q c ∈ U → l = 0) → 0 < (Matrix.of fun c c' => q c' ⬝ᵥ Hb *ᵥ star (q c)).det.re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.GramSemidef.gram_det_re_pos | exact GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.GramSemidef.gram_det_re_pos | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.GramSemidef.gram_det_re_pos <;> assumption)
