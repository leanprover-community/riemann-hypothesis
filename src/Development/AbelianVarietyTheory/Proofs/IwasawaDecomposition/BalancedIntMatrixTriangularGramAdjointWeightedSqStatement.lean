module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedIntMatrixTriangularGramAdjointWeightedSq
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal

@[expose] public section

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.balancedIntMatrix_triangularGram_adjoint_weighted_sq_trace : ∀ (n : ℕ) (A A' : Matrix (Fin n) (Fin n) ℤ) (d : Fin n → ℝ) (u v : Matrix (Fin n) (Fin n) ℝ), (∀ i, 0 < d i) → v * u = 1 → u * v = 1 → (A.map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u * A'.map (Int.cast : ℤ → ℝ) → (∀ p q, d p * (u * A.map (Int.cast : ℤ → ℝ) * v) p q = d q * (u * A'.map (Int.cast : ℤ → ℝ) * v) q p) ∧ (∑ p, ∑ q, d p / d q * (u * A.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 = (((A' * A).trace : ℤ) : ℝ)) ∧ ∑ p, ∑ q, d p / d q * (u * A'.map (Int.cast : ℤ → ℝ) * v) p q ^ 2 = (((A' * A).trace : ℤ) : ℝ) := by
  first | exact @GlobalTheory.RedTh.adjoint_weighted_sq_trace | exact GlobalTheory.RedTh.adjoint_weighted_sq_trace | (intros; apply GlobalTheory.RedTh.adjoint_weighted_sq_trace <;> assumption)
