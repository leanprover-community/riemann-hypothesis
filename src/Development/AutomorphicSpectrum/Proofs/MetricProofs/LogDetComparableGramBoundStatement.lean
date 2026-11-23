module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
public import Mathlib.LinearAlgebra.Matrix.Block
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetComparableGramBound
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.gram_log_unitary_triangular_invariance : ∀ (N : ℕ) (hd : Fin N → ℝ) (k : ℕ) (g u b : Matrix (Fin N) (Fin N) ℂ), (gramOf hd u = diagonal (fun i => ((hd i : ℝ) : ℂ)) → gramLog hd k (u * g) = gramLog hd k g) ∧ (b.BlockTriangular id → IsUnit b.det → (gramHead hd k g).det ≠ 0 → gramLog hd k (g * b) = gramLog hd k g + ∑ a : Fin N, if (a : ℕ) < k then Real.log ‖b a a‖ else 0) := by
  exact @GlobalTheory.CompanionTheory.Ar.PB.gramLog_inv
