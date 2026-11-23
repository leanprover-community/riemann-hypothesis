module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockNormBoundsMulXPderiv
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.fock_norm_bounds_mul_X_pderiv : ∀ (σ : Type) [DecidableEq σ] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : MvPolynomial σ ℂ →ₗ[ℂ] H), IsFockIP ι → ∀ (i : σ) (d : ℕ) (P : MvPolynomial σ ℂ), P.totalDegree ≤ d → ‖ι (X i * P)‖ ^ 2 ≤ ((d : ℝ) + 1) * ‖ι P‖ ^ 2 ∧ ‖ι (pderiv i P)‖ ^ 2 ≤ (d : ℝ) * ‖ι P‖ ^ 2 := by
  first | exact @GlobalTheory.FockNormBound.fock_norm_bounds | exact GlobalTheory.FockNormBound.fock_norm_bounds | (intros; apply GlobalTheory.FockNormBound.fock_norm_bounds <;> assumption)
