module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DefiningCoordinates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIteratedComplexPartialDerivTermwise
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.hasSum_iteratedComplexPartialDeriv_termwise : ∀ (I : Type) [Fintype I] [DecidableEq I] (Ξ : Type) (u : List I) (r : ℝ) (f : Ξ → (I → ℂ) → ℂ) (g : (I → ℂ) → ℂ) (M : Ξ → ℝ), 0 < r → Summable M → (∀ ξ, DifferentiableOn ℂ (f ξ) (Metric.ball 0 r)) → (∀ ξ, ∀ z ∈ Metric.ball (0 : I → ℂ) r, ‖f ξ z‖ ≤ M ξ) → (∀ z ∈ Metric.ball (0 : I → ℂ) r, HasSum (fun ξ ↦ f ξ z) (g z)) → HasSum (fun ξ ↦ iterD u (f ξ) 0) (iterD u g 0) := by
  first | exact @GlobalTheory.HilbFam.hasSum_iterD_termwise | exact GlobalTheory.HilbFam.hasSum_iterD_termwise | (intros; apply GlobalTheory.HilbFam.hasSum_iterD_termwise <;> assumption)
