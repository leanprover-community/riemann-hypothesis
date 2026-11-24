module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMulNormalisedAbsPowHalfEqOne
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix ValuativeRel


theorem _root_.GlobalTheory.T.norm_mul_normalisedAbsPow_half_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (χ : kˣ →* ℂˣ), (∀ u : kˣ, valuation k (u : k) = 1 → ‖(χ u : ℂ)‖ = 1) →
    ∀ ϖ : kˣ, GlobalTheory.SplitFlip.IsUnif ϖ → ‖(χ ϖ : ℂ)‖ ^ 2 * (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d = 1 →
    ∀ x : kˣ, ‖(χ x : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2))‖ = 1 := by
  first | exact @GlobalTheory.CharNormHalf.norm_mul_apow_eq_one | exact GlobalTheory.CharNormHalf.norm_mul_apow_eq_one | (intros; apply GlobalTheory.CharNormHalf.norm_mul_apow_eq_one <;> assumption)
