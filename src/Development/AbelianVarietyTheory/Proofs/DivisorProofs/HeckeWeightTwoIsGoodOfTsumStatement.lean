module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoIsGoodOfTsum
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

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo


theorem _root_.GlobalTheory.T.heckeWeightTwo_isGood_of_tsum : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (g : ι → ℂ → (Emb F → ℂ) → ℂ) (P : ℂ → (Emb F → ℂ) → ℂ),
  (∀ i, ∀ σ ∈ halfPlane, ContDiffOn ℝ ∞ (g i σ) (upperHalf F)) →
  (∀ i, ∀ w : List (Emb F × Bool), ∀ z ∈ upperHalf F, DifferentiableOn ℂ (fun σ => wirtWord w (g i σ) z) halfPlane) →
  (∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F → ∀ n : ℕ,
    ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ σ ∈ K, ∀ z ∈ L, ‖iteratedFDeriv ℝ n (g i σ) z‖ ≤ u i) →
  (∀ σ ∈ halfPlane, ∀ z ∈ upperHalf F, P σ z = ∑' i, g i σ z) →
  IsGood P := by
  first | exact @GlobalTheory.HeckeTwo.isGood_of_tsum | exact GlobalTheory.HeckeTwo.isGood_of_tsum | (intros; apply GlobalTheory.HeckeTwo.isGood_of_tsum <;> assumption)
