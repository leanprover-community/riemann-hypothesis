module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanZeroCompSmulPeriodicFundamentalDomain
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

open MeasureTheory

theorem _root_.GlobalTheory.T.mean_zero_comp_smul_periodic_fundamentalDomain : ∀ (n : Type) [Fintype n] (L : AddSubgroup (n → ℝ)) [Countable L] (D : Set (n → ℝ)) (k : (n → ℝ) → ℂ) (q : ℝ), 0 < q → MeasureTheory.IsAddFundamentalDomain L D MeasureTheory.volume → 0 < MeasureTheory.volume D → MeasureTheory.volume D < ⊤ → Continuous k → (∃ C : ℝ, ∀ s, ‖k s‖ ≤ C) → (∀ p ∈ L, ∀ s, k (s + p) = k s) → ∫ s in D, k s = 0 → ∀ (L₁ : AddSubgroup (n → ℝ)) [Countable L₁] (D₁ : Set (n → ℝ)), MeasureTheory.IsAddFundamentalDomain L₁ D₁ MeasureTheory.volume → MeasureTheory.volume D₁ < ⊤ → (∀ p ∈ L₁, ∀ s, k (q • (s + p)) = k (q • s)) → ∫ s in D₁, k (q • s) = 0 := by
  first | exact @GlobalTheory.mean_zero_comp_smul_of_periodic | exact GlobalTheory.mean_zero_comp_smul_of_periodic | (intros; apply GlobalTheory.mean_zero_comp_smul_of_periodic <;> assumption)
