module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Finset

noncomputable section

def RestInnerTsumBound.Statement : Prop :=
  ∀ (p : ℝ) (k : ℕ) (c : ℕ → ℝ) (M : ℝ), 2 ≤ p → 1 ≤ k → (∀ n, |c n| ≤ M) →
    Summable (fun n : ℕ => (p ^ ((n + 1) * k))⁻¹ * c n) ∧
      |∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ * c n| ≤ M * (2 * (p ^ k)⁻¹)

def RestKSumBound.Statement : Prop :=
  ∀ (p X : ℝ) (N : ℕ), 0 < p → 0 ≤ X → X ≤ 3 / 8 * p →
    ∑ k ∈ Finset.Icc 2 N, 2 * (p ^ k)⁻¹ * X ^ (k - 1) / (k.factorial : ℝ) ≤ 1.5 * X / p ^ 2

def RestPrimeBoundOfFactor.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock) (B₀ : ℝ), 1 ≤ f → 1 ≤ r → 1 ≤ a →
    4 * (f : ℝ) * ((r + a : ℕ) : ℝ) ^ 2 ≤ B₀ →
    ∀ Q : ℕ → Fin f → RootRing f (r + a),
      (∀ k : ℕ, 2 ≤ k → k ≤ r + a → ∀ τ τ' : Fin f,
        |restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) τ')| ≤
          ((f * (r * a) + 1 : ℕ) : ℚ) * |fibreDegree f r a c| * restX r a ^ (k - 1) /
            (k.factorial : ℚ)) →
    ∀ (s : ℕ → ℕ → Fin f → Fin f) (e : ℕ → ℕ → Fin f → ℕ → ℚ),
      (∀ p n τ k, e p n τ k = 1 ∨ e p n τ k = -1) →
    ∀ p : ℕ, p.Prime → B₀ < p →
      |restPrimeModel f r a c Q s e p| ≤
        1.5 * f * (restX r a : ℝ) * (Real.log p / (p : ℝ) ^ 2) *
          ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)|

def RestBoundOfPrimeBound.Statement : Prop :=
  ∀ (f r a : ℕ) (c : SmallBlock) (B₀ : ℝ), 1 ≤ f → 1 ≤ r → 1 ≤ a →
    4 * (f : ℝ) * ((r + a : ℕ) : ℝ) ^ 2 ≤ B₀ →
    ∀ (Q : ℕ → Fin f → RootRing f (r + a)) (s : ℕ → ℕ → Fin f → Fin f)
      (e : ℕ → ℕ → Fin f → ℕ → ℚ),
    (∀ p : ℕ, p.Prime → B₀ < p →
      |restPrimeModel f r a c Q s e p| ≤
        1.5 * f * (restX r a : ℝ) * (Real.log p / (p : ℝ) ^ 2) *
          ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)|) →
    ∀ P : Set ℕ,
      Summable (fun p : {p : ℕ // p ∈ P ∧ p.Prime ∧ B₀ < p} =>
        |restPrimeModel f r a c Q s e p|) ∧
      |∑' p : {p : ℕ // p ∈ P ∧ p.Prime ∧ B₀ < p}, restPrimeModel f r a c Q s e p| ≤
        1.6 * ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)|

end

end RestTerms

end GroundTheory.Heights₂.Heights
