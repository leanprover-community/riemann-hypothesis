module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeGermNullstellensatz
public import Mathlib.FieldTheory.Separable
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def IsGermCombination {σ : Type} [Fintype σ] (w : σ → ℂ) {k : ℕ} (p : Fin k → (σ → ℂ) → ℂ)
    (f : (σ → ℂ) → ℂ) : Prop :=
  ∃ h : Fin k → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (h i) w) ∧ ∀ᶠ z in 𝓝 w, f z = ∑ i, h i z * p i z

noncomputable def monicOfCoeffs {N : ℕ} (c : Fin N → ℂ) : Polynomial ℂ :=
  Polynomial.X ^ N + ∑ j : Fin N, Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)

def IsPrimitivePresentation {σ : Type} [Fintype σ] (w : σ → ℂ) {k : ℕ} (p : Fin k → (σ → ℂ) → ℂ) {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ) {N : ℕ} (c : Fin N → (Fin d → ℂ) → ℂ)
    (δ : (Fin d → ℂ) → ℂ) : Prop :=
  (∀ j, AnalyticAt ℂ (c j) (A w)) ∧ AnalyticAt ℂ δ (A w) ∧
  IsGermCombination w p (fun z => ℓ z ^ N + ∑ j, c j (A z) * ℓ z ^ (j : ℕ)) ∧
  (∀ a : Fin N → (Fin d → ℂ) → ℂ, (∀ j, AnalyticAt ℂ (a j) (A w)) →
    IsGermCombination w p (fun z => ∑ j, a j (A z) * ℓ z ^ (j : ℕ)) →
    ∀ j, ∀ᶠ y in 𝓝 (A w), a j y = 0) ∧
  (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 → (monicOfCoeffs fun j => c j y).Separable) ∧
  (∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
    ∃ (M : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (a j) (A w)) ∧
      IsGermCombination w p (fun z => δ (A z) ^ M * g z - ∑ j, a j (A z) * ℓ z ^ (j : ℕ))) ∧
  (∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g w →
    ∃ (n : ℕ) (b : Fin n → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (b j) (A w)) ∧
      IsGermCombination w p (fun z => g z ^ n + ∑ j, b j (A z) * g z ^ (j : ℕ)) ∧
      ∀ T : ℂ, T ^ n + ∑ j, b j (A w) * T ^ (j : ℕ) = (T - g w) ^ n)

def PrimeGermPrimitivePresentation.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (p : Fin k → (σ → ℂ) → ℂ),
    (∀ i, AnalyticAt ℂ (p i) w) → (holGermIdeal w p).IsPrime →
    ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ)
      (c : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ),
      IsPrimitivePresentation w p A ℓ c δ ∧ ¬ IsGermCombination w p (fun z => δ (A z))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
