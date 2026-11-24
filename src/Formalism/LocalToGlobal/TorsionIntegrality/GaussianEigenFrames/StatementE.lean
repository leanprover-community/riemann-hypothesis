module

public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Mathlib.NumberTheory.NumberField.Basic
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

noncomputable section
open NumberField

namespace Formalism.L2.Th1.GD

open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def InertiaRam : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (E : Type) [Field E] [NumberField E] (s : E ≃+* E) (δ : E)
    (φ : E →+* ℂ_[p]), δ ^ 2 = -(p : E) → s δ = -δ → (∀ y, s (s y) = y) →
    (∀ y : E, s y = y → φ y ∈ MaximalUnramifiedExtension p) →
    ‖φ δ‖ = ‖(p : ℂ_[p])‖ ^ (1 / 2 : ℝ) ∧
    (∀ y : 𝓞 E, ‖φ (y : E) - φ (s (y : E))‖ ≤ ‖(p : ℂ_[p])‖ ^ (1 / 2 : ℝ)) ∧
    (∀ y : 𝓞 E, ‖φ (y : E)‖ < 1 → ‖φ (y : E)‖ ≤ ‖φ δ‖)

def EmbSep : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E]
    [Algebra K E] [IsGalois ℚ E] (φ ψ₁ ψ₂ : E →+* ℂ_[p]),
    (∃ π : 𝓞 K, ‖φ (algebraMap K E (π : K))‖ < 1 ∧
      ∀ y : 𝓞 E, ‖φ (y : E)‖ < 1 → ‖φ (y : E)‖ ≤ ‖φ (algebraMap K E (π : K))‖) →
    (∀ x : K, ψ₁ (algebraMap K E x) = ψ₂ (algebraMap K E x)) →
    (∀ y : 𝓞 E, ‖φ (y : E) - ψ₂ (y : E)‖ < 1) →
    ψ₁ ≠ ψ₂ →
    ∃ y : 𝓞 E, ‖φ (y : E) - ψ₁ (y : E)‖ = 1

def SepPairs : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (c s : E ≃+* E)
    (δ : E), δ ^ 2 = -(p : E) → c δ = -δ → s δ = -δ → (∀ y, c (c y) = y) → (∀ y, s (s y) = y) →
    (∀ y, s (c y) = c (s y)) →
    ∀ (H : Type) (emb : Bool × H → (E →+* ℂ_[p])), Function.Injective emb →
    (∀ τ ρ, emb τ δ = emb ρ δ) → (∀ t y, emb (true, t) y = emb (false, t) (s (c y))) →
    (∀ τ (y : E), s y = y → emb τ y ∈ MaximalUnramifiedExtension p) →
    ∀ τ ρ : Bool × H, ρ ≠ (!τ.1, τ.2) → ∃ e : 𝓞 E, ‖emb τ (e : E) - emb ρ (c (e : E))‖ = 1

end Formalism.L2.Th1.GD
