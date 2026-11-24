module

public import Formalism.FrobeniusOrbits.HostDiffSupport
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

def NoRel (T : Finset ℕ) (L : ℕ) : Prop :=
  ∀ s₁ ∈ T, ∀ s₂ ∈ T, ∀ s₃ ∈ T, s₁ ≠ s₂ → s₁ ≠ s₃ → s₂ ≠ s₃ →
    ∀ i j : ℤ, 0 < |i| → |i| ≤ L → 0 < |j| → |j| ≤ L → i ≠ j →
      j * ((s₂ : ℤ) - s₁) ≠ i * ((s₃ : ℤ) - s₁)

def InTranslate {n : ℕ} (T : Finset ℕ) (u₀ x : ZMod n) : Prop := ∃ s ∈ T, x = (s : ZMod n) + u₀

instance decidableInTranslate {n : ℕ} (T : Finset ℕ) (u₀ x : ZMod n) :
    Decidable (InTranslate T u₀ x) := by
  unfold InTranslate
  exact Finset.decidableExistsAndFinset

open Classical in
def HostThickOrbit : Prop :=
  ∀ (n L : ℕ), 0 < n → 2 ≤ L → ∀ T : Finset ℕ, (∀ s ∈ T, 4 * L * s < n) → NoRel T L →
  ∀ u₀ t h : ZMod n,
    (4 * L < addOrderOf h → ∀ i₀ : ℤ,
      ((Finset.Ico i₀ (i₀ + L)).filter (fun i : ℤ => InTranslate T u₀ (t + i • h))).card ≤ 2) ∧
    (addOrderOf h ≤ 4 * L →
      {x : ZMod n | (∃ i : ℤ, x = t + i • h) ∧ InTranslate T u₀ x}.ncard ≤ 1)

def HostThickExists : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n L : ℕ, 2 ≤ L → ∃ T : Finset ℕ, (∀ s ∈ T, 4 * L * s < n) ∧ NoRel T L ∧
    (n : ℝ) * Real.exp (-C * Real.sqrt (Real.log n * Real.log L)) / L ≤ T.card

def bern {α : Type*} [Fintype α] (δ : ℝ) (T : Finset α) : ℝ :=
  δ ^ T.card * (1 - δ) ^ (Fintype.card α - T.card)


def HostStab : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ (k g : ℕ), g.Prime → 2 ^ (e + 2) * k < g - 1 →
  ∀ Γ : Subgroup (Matrix.GeneralLinearGroup (Fin k) (hostE ζ a b)),
    (∀ γ ∈ Γ, ∃ m : ℕ, orderOf γ = g ^ m) → Γ = ⊥

def HostOrdinary : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime]
    [P.LiesOver (span {(p : ℤ)})],
    (∀ σ τ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, τ ∈ MulAction.stabilizer _ P →
      (galE e ζ a b (σ * τ) ∈ Psi e ↔ galE e ζ a b σ ∈ Psi e)) ↔
    (primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard = 2

def HostUnimodular : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, galE e ζ a b σ = cc e →
  ∀ 𝔟 : Ideal (𝓞 (hostE ζ a b)),
    differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) = 𝔟 * (σ • 𝔟) →
    ∀ x : hostE ζ a b,
      x ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 (hostE ζ a b))) (hostE ζ a b))⁻¹) ↔
        ∀ y ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 (hostE ζ a b))) (hostE ζ a b))⁻¹),
          Algebra.trace (KinE ζ a b) (hostE ζ a b) (x * σ y) ∈
            (algebraMap (𝓞 (KinE ζ a b)) (KinE ζ a b)).range

def etaF {L : Type*} [Field L] [NumberField L] (ζ a b : L) (𝔭 : Ideal (𝓞 (hostF ζ a b))) : ℤ :=
  if (primesOver 𝔭 (𝓞 (hostE ζ a b))).ncard = 2 then 1 else -1

def HostEta : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
    (∀ 𝔭 : Ideal (𝓞 (hostF ζ a b)), 𝔭.IsPrime → 𝔭 ≠ ⊥ →
      (primesOver 𝔭 (𝓞 (hostE ζ a b))).ncard = 2 ∨
        ((primesOver 𝔭 (𝓞 (hostE ζ a b))).ncard = 1 ∧ 𝔭.inertiaDegIn (𝓞 (hostE ζ a b)) = 2)) ∧
    (∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ≠ q → p ≠ d →
      ∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
        (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b), IsArithFrobAt ℤ σ P →
        (etaF ζ a b (P.comap (algebraMap (𝓞 (hostF ζ a b)) (𝓞 (hostE ζ a b)))) = -1 ↔
          galE e ζ a b σ = cc e)) ∧
    (∀ (p : ℕ) [Fact p.Prime], (p = 2 ∨ p = q ∨ (p = d ∧ 2 ≤ e)) →
      ∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
        etaF ζ a b (P.comap (algebraMap (𝓞 (hostF ζ a b)) (𝓞 (hostE ζ a b)))) = 1)

end Formalism.FrobeniusOrbits
