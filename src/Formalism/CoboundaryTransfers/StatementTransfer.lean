module

public import Formalism.CoboundaryTransfers.Statement
public import Formalism.LagrangeIdealLifts.Statement
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.CoboundaryTransfers

def UClaimU : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (B : Base ℤ_[ℓ] A) (M : ℕ)
    (u : ℤ_[ℓ]ˣ), B.p = ℓ → B.φ B.X = B.X * B.Q → B.GammaX (u : ℤ_[ℓ]) → B.GammaQ →
    ∀ (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
    (W : WachMod B M D) (s : ℕ) (J : Finset ℤ),
    1 ≤ s → (ℓ = 2 → 2 ≤ s) → PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s → 0 ∉ J →
    (∀ n ∈ W.N, ∃ z ∈ W.N, B.X ^ (M + 1) • n = B.X ^ (M + 1) • z - W.φ (B.X ^ (M + 1) • z)) →
    (∀ y, W.QInv y → B.X • y ∈ W.N → y ∈ W.N) →
    (∀ y, W.QInv y → Polynomial.aeval W.γ ((Polynomial.X - 1) *
      ∏ j ∈ J, (Polynomial.X - Polynomial.C (((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])))) y ∈ W.N) →
    (∀ y, W.QInv y → (ℓ : ℤ_[ℓ]) • y ∈ W.N → y ∈ W.N) →
    W.TorsKilled ((∏ j ∈ J, (1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))) *
      ∏ i ∈ Finset.Icc 1 M, ((u : ℤ_[ℓ]) ^ i - 1))

def LemmaUU : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] (B : Base ℤ_[ℓ] A) (M : ℕ)
    (u : ℤ_[ℓ]ˣ), B.p = ℓ → B.φ B.X = B.X * B.Q → B.GammaX (u : ℤ_[ℓ]) → B.GammaQ →
    ∀ (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[ℓ] D₀] [IsScalarTower ℤ_[ℓ] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    (W₀ : WachMod B M D₀) (W₁ : WachMod B M D₁) (W₂ : WachMod B M D₂) (S : SES W₀ W₁ W₂)
    (e s : ℕ) (J : Finset ℤ),
    1 ≤ s → (ℓ = 2 → 2 ≤ s) → PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s → 0 ∉ J →
    (∀ n ∈ W₀.N, ∃ z ∈ W₀.N, B.X ^ (M + 1) • n = B.X ^ (M + 1) • z - W₀.φ (B.X ^ (M + 1) • z)) →
    (∀ y, W₀.QInv y → B.X • y ∈ W₀.N → y ∈ W₀.N) →
    (∀ y, W₀.QInv y → Polynomial.aeval W₀.γ ((Polynomial.X - 1) *
      ∏ j ∈ J, (Polynomial.X - Polynomial.C (((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])))) y ∈ W₀.N) →
    (∀ y, W₀.QInv y → (ℓ : ℤ_[ℓ]) • y ∈ W₀.N → y ∈ W₀.N) →
    CokerKilled S e → RatSurj S → Lifts S ((ℓ : ℤ_[ℓ]) ^ (e + LIFT.eU ℓ M s J))

end Formalism.CoboundaryTransfers
