module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
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

set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u

section Statements

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
variable (Ω : Type*) [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]

def Ba.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type u) [AddCommGroup V] [Module Ω V]
    (E E' E'' : ChartBundle O (mseg x) N V),
    IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' → SameGeneric O x E' E'' →
    ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ),
      Q.IsHomogeneous (d + 1 - k) →
      ck O x d N E E'' k L Q = ck O x d N E E' k L Q + ck O x d N E' E'' k L Q ∧
        ck O x d N E' E k L Q = -ck O x d N E E' k L Q

def Bb.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (d N N₁ N₂ : ℕ) (V V₁ V₂ : Type u) [AddCommGroup V] [Module Ω V]
    [AddCommGroup V₁] [Module Ω V₁] [AddCommGroup V₂] [Module Ω V₂]
    (E E' : ChartBundle O (mseg x) N V) (i : V₁ →ₗ[Ω] V) (p : V →ₗ[Ω] V₂)
    (E₁ E₁' : ChartBundle O (mseg x) N₁ V₁) (E₂ E₂' : ChartBundle O (mseg x) N₂ V₂),
    IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' → IsSubQuot O x E i p E₁ E₂ →
    IsSubQuot O x E' i p E₁' E₂' →
    ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ),
      Q.IsHomogeneous (d + 1 - k) →
      ck O x d N E E' k L Q = ck O x d N₁ E₁ E₁' k L Q + ck O x d N₂ E₂ E₂' k L Q

def Bd.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type u) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V) (g : O), g ≠ 0 →
    IsModelOver O (mcIdeal O x) d →
    (∀ s, mseg x s ≠ 0 → ∀ v, v ∈ E'.lat s ↔ ∃ e ∈ E.lat s, v = algebraMap O Ω g • e) →
    ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ),
      Q.IsHomogeneous (d + 1 - k) →
      ck O x d N E E' k L Q = (k : ℤ) * rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q g ∧
        ∀ (m n : ℕ) (h w : O), IsUnit w → 1 ≤ m → g ^ m = w * h ^ n →
          (m : ℤ) * rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q g =
            (n : ℤ) * rootNum O x d N E (psum (Fin N) ℤ (k - 1)) L Q h

end Statements

section FieldStatements

variable (F : Type*) [Field F] (Ω : Type*) [Field Ω] [Algebra F Ω]
variable {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]

def SegreFlagIndep.Statement : Prop :=
  ∀ (x : (Σ k, ι k) → Ω) (e : ℕ), IsProjVarF (mcIdeal F x) e →
    ∀ (N : ℕ) (E : Type u) [AddCommGroup E] [Module Ω E] (B : ChartBundle F (mseg x) N E)
      (fl₁ fl₂ : FullFlag F x B) (I₀ : IFamily F ι), IsFieldIntersection I₀ →
    ∀ G : MvPolynomial (Fin N) ℤ, G.IsSymmetric → ∀ (c n : ℕ) (Y : Fin n → K → ℤ),
      G.IsHomogeneous c → c + n = e →
      polyNum I₀ (mcIdeal F x) e (Fin.append fl₁.deg Y)
          (rename (Fin.castAdd n) G * ∏ j : Fin n, X (Fin.natAdd N j)) =
        polyNum I₀ (mcIdeal F x) e (Fin.append fl₂.deg Y)
          (rename (Fin.castAdd n) G * ∏ j : Fin n, X (Fin.natAdd N j))

end FieldStatements

section Inhabitants

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem sameGeneric_symm {Ω : Type*} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {x : (Σ k, ι k) → Ω} {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]
    {E E' : ChartBundle O (mseg x) N V} (h : SameGeneric O x E E') : SameGeneric O x E' E :=
  fun s hs => ⟨(h s hs).2, (h s hs).1⟩

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
