module

public import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
public import Mathlib.GroupTheory.Index
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

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Mv

def ModelMoves : Prop :=
  ∀ (k : Type) [Field k] (A B : Type) [AddCommGroup A] [AddCommGroup B] (c : B → A → k), IsBichar c →
    ∀ (A₁ A₂ : AddSubgroup A) (B₁ B₂ : AddSubgroup B),
      (∀ b, b ∈ B₁ ↔ ∀ a ∈ A₁, c b a = 1) →
      (∀ b ∈ B₂, ∀ a ∈ A₂, c b a = 1) →
      (∀ a ∈ A₁, (∀ b ∈ B₂, c b a = 1) → a ∈ A₂) →
      ∀ (SA : Finset A) (SB : Finset B), IsRepsG A₁ A₂ SA → IsRepsG B₁ B₂ SB →
        ∑ a ∈ SA, ∑ b ∈ SB, rhoA a (rhoB c b (ind (A₁ : Set A))) = (SB.card : k) • ind (A₂ : Set A)

def XiExists : Prop :=
  ∀ (k : Type) [Field k] (A B T : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup T] [Module k T]
    (c : B → A → k) (WA : A → T →ₗ[k] T) (WB : B → T →ₗ[k] T), IsBichar c → IsHeis c WA WB →
    ∀ (A₀ : AddSubgroup A) (θ : T), (∀ a ∈ A₀, WA a θ = θ) → (∀ b, (∀ a ∈ A₀, c b a = 1) → WB b θ = θ) →
      ∃! Xi : Sch c A₀ →ₗ[k] T, IsXi c WA WB A₀ θ Xi

def XiInter : Prop :=
  ∀ (k : Type) [Field k] (A B T : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup T] [Module k T]
    (c : B → A → k) (WA : A → T →ₗ[k] T) (WB : B → T →ₗ[k] T), IsBichar c → IsHeis c WA WB →
    ∀ (A₀ : AddSubgroup A) (θ : T) (Xi : Sch c A₀ →ₗ[k] T), IsXi c WA WB A₀ θ Xi →
      ∀ (Φ : A → k) (hΦ : Φ ∈ Sch c A₀),
        (∀ a, ∃ h : rhoA a Φ ∈ Sch c A₀, Xi ⟨rhoA a Φ, h⟩ = WA a (Xi ⟨Φ, hΦ⟩)) ∧
        ∀ b, ∃ h : rhoB c b Φ ∈ Sch c A₀, Xi ⟨rhoB c b Φ, h⟩ = WB b (Xi ⟨Φ, hΦ⟩)

def Moves : Prop :=
  ∀ (k : Type) [Field k] (A B T : Type) [AddCommGroup A] [AddCommGroup B] [AddCommGroup T] [Module k T]
    (c : B → A → k) (WA : A → T →ₗ[k] T) (WB : B → T →ₗ[k] T), IsBichar c → IsHeis c WA WB →
    ∀ (A₀ A₁ : AddSubgroup A) (B₀ B₁ : AddSubgroup B) (θ : T) (Xi : Sch c A₀ →ₗ[k] T), IsXi c WA WB A₀ θ Xi →
      (∀ b, b ∈ B₀ ↔ ∀ a ∈ A₀, c b a = 1) →
      (∀ b ∈ B₁, ∀ a ∈ A₁, c b a = 1) →
      (∀ a ∈ A₀, (∀ b ∈ B₁, c b a = 1) → a ∈ A₁) →
      ∀ (SA : Finset A) (SB : Finset B), IsRepsG A₀ A₁ SA → IsRepsG B₀ B₁ SB → (SB.card : k) ≠ 0 →
        ∃ h : ind (A₁ : Set A) ∈ Sch c A₀,
          ∑ a ∈ SA, ∑ b ∈ SB, WA a (WB b θ) = (SB.card : k) • Xi ⟨ind (A₁ : Set A), h⟩

def IndexDual : Prop :=
  ∀ (k : Type) [Field k] (A B : Type) [AddCommGroup A] [AddCommGroup B] (c : B → A → k), IsBichar c →
    ∀ (A₀ A₁ : AddSubgroup A) (B₀ B₁ : AddSubgroup B),
      (∀ b, b ∈ B₀ ↔ ∀ a ∈ A₀, c b a = 1) →
      (∀ b ∈ B₁, ∀ a ∈ A₁, c b a = 1) →
      (∀ a ∈ A₀, (∀ b ∈ B₁, c b a = 1) → a ∈ A₁) →
      A₁.relIndex A₀ ≠ 0 → B₀.relIndex B₁ = A₁.relIndex A₀

def ExtendLin : Prop :=
  ∀ (k : Type) [Field k] (M T : Type) [AddCommGroup M] [Module k M] [AddCommGroup T] [Module k T] (ι : Type)
    (f : ι → M) (g : ι → T),
    (∀ (s : Finset ι) (r : ι → k), ∑ i ∈ s, r i • f i = 0 → ∑ i ∈ s, r i • g i = 0) →
      ∃ Xi : M →ₗ[k] T, ∀ i, Xi (f i) = g i

end Formalism.L2.PairingIndexBounds.Mv

namespace Formalism.L2.PairingIndexBounds.Mv
end Formalism.L2.PairingIndexBounds.Mv
