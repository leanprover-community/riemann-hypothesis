module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep

namespace PositivityTheory.Rg.BcN.F2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]

def IsHk (K : Subgroup (GL ι F)) (e : GL ι F → ℂ) : Prop :=
  IsOpen (K : Set (GL ι F)) ∧ IsCompact (K : Set (GL ι F)) ∧ HasCompactSupport e ∧
    ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ g, e (k₁ * g * k₂) = e g

def hk {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V) (K : Subgroup (GL ι F))
    (e : GL ι F → ℂ) (v : V) : V :=
  ∑ᶠ q : GL ι F ⧸ K, e q.out • ρ q.out v

def hconv (K : Subgroup (GL ι F)) (e₁ e₂ : GL ι F → ℂ) (g : GL ι F) : ℂ :=
  ∑ᶠ q : GL ι F ⧸ K, e₁ q.out * e₂ (q.out⁻¹ * g)

def hstar (e : GL ι F → ℂ) (g : GL ι F) : ℂ := starRingEnd ℂ (e g⁻¹)

variable (F ι)

def HkAlg : Prop :=
  ∀ (K : Subgroup (GL ι F)) (e₁ e₂ : GL ι F → ℂ), IsHk K e₁ → IsHk K e₂ →
    IsHk K (hconv K e₁ e₂) ∧ IsHk K (hstar e₁) ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL ι F) V), ∀ v ∈ fixed ρ K,
      hk ρ K e₁ v ∈ fixed ρ K ∧ hk ρ K (hconv K e₁ e₂) v = hk ρ K e₁ (hk ρ K e₂ v) ∧
      ∀ B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ, (∀ g v w, B (ρ g v) (ρ g w) = B v w) → ∀ w ∈ fixed ρ K,
        B (hk ρ K e₁ v) w = B v (hk ρ K (hstar e₁) w)

def IsolateAt : Prop :=
  ∀ (K : Subgroup (GL ι F)), IsOpen (K : Set (GL ι F)) → IsCompact (K : Set (GL ι F)) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL ι F) V), IsSmooth π → π.IsIrreducible →
      (∃ v ∈ fixed π K, v ≠ 0) →
    ∀ (J : Type) [Fintype J] (W : J → Type) [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
      (τ : ∀ j, Representation ℂ (GL ι F) (W j)), (∀ j, IsSmooth (τ j)) → (∀ j, (τ j).IsIrreducible) →
      (∀ j, IsEmpty ((τ j).Equiv π)) →
      ∃ e : GL ι F → ℂ, IsHk K e ∧ ∃ v₀ ∈ fixed π K, ∃ l : V →ₗ[ℂ] ℂ, l v₀ = 1 ∧
        (∀ v ∈ fixed π K, hk π K e v = l v • v₀) ∧ ∀ j, ∀ w ∈ fixed (τ j) K, hk (τ j) K e w = 0

def ProdFinLen : Prop :=
  ∀ (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ ι)
    (X : α → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (σ : ∀ a, Representation ℂ (GL (m a) F) (X a)),
    (∀ a, IsSmooth (σ a)) → (∀ a, (σ a).IsIrreducible) → HasFiniteLength (multiProd e σ)

end PositivityTheory.Rg.BcN.F2
