module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.RepresentationTheory.Basic
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

open Finset Polynomial
open scoped ComplexOrder

noncomputable section

namespace Formalism.CyclotomicNorms

def Exc (g d ℓ : ℕ) : Prop := ℓ.Prime ∧ g ^ d < ℓ ^ (4 * padicValNat ℓ (g ^ d - 1))

def BB (N g : ℕ) : Set ℕ := {g} ∪ {ℓ | ∃ d, 1 ≤ d ∧ d ≤ N ∧ Exc g d ℓ}

def BBCount : Prop :=
  ∀ g : ℕ, 2 ≤ g →
    (∀ d : ℕ, 1 ≤ d → Set.Finite {ℓ | Exc g d ℓ} ∧ Set.ncard {ℓ | Exc g d ℓ} ≤ 3) ∧
    ∀ N : ℕ, Set.Finite (BB N g) ∧ Set.ncard (BB N g) ≤ 3 * N + 1

def RootsOfUnityCount : Prop :=
  ∀ ℓ w d : ℕ, ℓ.Prime → 1 ≤ w → 1 ≤ d →
    (ℓ ≠ 2 → Nat.card {x : ZMod (ℓ ^ w) // x ^ d = 1} ≤ d * ℓ ^ padicValNat ℓ d) ∧
    Nat.card {x : ZMod (ℓ ^ w) // x ^ d = 1} ≤ 2 * d

def ChoiceCount : Prop :=
  ∀ (Y : ℝ) (N g₁ : ℕ), 2 ≤ Y → 1 ≤ N → Y ≤ g₁ → (g₁ : ℝ) ≤ 2 * Y →
    ∀ S : Finset ℕ, (∀ g ∈ S, Y ≤ g ∧ (g : ℝ) ≤ 2 * Y ∧ (BB N g ∩ BB N g₁).Nonempty) →
      (S.card : ℝ) ≤ (3 * N + 1) * (1 + 2 * N ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1))

def BlocksCycle : Prop :=
  ∀ (G Ω : Type) [Group G] [MulAction G Ω] [Fintype Ω] [DecidableEq Ω] (B : Finset (Finset Ω))
    (m p : ℕ) (g₀ : G),
    (∀ b ∈ B, b.card = m) → (∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → Disjoint b b') → (∀ x, ∃ b ∈ B, x ∈ b) →
    (∀ g : G, ∀ b ∈ B, b.image (fun x => g • x) ∈ B) →
    p.Prime → Fintype.card Ω < 2 * p →
    (MulAction.toPerm g₀ : Equiv.Perm Ω).IsCycle →
    (MulAction.toPerm g₀ : Equiv.Perm Ω).support.card = p →
    B.card = 1 ∨ B.card = Fintype.card Ω

def JordanTransitive : Prop :=
  ∀ (G Ω : Type) [Group G] [MulAction G Ω] [Fintype Ω] [DecidableEq Ω] (p : ℕ) (g₀ : G),
    MulAction.IsPretransitive G Ω → p.Prime → Fintype.card Ω < 2 * p →
    p + 3 ≤ Fintype.card Ω →
    (MulAction.toPerm g₀ : Equiv.Perm Ω).IsCycle →
    (MulAction.toPerm g₀ : Equiv.Perm Ω).support.card = p →
    alternatingGroup Ω ≤ (MulAction.toPermHom G Ω).range ∧ ¬ Group.IsSolvable G

def Restriction : Prop :=
  ∀ (G k V : Type) [Group G] [Field k] [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (N : ℕ) (H : Subgroup G) [H.Normal] (I : Subgroup G) (e : Module.Basis (Fin N) k V)
    (χ : Fin N → G → k) (φ : G) (π : Equiv.Perm (Fin N)) (p : ℕ),
    8 ≤ N → Finite (G ⧸ H) → Group.IsSolvable (G ⧸ H) → I ≤ H →
    (∀ W : Submodule k V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∀ i, ∀ y ∈ I, ρ y (e i) = χ i y • e i) →
    (∀ i j, i ≠ j → ∃ y ∈ I, χ i y ≠ χ j y) →
    (∀ y, y ∈ I ↔ φ * y * φ⁻¹ ∈ I) →
    (∀ i, ∀ y ∈ I, χ (π i) y = χ i (φ⁻¹ * y * φ)) →
    p.Prime → Fintype.card (Fin N) < 2 * p → p + 3 ≤ N → p ∈ π.cycleType →
    ∀ W : Submodule k V, (∀ h ∈ H, ∀ x ∈ W, ρ h x ∈ W) → W = ⊥ ∨ W = ⊤

def monicOf {K : Type} [Field K] {N : ℕ} (a : Fin N → K) : K[X] :=
  X ^ N + ∑ i : Fin N, C (a i) * X ^ (i : ℕ)


end Formalism.CyclotomicNorms
