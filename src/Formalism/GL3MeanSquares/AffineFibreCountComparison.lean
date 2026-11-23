module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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

namespace Formalism.HermitianLattices.RamifiedLatticeOperators

open Finset Matrix ComplexConjugate

def Fubini_orbits : Prop :=
  ∀ (Γ P Q V : Type) [Group Γ] [MulAction Γ P] [MulAction Γ Q] [AddCommGroup V] [Module ℚ V]
    (pr : P → Q) (fib : Q → Finset P) (Ψ : P → V) (RP : Finset P) (RQ : Finset Q),
    (∀ (γ : Γ) (p : P), pr (γ • p) = γ • pr p) → (∀ p y, p ∈ fib y ↔ pr p = y) →
    (∀ (γ : Γ) (p : P), Ψ (γ • p) = Ψ p) →
    (∀ y : Q, Finite (MulAction.stabilizer Γ y)) →
    (∀ p : P, ∃! r, r ∈ RP ∧ r ∈ MulAction.orbit Γ p) →
    (∀ y : Q, ∃! r, r ∈ RQ ∧ r ∈ MulAction.orbit Γ y) →
    ∑ p ∈ RP, ((Nat.card (MulAction.stabilizer Γ p) : ℚ))⁻¹ • Ψ p =
      ∑ y ∈ RQ, ((Nat.card (MulAction.stabilizer Γ y) : ℚ))⁻¹ • ∑ p ∈ fib y, Ψ p

def Count_orbits : Prop :=
  ∀ (Γ A B V : Type) [Group Γ] [MulAction Γ A] [MulAction Γ B] [AddCommGroup V] [Module ℚ V]
    (up : A → Finset B) (down : B → Finset A) (G : A → B → V) (RA : Finset A) (RB : Finset B),
    (∀ a b, b ∈ up a ↔ a ∈ down b) → (∀ (γ : Γ) a b, b ∈ up a → γ • b ∈ up (γ • a)) →
    (∀ (γ : Γ) a b, b ∈ up a → G (γ • a) (γ • b) = G a b) →
    (∀ a : A, Finite (MulAction.stabilizer Γ a)) → (∀ b : B, Finite (MulAction.stabilizer Γ b)) →
    (∀ a : A, ∃! r, r ∈ RA ∧ r ∈ MulAction.orbit Γ a) →
    (∀ b : B, ∃! r, r ∈ RB ∧ r ∈ MulAction.orbit Γ b) →
    ∑ a ∈ RA, ((Nat.card (MulAction.stabilizer Γ a) : ℚ))⁻¹ • ∑ b ∈ up a, G a b =
      ∑ b ∈ RB, ((Nat.card (MulAction.stabilizer Γ b) : ℚ))⁻¹ • ∑ a ∈ down b, G a b

def LemmaB'_length : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
    ∀ (ι : Type) [Fintype ι] (deg : ι → ℕ),
      Module.length R ((ι → R) ⧸
        (Submodule.pi Set.univ (fun i => Ideal.span {ϖ ^ deg i}) : Submodule R (ι → R))) =
        ((∑ i, deg i : ℕ) : ℕ∞)

end Formalism.HermitianLattices.RamifiedLatticeOperators
