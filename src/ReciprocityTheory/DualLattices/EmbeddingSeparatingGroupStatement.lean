module

public import ReciprocityTheory.DualLattices.EigenLengthFrobeniusStatement
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

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def EmbeddingSeparatingGroupStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    p ≠ 2 → HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H),
    ∃ (G : Type) (_ : CommGroup G) (_ : Fintype G) (β : G → O),
      (∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) ∧ H.ρ (β 1) = 1 ∧
      IsUnit (Fintype.card G : R) ∧
      (∀ i γ, U.εT i ≠ 0 → U.sg (U.φ i) (β γ) = U.sg i (β γ) ^ p) ∧
      (∀ i k, U.εT i ≠ 0 → U.εT k ≠ 0 → i ≠ k →
        ∃ γ, v (algebraMap R C (U.sg i (β γ) - U.sg k (β γ))) = 1) ∧
      (∀ i, U.εT i ≠ 0 → ∃ γ, v (algebraMap R C (U.sg i (β γ) - 1)) = 1)

def EigenElementaryDivisorStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (X : Fin U.m → NNReal),
    (∀ i, HasLen v R (xModE H.Ht (bt2 H U) U.εT U.εL U.cj i) (X i)) →
    ∃ (κ : Ix g → Fin U.m) (Λ : Matrix (Ix g) (Ix g) R) (ε : Ix g → R),
      IsUnit Λ.det ∧ (∀ j, Matrix.vecMul (Λ j) (U.εT (κ j)) = Λ j) ∧
      (∀ j, ∃ c, cp = ε j * c) ∧
      (∀ i, ∏ j ∈ Finset.univ.filter (fun j => κ j = i), v (algebraMap R C (ε j)) = X i) ∧
      (∀ i (n : ℕ), Nonempty (LinearMap.range (Matrix.mulVecLin (U.εT i)) ≃ₗ[R] (Fin n → R)) →
        (Finset.univ.filter fun j => κ j = i).card = n) ∧
      (∀ i, Submodule.span R (Set.range fun k => (fromRows H.Ht (bt2 H U) * U.εT i) k) =
        Submodule.span R ((fun j => ε j • Λ j) '' {j | κ j = i}))

def EigenRankStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ (H : HodgeTateDatum p g v R O σ cp) (U : UnramData p g v R O σ cp H),
    (∀ i, ∃ n : ℕ, Nonempty (LinearMap.range (Matrix.mulVecLin (U.εT i)) ≃ₗ[R] (Fin n → R)) ∧
      Nonempty (LinearMap.range (Matrix.mulVecLin (U.εT (U.φ i))) ≃ₗ[R] (Fin n → R))) ∧
    (∀ i, U.εT i = 0 → U.r i = 0)

end ReciprocityTheory.PGsh.Up
