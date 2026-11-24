module

public import Mathlib.Data.Rat.Defs
public import Mathlib.GroupTheory.DoubleCoset
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.IndefiniteRowSideFullHecke.StabiliserCardinality

def stab {G : Type} [Group G] (Γ K : Subgroup G) (y : G) : Subgroup G :=
  Γ ⊓ K.map (MulAut.conj y).toMonoidHom

theorem mem_stab {G : Type} [Group G] (Γ K : Subgroup G) (y γ : G) :
    γ ∈ stab Γ K y ↔ γ ∈ Γ ∧ y⁻¹ * γ * y ∈ K := by
  unfold stab
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  refine and_congr_right fun _ => ⟨?_, fun h => ⟨_, h, by simp [mul_assoc]⟩⟩
  rintro ⟨k, hk, rfl⟩
  simpa [mul_assoc] using hk

def DoubleCosetCount : Prop :=
  ∀ (G : Type) [Group G] (Γ U K : Subgroup G), U ≤ K →
    (U.subgroupOf K).FiniteIndex →
    ∀ [Fintype (DoubleCoset.Quotient (Γ : Set G) (K : Set G))],
    (∀ y : G, Finite (stab Γ K y)) →
    (∀ x : G, stab Γ U x = ⊥) →
    ∀ rep : DoubleCoset.Quotient (Γ : Set G) (K : Set G) → G,
      (∀ c, DoubleCoset.mk Γ K (rep c) = c) →
      Finite (DoubleCoset.Quotient (Γ : Set G) (U : Set G)) ∧
      (Nat.card (DoubleCoset.Quotient (Γ : Set G) (U : Set G)) : ℚ) =
        (U.relIndex K : ℚ) *
          ∑ c : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
            1 / (Nat.card (stab Γ K (rep c)) : ℚ)

end GlobalTheory.IndefiniteRowSideFullHecke.StabiliserCardinality
